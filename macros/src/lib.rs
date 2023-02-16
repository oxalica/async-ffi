//! Helper macros for `async_ffi::FfiFuture`.
use std::mem;

use proc_macro::TokenStream as RawTokenStream;
use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use quote::{quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream, Result};
use syn::spanned::Spanned;
use syn::{
    parse_quote_spanned, Attribute, Block, Error, FnArg, ForeignItemFn, GenericParam, ItemFn,
    Lifetime, LifetimeDef, Pat, PatIdent, Signature, Token,
};

/// A helper macro attribute to converts an `async fn` into a ordinary `fn` returning `FfiFuture`.
///
/// Note that this crate doesn't automatically pulls in `async_ffi` dependency. You must manually
/// add `async_ffi` dependency to your `Cargo.toml`. Or alternatively, using `macros` feature of
/// `async_ffi` which re-export the macro from this crate, instead of pulling in this crate
/// explicitly.
///
/// # Usages
///
/// The typical usage is to apply this macro to an `async fn`.
/// ```
/// # async fn do_work(_: i32) {}
/// use async_ffi_macros::async_ffi;
/// // Or if you have `macros` feature of `async_ffi` enabled,
/// // use async_ffi::async_ffi;
///
/// #[async_ffi]
/// #[no_mangle]
/// async fn func(x: i32) -> i32 {
///     do_work(x).await;
///     x + 42
/// }
/// ```
///
/// It would be converted into roughly:
/// ```
/// # async fn do_work(_: i32) {}
/// #[no_mangle]
/// extern "C" fn func(x: i32) -> ::async_ffi::FfiFuture<i32> {
///     ::async_ffi::FfiFuture::new(async move {
///         // NB. Arguments are always moved into the result Future, no matter if it's used.
///         // This is the same behavior as original `async fn`s.
///         let x = x;
///
///         do_work(x).await;
///         x + 42
///     })
/// }
/// ```
///
/// You can also apply `#[async_ffi]` to external functions.
/// ```
/// # use async_ffi_macros::async_ffi;
/// extern "C" {
///     #[async_ffi]
///     async fn extern_fn(arg: i32) -> i32;
///     // => fn extern_fn(arg: i32) -> ::async_ffi::FfiFuture<i32>;
/// }
/// ```
///
/// ## Non-`Send` futures
/// Call the macro with arguments `?Send` to wrap the result into `LocalFfiFuture` instead of
/// `FfiFuture`.
///
/// ```
/// # use async_ffi_macros::async_ffi;
/// #[async_ffi(?Send)]
/// async fn func() {}
/// // => fn func() -> ::async_ffi::LocalFfiFuture<()> { ... }
/// ```
///
/// ## References in parameters
/// When parameters of your `async fn` contain references, you need to capture their lifetimes in
/// the result `FfiFuture`. Currently, we don't expand lifetime elisions. You must explicitly give
/// the result lifetime a name in macro arguments and specify all bounds if necessary.
///
/// ```
/// # use async_ffi_macros::async_ffi;
/// #[async_ffi('fut)]
/// async fn borrow(x: &'fut i32, y: &'fut i32) -> i32 { *x + *y }
/// // => fn borrow<'fut>(x: &'fut i32) -> ::async_ffi::BorrowingFfiFuture<'fut, i32> { ... }
///
/// // In complex cases, explicit bounds are necessary.
/// #[async_ffi('fut)]
/// async fn complex<'a: 'fut, 'b: 'fut>(x: &'a mut i32, y: &'b mut i32) -> i32 { *x + *y }
/// // => fn complex<'a: 'fut, 'b: 'fut, 'fut>(x: &'a mut i32, y: &'b mut i32) -> BorrowingFfiFuture<'fut, i32> { ... }
///
/// // Non Send async fn can also work together.
/// #[async_ffi('fut, ?Send)]
/// async fn non_send(x: &'fut i32, y: &'fut i32) -> i32 { *x }
/// // => fn non_send<'fut>(x: &'fut i32) -> ::async_ffi::LocalBorrowingFfiFuture<'fut, i32> { ... }
/// ```
#[proc_macro_attribute]
pub fn async_ffi(args: RawTokenStream, input: RawTokenStream) -> RawTokenStream {
    async_ffi_inner(args.into(), input.into()).into()
}

fn async_ffi_inner(args: TokenStream, mut input: TokenStream) -> TokenStream {
    let mut errors = Vec::new();
    let args = syn::parse2::<Args>(args)
        .map_err(|err| errors.push(err))
        .unwrap_or_default();
    if matches!(input.clone().into_iter().last(), Some(TokenTree::Punct(p)) if p.as_char() == ';') {
        match syn::parse2::<ForeignItemFn>(input.clone()) {
            Ok(mut item) => {
                expand(&mut item.attrs, &mut item.sig, None, args, &mut errors);
                input = item.to_token_stream();
            }
            Err(err) => errors.push(err),
        }
    } else {
        match syn::parse2::<ItemFn>(input.clone()) {
            Ok(mut item) => {
                expand(
                    &mut item.attrs,
                    &mut item.sig,
                    Some(&mut item.block),
                    args,
                    &mut errors,
                );
                input = item.to_token_stream();
            }
            Err(err) => errors.push(err),
        }
    }
    for err in errors {
        input.extend(err.into_compile_error());
    }
    input
}

mod kw {
    syn::custom_keyword!(Send);
}

#[derive(Default)]
struct Args {
    pub lifetime: Option<Lifetime>,
    pub local: bool,
}

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut this = Self::default();
        if input.peek(Lifetime) {
            this.lifetime = Some(input.parse::<Lifetime>()?);
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }
        if input.peek(Token![?]) {
            input.parse::<Token![?]>()?;
            input.parse::<kw::Send>()?;
            this.local = true;
        }
        if !input.is_empty() {
            return Err(Error::new(
                Span::call_site(),
                "invalid arguments for #[async_ffi]",
            ));
        }
        Ok(this)
    }
}

fn expand(
    attrs: &mut Vec<Attribute>,
    sig: &mut Signature,
    body: Option<&mut Block>,
    args: Args,
    errors: &mut Vec<Error>,
) {
    let mut emit_err =
        |span: Span, msg: &str| errors.push(Error::new(span, format!("#[async_ffi] {}", msg)));

    let async_span = if let Some(tok) = sig.asyncness.take() {
        tok.span
    } else {
        if body.is_some() {
            emit_err(sig.fn_token.span, "expects an `async fn`");
        }
        Span::call_site()
    };

    attrs.push(parse_quote_spanned!(async_span=> #[allow(clippy::needless_lifetimes)]));
    attrs.push(parse_quote_spanned!(async_span=> #[must_use]));

    let lifetime = match args.lifetime {
        None => Lifetime::new("'static", Span::call_site()),
        Some(lifetime) => {
            // Add the lifetime into generic parameters, at the end of existing lifetimes.
            sig.generics.lt_token.get_or_insert(Token![<](async_span));
            sig.generics.gt_token.get_or_insert(Token![>](async_span));
            let lifetime_cnt = sig.generics.lifetimes_mut().count();
            sig.generics.params.insert(
                lifetime_cnt,
                GenericParam::Lifetime(LifetimeDef::new(lifetime.clone())),
            );

            lifetime
        }
    };

    let ffi_future = if args.local {
        quote_spanned!(async_span=> ::async_ffi::LocalBorrowingFfiFuture)
    } else {
        quote_spanned!(async_span=> ::async_ffi::BorrowingFfiFuture)
    };

    match &mut sig.output {
        syn::ReturnType::Default => {
            sig.output = parse_quote_spanned!(async_span=> -> #ffi_future<#lifetime, ()>);
        }
        syn::ReturnType::Type(_r_arrow, ret_ty) => {
            *ret_ty = parse_quote_spanned!(async_span=> #ffi_future<#lifetime, #ret_ty>);
        }
    }

    if let Some(va) = &sig.variadic {
        emit_err(va.span(), "does not support variadic parameters");
    }

    // Force capturing all arguments in the returned Future.
    // This is the behavior of `async fn`.
    let mut param_bindings = TokenStream::new();
    for (param, i) in sig.inputs.iter_mut().zip(1..) {
        let pat_ty = match param {
            FnArg::Receiver(receiver) => {
                emit_err(receiver.span(), "does not support `self` parameter");
                continue;
            }
            FnArg::Typed(pat_ty) => pat_ty,
        };
        let param_ident = match &*pat_ty.pat {
            Pat::Ident(pat_ident) => {
                if pat_ident.ident == "self" {
                    emit_err(pat_ident.span(), "does not support `self` parameter");
                    continue;
                }
                pat_ident.ident.clone()
            }
            _ => Ident::new(&format!("__param{}", i), pat_ty.span()),
        };
        let old_pat = mem::replace(
            &mut *pat_ty.pat,
            Pat::Ident(PatIdent {
                attrs: Vec::new(),
                by_ref: None,
                mutability: None,
                ident: param_ident.clone(),
                subpat: None,
            }),
        );
        let attributes = &pat_ty.attrs;
        param_bindings.extend(quote_spanned! {old_pat.span()=>
            #(#attributes)*
            #[allow(
                clippy::let_unit_value,
                clippy::no_effect_underscore_binding,
                clippy::shadow_same,
                clippy::used_underscore_binding,
            )]
            let #old_pat = #param_ident;
        });
    }

    if let Some(body) = body {
        let stmts = mem::take(&mut body.stmts);
        body.stmts = parse_quote_spanned! {async_span=>
            #ffi_future::new(async move {
                #param_bindings
                #(#stmts)*
            })
        };
    }
}

#[cfg(doctest)]
mod tests {
    /// ```compile_fail
    /// #[async_ffi_macros::async_ffi]
    /// pub fn not_async() {}
    /// ```
    fn not_async() {}

    /// ```compile_fail
    /// pub trait Trait {
    ///     #[async_ffi_macros::async_ffi]
    ///     async fn method(&self);
    /// }
    /// ```
    fn receiver_trait_method() {}

    /// ```compile_fail
    /// struct Struct;
    /// impl Struct {
    ///     #[async_ffi_macros::async_ffi]
    ///     async fn method(&self) {}
    /// }
    /// ```
    fn receiver_impl_method() {}

    /// ```compile_fail
    /// struct Struct;
    /// impl Struct {
    ///     #[async_ffi_macros::async_ffi]
    ///     async fn method(self: &mut Self) {}
    /// }
    /// ```
    fn typed_receiver() {}
}
