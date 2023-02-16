//! Helper macros for `async_ffi::FfiFuture`.
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
                "invalid arguments to #[async_ffi]",
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
    let async_span = if let Some(tok) = sig.asyncness.take() {
        tok.span
    } else {
        if body.is_some() {
            errors.push(Error::new(
                sig.fn_token.span,
                "#[async_ffi] expects an `async fn`",
            ));
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
        errors.push(Error::new(
            va.span(),
            "#[async_ffi] only supports identifier and wildcard arguments",
        ));
    }

    let mut params = Vec::with_capacity(sig.inputs.len());
    for (param, i) in sig.inputs.iter_mut().zip(1..) {
        match param {
            FnArg::Receiver(receiver) => params.push(receiver.self_token.to_token_stream()),
            FnArg::Typed(pat_ty) => match &*pat_ty.pat {
                Pat::Ident(pat_ident) if pat_ident.subpat.is_none() => {
                    params.push(pat_ident.to_token_stream());
                }
                Pat::Wild(pat_wild) => {
                    let ident = Ident::new(&format!("__param{i}"), pat_wild.span());
                    params.push(ident.to_token_stream());
                    pat_ty.pat = Box::new(Pat::Ident(PatIdent {
                        attrs: Vec::new(),
                        by_ref: None,
                        mutability: None,
                        ident,
                        subpat: None,
                    }));
                }
                _ => {
                    errors.push(Error::new(
                        param.span(),
                        "#[async_ffi] only supports identifier and wildcard arguments",
                    ));
                }
            },
        }
    }

    if let Some(body) = body {
        let stmts = std::mem::take(&mut body.stmts);
        body.stmts = parse_quote_spanned! {async_span=>
            #ffi_future::new(async move {
                // Force capturing all arguments in the returned Future.
                // This is the behavior of `async fn`.
                #(let _ = &#params;)*

                #(#stmts)*
            })
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};
    use quote::quote;

    #[track_caller]
    #[allow(clippy::needless_pass_by_value)]
    fn check(args: TokenStream, input: TokenStream, expect: Expect) {
        let got = async_ffi_inner(args, input).to_string();
        expect.assert_eq(&got);
    }

    #[test]
    fn no_args() {
        check(
            quote!(),
            quote! {
                async fn foo() {}
            },
            expect!["# [allow (clippy :: needless_lifetimes)] # [must_use] fn foo () -> :: async_ffi :: BorrowingFfiFuture < 'static , () > { :: async_ffi :: BorrowingFfiFuture :: new (async move { }) }"],
        );
    }

    #[test]
    fn has_args() {
        check(
            quote!(),
            quote! {
                async fn foo(x: i32) { x + 1 }
            },
            expect!["# [allow (clippy :: needless_lifetimes)] # [must_use] fn foo (x : i32) -> :: async_ffi :: BorrowingFfiFuture < 'static , () > { :: async_ffi :: BorrowingFfiFuture :: new (async move { let _ = & x ; x + 1 }) }"],
        );
        check(
            quote!(),
            quote! {
                async fn foo(&self, y: i32) -> i32 { self.x + y }
            },
            expect!["# [allow (clippy :: needless_lifetimes)] # [must_use] fn foo (& self , y : i32) -> :: async_ffi :: BorrowingFfiFuture < 'static , i32 > { :: async_ffi :: BorrowingFfiFuture :: new (async move { let _ = & self ; let _ = & y ; self . x + y }) }"],
        );
    }

    #[test]
    fn not_async() {
        check(
            quote!(),
            quote! {
                fn foo() {}
            },
            expect![[
                r##"# [allow (clippy :: needless_lifetimes)] # [must_use] fn foo () -> :: async_ffi :: BorrowingFfiFuture < 'static , () > { :: async_ffi :: BorrowingFfiFuture :: new (async move { }) } compile_error ! { "#[async_ffi] expects an `async fn`" }"##
            ]],
        );
    }

    #[test]
    fn non_send() {
        check(
            quote!(?Send),
            quote! {
                async fn foo() {}
            },
            expect!["# [allow (clippy :: needless_lifetimes)] # [must_use] fn foo () -> :: async_ffi :: LocalBorrowingFfiFuture < 'static , () > { :: async_ffi :: LocalBorrowingFfiFuture :: new (async move { }) }"],
        );
    }

    #[test]
    fn extern_fn() {
        check(
            quote!(),
            quote! {
                async fn extern_fn(arg1: u32) -> u32;
            },
            expect!["# [allow (clippy :: needless_lifetimes)] # [must_use] fn extern_fn (arg1 : u32) -> :: async_ffi :: BorrowingFfiFuture < 'static , u32 > ;"],
        );
    }

    #[test]
    fn borrow_args() {
        check(
            quote!('fut),
            quote! {
                async fn f(x: &i32) {}
            },
            expect!["# [allow (clippy :: needless_lifetimes)] # [must_use] fn f < 'fut > (x : & i32) -> :: async_ffi :: BorrowingFfiFuture < 'fut , () > { :: async_ffi :: BorrowingFfiFuture :: new (async move { let _ = & x ; }) }"],
        );
    }
}
