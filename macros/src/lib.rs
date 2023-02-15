//! Helper macros for `async_ffi::FfiFuture`.
use proc_macro::TokenStream as RawTokenStream;
use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use quote::{quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream, Result};
use syn::spanned::Spanned;
use syn::{
    parse_quote_spanned, Block, Error, FnArg, ForeignItemFn, ItemFn, Pat, PatIdent, Signature,
    Token,
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
/// Typical usage is to apply this macro before an `async fn`.
/// ```
/// # async fn do_work(_: i32) { }
/// use async_ffi_macros::async_ffi;
/// // Or if you have `macros` feature of `async_ffi` enabled.
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
/// # async fn do_work(_: i32) { }
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
/// use async_ffi_macros::async_ffi;
/// // use async_ffi::async_ffi;
///
/// extern "C" {
///     #[async_ffi]
///     async fn extern_fn(arg: i32) -> i32;
/// }
/// ```
/// It would become:
/// ```
/// extern "C" {
///     fn extern_fn(arg: i32) -> ::async_ffi::FfiFuture<i32>;
/// }
/// ```
///
/// ## `!Send` futures
/// Call the macro with arguments `?Send` to wrap the result into `LocalFfiFuture` instead of
/// `FfiFuture`.
///
/// ```
/// use async_ffi_macros::async_ffi;
/// // use async_ffi::async_ffi;
///
/// #[async_ffi(?Send)]
/// async fn func() { }
/// ```
/// It would become:
/// ```
/// fn func() -> ::async_ffi::LocalFfiFuture<()> {
///     ::async_ffi::LocalFfiFuture::new(async move {})
/// }
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
                expand(&mut item.sig, None, args, &mut errors);
                input = item.to_token_stream();
            }
            Err(err) => errors.push(err),
        }
    } else {
        match syn::parse2::<ItemFn>(input.clone()) {
            Ok(mut item) => {
                expand(&mut item.sig, Some(&mut item.block), args, &mut errors);
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

#[derive(Debug, Default, Clone, Copy)]
struct Args {
    pub local: bool,
}

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut this = Self::default();
        if input.peek(Token![?]) {
            input.parse::<Token![?]>()?;
            input.parse::<kw::Send>()?;
            this.local = true;
        }
        if !input.is_empty() {
            return Err(Error::new(
                Span::call_site(),
                "expecting #[async_ffi] or #[async_ffi(?Send)]",
            ));
        }
        Ok(this)
    }
}

fn expand(sig: &mut Signature, body: Option<&mut Block>, args: Args, errors: &mut Vec<Error>) {
    let async_span = match sig.asyncness.take() {
        Some(tok) => tok.span,
        None => {
            if body.is_some() {
                errors.push(Error::new(
                    sig.fn_token.span,
                    "#[async_ffi] expects an `async fn`",
                ));
            }
            Span::call_site()
        }
    };

    let ffi_future = if args.local {
        quote_spanned!(async_span=> ::async_ffi::LocalFfiFuture)
    } else {
        quote_spanned!(async_span=> ::async_ffi::FfiFuture)
    };

    match &mut sig.output {
        syn::ReturnType::Default => {
            sig.output = parse_quote_spanned!(async_span=> -> #ffi_future<()>);
        }
        syn::ReturnType::Type(_r_arrow, ret_ty) => {
            *ret_ty = parse_quote_spanned!(async_span=> #ffi_future<#ret_ty>);
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
    fn check(args: TokenStream, input: TokenStream, expect: Expect) {
        let got = async_ffi_inner(args, input).to_string();
        expect.assert_eq(&got);
    }

    #[test]
    fn no_args() {
        check(
            quote!(),
            quote! {
                async fn foo() { }
            },
            expect!["fn foo () -> :: async_ffi :: FfiFuture < () > { :: async_ffi :: FfiFuture :: new (async move { }) }"],
        );
    }

    #[test]
    fn has_args() {
        check(
            quote!(),
            quote! {
                async fn foo(x: i32) { x + 1 }
            },
            expect!["fn foo (x : i32) -> :: async_ffi :: FfiFuture < () > { :: async_ffi :: FfiFuture :: new (async move { let _ = & x ; x + 1 }) }"],
        );
        check(
            quote!(),
            quote! {
                async fn foo(&self, y: i32) -> i32 { self.x + y }
            },
            expect!["fn foo (& self , y : i32) -> :: async_ffi :: FfiFuture < i32 > { :: async_ffi :: FfiFuture :: new (async move { let _ = & self ; let _ = & y ; self . x + y }) }"],
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
                r##"fn foo () -> :: async_ffi :: FfiFuture < () > { :: async_ffi :: FfiFuture :: new (async move { }) } compile_error ! { "#[async_ffi] expects an `async fn`" }"##
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
            expect!["fn foo () -> :: async_ffi :: LocalFfiFuture < () > { :: async_ffi :: LocalFfiFuture :: new (async move { }) }"],
        );
    }

    #[test]
    fn extern_fn() {
        check(
            quote!(),
            quote! {
                async fn extern_fn(arg1: u32) -> u32;
            },
            expect!["fn extern_fn (arg1 : u32) -> :: async_ffi :: FfiFuture < u32 > ;"],
        );
    }
}
