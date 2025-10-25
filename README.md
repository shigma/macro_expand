# macro_expand
 
[![Crates.io](https://img.shields.io/crates/v/macro_expand.svg)](https://crates.io/crates/macro_expand)
[![Documentation](https://docs.rs/macro_expand/badge.svg)](https://docs.rs/macro_expand)

A Rust library for expanding procedural macros in-place. It allows you to register custom procedural macros and apply them to Rust source code programmatically. This is particularly useful for testing procedural macros by comparing their output against expected snapshots.

## Installation
 
Add to your `Cargo.toml`:
 
```toml
[dependencies]
macro_expand = { version = "0.1" }
```

## Example

When developing procedural macros, it's recommended to implement your macro logic using `proc_macro2` instead of
directly using `proc_macro`. This approach enables testing without the limitations of the `proc_macro` API,
which cannot be used outside of a procedural macro context.

```rust
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

// The actual proc-macro entry point
#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(tokens: TokenStream) -> TokenStream {
    derive_my_trait_inner(tokens.into()).into()
}

// The testable implementation using proc_macro2
pub(crate) fn derive_my_trait_inner(tokens: TokenStream2) -> TokenStream2 {
    let input: syn::DeriveInput = syn::parse2(tokens).unwrap();
    let input_ident = &input.ident;
    quote! {
        impl MyTrait for #input_ident {
            fn my_method(&self) {
                println!("MyTrait method called on {}", stringify!(#input_ident));
            }
        }
    }
}

#[cfg(test)]
mod test {
    use macro_expand::Context;
    use quote::quote;
    use std::fs::read_to_string;
    use super::*;

    #[test]
    fn fixtures() {
        let mut ctx = Context::new();
        // Register the inner implementation using testable implementation
        ctx.register_proc_macro_derive("MyTrait".into(), derive_my_trait_inner, vec![]);
        let input = read_to_string("fixtures/input.rs").unwrap().parse().unwrap();
        let output = ctx.transform(input);
        let expected = read_to_string("fixtures/output.rs").unwrap().parse().unwrap();
        let formatted = prettyplease::unparse(&syn::parse(output).unwrap());
        assert_eq!(formatted, expected);
    }
}
```
