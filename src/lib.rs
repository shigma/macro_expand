#![allow(clippy::test_attr_in_doctest)]

//! # macro_expand
//!
//! A Rust library for expanding procedural macros in-place. It allows you to register custom procedural macros and
//! apply them to Rust source code programmatically. This is particularly useful for testing procedural macros by
//! comparing their output against expected snapshots.
//!
//! ## Example
//!
//! When developing procedural macros, it's recommended to implement your macro logic using [`proc_macro2`] instead of
//! directly using [`proc_macro`]. This approach enables testing without the limitations of the [`proc_macro`] API,
//! which cannot be used outside of a procedural macro context.
//!
//! ```
//! # extern crate proc_macro;
//! use proc_macro::TokenStream;
//! use proc_macro2::TokenStream as TokenStream2;
//! use quote::quote;
//!
//! // The actual proc-macro entry point
//! # const IGNORE1: &str = stringify! {
//! #[proc_macro_derive(MyTrait)]
//! # };
//! pub fn derive_my_trait(tokens: TokenStream) -> TokenStream {
//!     derive_my_trait_inner(tokens.into()).into()
//! }
//!
//! // The testable implementation using proc_macro2
//! pub(crate) fn derive_my_trait_inner(tokens: TokenStream2) -> TokenStream2 {
//!     let input: syn::DeriveInput = syn::parse2(tokens).unwrap();
//!     let input_ident = &input.ident;
//!     quote! {
//!         impl MyTrait for #input_ident {
//!             fn my_method(&self) {
//!                 println!("MyTrait method called on {}", stringify!(#input_ident));
//!             }
//!         }
//!     }
//! }
//!
//! #[cfg(test)]
//! mod test {
//!     use macro_expand::Context;
//!     use quote::quote;
//!     use std::fs::read_to_string;
//!     use super::*;
//!
//!     #[test]
//!     fn fixtures() {
//!         let mut ctx = Context::new();
//!         // Register the inner implementation using testable implementation
//!         ctx.proc_macro_derive("MyTrait".into(), derive_my_trait_inner, vec![]);
//!         let input = read_to_string("fixtures/input.rs").unwrap().parse().unwrap();
//!         let output = ctx.transform(input);
//!         let expected = read_to_string("fixtures/output.rs").unwrap().parse().unwrap();
//!         let formatted = prettyplease::unparse(&syn::parse(output).unwrap());
//!         assert_eq!(formatted, expected);
//!     }
//! }
//! ```

#[cfg(doc)]
extern crate proc_macro;

use std::collections::{HashMap, HashSet};
use std::mem::take;

use itertools::{Either, Itertools};
use proc_macro2::TokenStream;
use quote::{ToTokens, quote};
use syn::parse::{Parse, ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::visit_mut::VisitMut;

#[expect(clippy::enum_variant_names)]
enum Item<'i> {
    ProcMacro(Box<dyn Fn(TokenStream) -> TokenStream + 'i>),
    ProcMacroAttribute(Box<dyn Fn(TokenStream, TokenStream) -> TokenStream + 'i>),
    ProcMacroDerive(Box<dyn Fn(TokenStream) -> TokenStream + 'i>, Vec<String>),
}

/// A context for registering and expanding procedural macros.
///
/// The `Context` holds a registry of macro implementations and provides methods to transform Rust source code by
/// expanding these macros.
#[derive(Default)]
pub struct Context<'i> {
    registry: HashMap<String, Item<'i>>,
}

impl<'i> Context<'i> {
    /// Creates a new empty [`Context`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Registers a function-like procedural macro.
    ///
    /// The macro will be invoked when encountered in expression or type position with the syntax `macro_name!(...)`,
    /// `macro_name![...]` or `macro_name!{...}`.
    pub fn proc_macro<F, T>(&mut self, ident: String, f: F) -> &mut Self
    where
        F: Fn(T) -> TokenStream + 'i,
        T: Parse,
    {
        self.registry.insert(
            ident,
            Item::ProcMacro(Box::new(move |input| match syn::parse2(input) {
                Ok(input) => f(input),
                Err(err) => err.to_compile_error(),
            })),
        );
        self
    }

    /// Registers a procedural macro attribute.
    ///
    /// The macro will be invoked when used as an attribute on items with the syntax `#[macro_name]` or
    /// `#[macro_name(...)]`.
    pub fn proc_macro_attribute<F, T, U>(&mut self, ident: String, f: F) -> &mut Self
    where
        F: Fn(T, U) -> TokenStream + 'i,
        T: Parse,
        U: Parse,
    {
        self.registry.insert(
            ident,
            Item::ProcMacroAttribute(Box::new(move |input, meta| {
                match (syn::parse2(input), syn::parse2(meta)) {
                    (Ok(input), Ok(meta)) => f(input, meta),
                    (Err(err), _) => err.to_compile_error(),
                    (_, Err(err)) => err.to_compile_error(),
                }
            })),
        );
        self
    }

    /// Registers a derive procedural macro.
    ///
    /// The macro will be invoked when used in a `#[derive(...)]` attribute. Generated implementations will be added
    /// after the original item.
    pub fn proc_macro_derive<F, T>(&mut self, ident: String, f: F, attributes: Vec<String>) -> &mut Self
    where
        F: Fn(T) -> TokenStream + 'i,
        T: Parse,
    {
        self.registry.insert(
            ident,
            Item::ProcMacroDerive(
                Box::new(move |input| match syn::parse2(input) {
                    Ok(input) => f(input),
                    Err(err) => err.to_compile_error(),
                }),
                attributes,
            ),
        );
        self
    }

    pub fn transform(&self, input: TokenStream) -> TokenStream {
        let mut input = syn::parse2(input).unwrap();
        let mut visitor = ProcMacroVisitor { ctx: self };
        visitor.visit_file_mut(&mut input);
        quote! { #input }
    }

    fn expand_item<I: ItemLike + Parse + ToTokens + Clone>(&self, mut item: I) -> Vec<I> {
        for i in 0..item.attrs_mut().len() {
            let path = item.attrs_mut()[i].path().to_token_stream().to_string();
            if let Some(Item::ProcMacroAttribute(f)) = self.registry.get(&path) {
                let attrs = item.attrs_mut();
                let suffix_attrs = attrs.drain(i + 1..).collect::<Vec<_>>();
                let attr = attrs.pop().unwrap();
                let prefix_attrs = take(attrs);
                *attrs = suffix_attrs;
                let meta_tokens = match attr.meta {
                    syn::Meta::Path(_path) => Default::default(),
                    syn::Meta::List(meta_list) => meta_list.tokens,
                    syn::Meta::NameValue(_meta_name_value) => {
                        panic!("unexpected MetaNameValue for #[{path}]");
                    }
                };
                let input_tokens = item.to_token_stream();
                let output_tokens = f(input_tokens, meta_tokens);
                return parse_repeated::<I>(output_tokens)
                    .unwrap()
                    .into_iter()
                    .flat_map(|mut item| {
                        let attrs = item.attrs_mut();
                        let mut new_attrs = prefix_attrs.clone();
                        new_attrs.extend(take(attrs));
                        *attrs = new_attrs;
                        self.expand_item(item)
                    })
                    .collect();
            } else if path == "derive" {
                let mut item_cloned = item.clone();
                let attrs = item_cloned.attrs_mut();
                let suffix_attrs = attrs.drain(i + 1..).collect::<Vec<_>>();
                let attr = attrs.pop().unwrap();
                let mut prefix_attrs = take(attrs);
                *attrs = suffix_attrs;
                let meta_tokens = match attr.meta {
                    syn::Meta::Path(_path) => panic!("malformed `derive` attribute input"),
                    syn::Meta::List(meta_list) => meta_list.tokens,
                    syn::Meta::NameValue(_meta_name_value) => panic!("malformed `derive` attribute input"),
                };
                let (extract, keep) = Punctuated::<syn::Ident, syn::Token![,]>::parse_terminated
                    .parse2(meta_tokens)
                    .unwrap()
                    .into_iter()
                    .partition_map::<Vec<_>, Vec<_>, _, _, _>(|ident| match self.registry.get(&ident.to_string()) {
                        Some(Item::ProcMacroDerive(f, attrs)) => Either::Left((f, attrs)),
                        _ => Either::Right(ident),
                    });
                if extract.is_empty() {
                    continue;
                }
                item = item_cloned;
                let mut helper_attrs = HashSet::new();
                let output_items = extract
                    .into_iter()
                    .flat_map(|(f, attrs)| {
                        helper_attrs.extend(attrs.iter().cloned());
                        let input_tokens = item.to_token_stream();
                        let output_tokens = f(input_tokens);
                        let mut items = parse_repeated::<I>(output_tokens).unwrap();
                        for item in &mut items {
                            let attrs = item.attrs_mut();
                            let mut new_attrs = prefix_attrs.clone();
                            new_attrs.extend(take(attrs));
                            *attrs = new_attrs;
                        }
                        items
                    })
                    .collect::<Vec<_>>();
                item.visit_mut(&mut DeriveVisitor { helper_attrs });
                if !keep.is_empty() {
                    prefix_attrs.push(syn::parse_quote! {
                        #[derive(#(#keep),*)]
                    })
                }
                let attrs = item.attrs_mut();
                prefix_attrs.extend(take(attrs));
                *attrs = prefix_attrs;
                return Some(item)
                    .into_iter()
                    .chain(output_items)
                    .flat_map(|item| self.expand_item(item))
                    .collect();
            }
        }
        let item_macro = match item.try_into_macro() {
            Err(item) => return vec![item],
            Ok(item_macro) => item_macro,
        };
        let path = item_macro.as_macro().path.to_token_stream().to_string();
        let Some(Item::ProcMacro(f)) = self.registry.get(&path) else {
            return vec![I::from_macro(item_macro)];
        };
        let (prefix_attrs, mac) = item_macro.into_attrs_and_macro();
        let input_tokens = mac.tokens;
        let output_tokens = f(input_tokens);
        parse_repeated::<I>(output_tokens)
            .unwrap()
            .into_iter()
            .flat_map(|mut item| {
                let attrs = item.attrs_mut();
                let mut new_attrs = prefix_attrs.clone();
                new_attrs.extend(take(attrs));
                *attrs = new_attrs;
                self.expand_item(item)
            })
            .collect()
    }
}

fn parse_repeated<T: Parse>(tokens: TokenStream) -> syn::Result<Vec<T>> {
    let parser = |input: ParseStream| {
        let mut items = vec![];
        while !input.is_empty() {
            items.push(input.parse::<T>()?);
        }
        Ok(items)
    };
    parser.parse2(tokens)
}

struct DeriveVisitor {
    helper_attrs: HashSet<String>,
}

impl VisitMut for DeriveVisitor {
    fn visit_attributes_mut(&mut self, attrs: &mut Vec<syn::Attribute>) {
        attrs.retain(|attr| {
            let path = attr.path().to_token_stream().to_string();
            !self.helper_attrs.contains(&path)
        });
    }
}

struct ProcMacroVisitor<'i> {
    ctx: &'i Context<'i>,
}

impl<'i> VisitMut for ProcMacroVisitor<'i> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let syn::Expr::Macro(expr_macro) = expr {
            let path = expr_macro.mac.path.to_token_stream().to_string();
            if let Some(Item::ProcMacro(f)) = self.ctx.registry.get(&path) {
                let input_tokens = expr_macro.mac.tokens.clone();
                let output_tokens = f(input_tokens);
                *expr = syn::parse2(output_tokens).unwrap();
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr)
    }

    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        if let syn::Type::Macro(ty_macro) = ty {
            let path = ty_macro.mac.path.to_token_stream().to_string();
            if let Some(Item::ProcMacro(f)) = self.ctx.registry.get(&path) {
                let input_tokens = ty_macro.mac.tokens.clone();
                let output_tokens = f(input_tokens);
                *ty = syn::parse2(output_tokens).unwrap();
            }
        }
        syn::visit_mut::visit_type_mut(self, ty)
    }

    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        block.stmts = take(&mut block.stmts)
            .into_iter()
            .flat_map(|stmt| match stmt {
                syn::Stmt::Item(item) => self.ctx.expand_item(item).into_iter().map(syn::Stmt::Item).collect(),
                _ => vec![stmt],
            })
            .collect();
        syn::visit_mut::visit_block_mut(self, block)
    }

    fn visit_file_mut(&mut self, file: &mut syn::File) {
        file.items = take(&mut file.items)
            .into_iter()
            .flat_map(|item| self.ctx.expand_item(item))
            .collect();
        syn::visit_mut::visit_file_mut(self, file)
    }

    fn visit_item_mod_mut(&mut self, item_mod: &mut syn::ItemMod) {
        if let Some((_, items)) = &mut item_mod.content {
            *items = take(items)
                .into_iter()
                .flat_map(|item| self.ctx.expand_item(item))
                .collect();
        }
        syn::visit_mut::visit_item_mod_mut(self, item_mod)
    }

    fn visit_item_trait_mut(&mut self, item_trait: &mut syn::ItemTrait) {
        item_trait.items = take(&mut item_trait.items)
            .into_iter()
            .flat_map(|trait_item| self.ctx.expand_item(trait_item))
            .collect();
        syn::visit_mut::visit_item_trait_mut(self, item_trait)
    }

    fn visit_item_impl_mut(&mut self, item_impl: &mut syn::ItemImpl) {
        item_impl.items = take(&mut item_impl.items)
            .into_iter()
            .flat_map(|impl_item| self.ctx.expand_item(impl_item))
            .collect();
        syn::visit_mut::visit_item_impl_mut(self, item_impl)
    }

    fn visit_item_foreign_mod_mut(&mut self, item_foreign_mod: &mut syn::ItemForeignMod) {
        item_foreign_mod.items = take(&mut item_foreign_mod.items)
            .into_iter()
            .flat_map(|foreign_item| self.ctx.expand_item(foreign_item))
            .collect();
        syn::visit_mut::visit_item_foreign_mod_mut(self, item_foreign_mod)
    }
}

trait ItemMacroLike {
    fn as_macro(&self) -> &syn::Macro;
    fn into_attrs_and_macro(self) -> (Vec<syn::Attribute>, syn::Macro);
}

impl ItemMacroLike for syn::ItemMacro {
    fn as_macro(&self) -> &syn::Macro {
        &self.mac
    }

    fn into_attrs_and_macro(self) -> (Vec<syn::Attribute>, syn::Macro) {
        (self.attrs, self.mac)
    }
}

impl ItemMacroLike for syn::TraitItemMacro {
    fn as_macro(&self) -> &syn::Macro {
        &self.mac
    }

    fn into_attrs_and_macro(self) -> (Vec<syn::Attribute>, syn::Macro) {
        (self.attrs, self.mac)
    }
}

impl ItemMacroLike for syn::ImplItemMacro {
    fn as_macro(&self) -> &syn::Macro {
        &self.mac
    }

    fn into_attrs_and_macro(self) -> (Vec<syn::Attribute>, syn::Macro) {
        (self.attrs, self.mac)
    }
}

impl ItemMacroLike for syn::ForeignItemMacro {
    fn as_macro(&self) -> &syn::Macro {
        &self.mac
    }

    fn into_attrs_and_macro(self) -> (Vec<syn::Attribute>, syn::Macro) {
        (self.attrs, self.mac)
    }
}

trait ItemLike: Sized {
    type ItemMacro: ItemMacroLike;
    fn try_into_macro(self) -> Result<Self::ItemMacro, Self>;
    fn from_macro(mac: Self::ItemMacro) -> Self;
    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute>;
    fn visit_mut<V: VisitMut>(&mut self, visitor: &mut V);
}

impl ItemLike for syn::Item {
    type ItemMacro = syn::ItemMacro;

    fn try_into_macro(self) -> Result<Self::ItemMacro, Self> {
        match self {
            syn::Item::Macro(item_macro) => Ok(item_macro),
            _ => Err(self),
        }
    }

    fn from_macro(mac: Self::ItemMacro) -> Self {
        syn::Item::Macro(mac)
    }

    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            syn::Item::Const(item) => &mut item.attrs,
            syn::Item::Enum(item) => &mut item.attrs,
            syn::Item::ExternCrate(item) => &mut item.attrs,
            syn::Item::Fn(item) => &mut item.attrs,
            syn::Item::ForeignMod(item) => &mut item.attrs,
            syn::Item::Impl(item) => &mut item.attrs,
            syn::Item::Macro(item) => &mut item.attrs,
            syn::Item::Mod(item) => &mut item.attrs,
            syn::Item::Static(item) => &mut item.attrs,
            syn::Item::Struct(item) => &mut item.attrs,
            syn::Item::Trait(item) => &mut item.attrs,
            syn::Item::TraitAlias(item) => &mut item.attrs,
            syn::Item::Type(item) => &mut item.attrs,
            syn::Item::Union(item) => &mut item.attrs,
            syn::Item::Use(item) => &mut item.attrs,
            _ => unimplemented!(),
        }
    }

    fn visit_mut<V: VisitMut>(&mut self, visitor: &mut V) {
        visitor.visit_item_mut(self);
    }
}

impl ItemLike for syn::TraitItem {
    type ItemMacro = syn::TraitItemMacro;

    fn try_into_macro(self) -> Result<Self::ItemMacro, Self> {
        match self {
            syn::TraitItem::Macro(item_macro) => Ok(item_macro),
            _ => Err(self),
        }
    }

    fn from_macro(mac: Self::ItemMacro) -> Self {
        syn::TraitItem::Macro(mac)
    }

    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            syn::TraitItem::Const(item) => &mut item.attrs,
            syn::TraitItem::Fn(item) => &mut item.attrs,
            syn::TraitItem::Macro(item) => &mut item.attrs,
            syn::TraitItem::Type(item) => &mut item.attrs,
            _ => unimplemented!(),
        }
    }

    fn visit_mut<V: VisitMut>(&mut self, visitor: &mut V) {
        visitor.visit_trait_item_mut(self);
    }
}

impl ItemLike for syn::ImplItem {
    type ItemMacro = syn::ImplItemMacro;

    fn try_into_macro(self) -> Result<Self::ItemMacro, Self> {
        match self {
            syn::ImplItem::Macro(item_macro) => Ok(item_macro),
            _ => Err(self),
        }
    }

    fn from_macro(mac: Self::ItemMacro) -> Self {
        syn::ImplItem::Macro(mac)
    }

    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            syn::ImplItem::Const(item) => &mut item.attrs,
            syn::ImplItem::Fn(item) => &mut item.attrs,
            syn::ImplItem::Macro(item) => &mut item.attrs,
            syn::ImplItem::Type(item) => &mut item.attrs,
            _ => unimplemented!(),
        }
    }

    fn visit_mut<V: VisitMut>(&mut self, visitor: &mut V) {
        visitor.visit_impl_item_mut(self);
    }
}

impl ItemLike for syn::ForeignItem {
    type ItemMacro = syn::ForeignItemMacro;

    fn try_into_macro(self) -> Result<Self::ItemMacro, Self> {
        match self {
            syn::ForeignItem::Macro(item_macro) => Ok(item_macro),
            _ => Err(self),
        }
    }

    fn from_macro(mac: Self::ItemMacro) -> Self {
        syn::ForeignItem::Macro(mac)
    }

    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            syn::ForeignItem::Fn(item) => &mut item.attrs,
            syn::ForeignItem::Macro(item) => &mut item.attrs,
            syn::ForeignItem::Static(item) => &mut item.attrs,
            syn::ForeignItem::Type(item) => &mut item.attrs,
            _ => unimplemented!(),
        }
    }

    fn visit_mut<V: VisitMut>(&mut self, visitor: &mut V) {
        visitor.visit_foreign_item_mut(self);
    }
}
