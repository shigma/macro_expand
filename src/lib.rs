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
/// The [`Context`] holds a registry of macro implementations and provides methods to transform Rust source code by
/// expanding these macros.
#[derive(Default)]
pub struct Context<'i> {
    registry: HashMap<String, Item<'i>>,
    modules: HashMap<String, Context<'i>>,
}

/// The kind of scope frame, determining use-import visibility.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    /// Block scope (fn body, `{}`): inherits outer imports.
    Block,
    /// Module scope (`mod`): isolates imports; outer imports are not visible.
    Module,
}

/// A scope frame tracking `use` imports at a given nesting level.
struct ScopeFrame {
    kind: ScopeKind,
    /// Maps local name → full path segments.
    /// e.g. `use foo::bar;` → { "bar" → ["foo", "bar"] }
    /// e.g. `use foo::bar as qux;` → { "qux" → ["foo", "bar"] }
    imports: HashMap<String, Vec<String>>,
    /// Glob import prefixes, e.g. `use foo::*;` → [["foo"]].
    globs: Vec<Vec<String>>,
}

impl ScopeFrame {
    fn new(kind: ScopeKind) -> Self {
        Self {
            kind,
            imports: HashMap::new(),
            globs: Vec::new(),
        }
    }

    /// Collect use imports from a `UseTree` into a scope frame.
    fn collect_use_tree(&mut self, prefix: &[String], tree: &syn::UseTree) {
        match tree {
            syn::UseTree::Path(use_path) => {
                let mut new_prefix = prefix.to_vec();
                new_prefix.push(use_path.ident.to_string());
                self.collect_use_tree(&new_prefix, &use_path.tree);
            }
            syn::UseTree::Name(use_name) => {
                let ident = use_name.ident.to_string();
                let mut segments = prefix.to_vec();
                segments.push(ident.clone());
                self.imports.insert(ident, segments);
            }
            syn::UseTree::Rename(use_rename) => {
                let original = use_rename.ident.to_string();
                let alias = use_rename.rename.to_string();
                let mut segments = prefix.to_vec();
                segments.push(original);
                self.imports.insert(alias, segments);
            }
            syn::UseTree::Group(use_group) => {
                for item in &use_group.items {
                    self.collect_use_tree(prefix, item);
                }
            }
            syn::UseTree::Glob(_) => {
                self.globs.push(prefix.to_vec());
            }
        }
    }

    /// Scan a list of items for `use` statements and populate the scope frame.
    fn collect_imports_from_items(&mut self, items: &[syn::Item]) {
        for item in items {
            if let syn::Item::Use(use_item) = item {
                self.collect_use_tree(&[], &use_item.tree);
            }
        }
    }

    /// Scan a list of statements for `use` statements and populate the scope frame.
    fn collect_imports_from_stmts(&mut self, stmts: &[syn::Stmt]) {
        for stmt in stmts {
            if let syn::Stmt::Item(syn::Item::Use(use_item)) = stmt {
                self.collect_use_tree(&[], &use_item.tree);
            }
        }
    }
}

impl<'i> Context<'i> {
    /// Creates a new empty [`Context`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns (or creates) a sub-module with the given name.
    ///
    /// Macros registered on a sub-module are only visible when the user's source
    /// code imports them via `use module_name::macro_name;`.
    pub fn module(&mut self, name: impl Into<String>) -> &mut Context<'i> {
        self.modules.entry(name.into()).or_default()
    }

    /// Registers a function-like procedural macro.
    ///
    /// The macro will be invoked when encountered in expression or type position with the syntax `macro_name!(...)`,
    /// `macro_name![...]` or `macro_name!{...}`.
    pub fn proc_macro<F, T>(&mut self, ident: impl Into<String>, f: F) -> &mut Self
    where
        F: Fn(T) -> TokenStream + 'i,
        T: Parse,
    {
        self.registry.insert(
            ident.into(),
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
    pub fn proc_macro_attribute<F, T, U>(&mut self, ident: impl Into<String>, f: F) -> &mut Self
    where
        F: Fn(T, U) -> TokenStream + 'i,
        T: Parse,
        U: Parse,
    {
        self.registry.insert(
            ident.into(),
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
    pub fn proc_macro_derive<F, T>(&mut self, ident: impl Into<String>, f: F, attributes: Vec<String>) -> &mut Self
    where
        F: Fn(T) -> TokenStream + 'i,
        T: Parse,
    {
        self.registry.insert(
            ident.into(),
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
        let mut visitor = ProcMacroVisitor {
            ctx: self,
            scopes: vec![],
        };
        visitor.visit_file_mut(&mut input);
        quote! { #input }
    }

    /// Resolve a name by looking it up in the global registry first,
    /// then walking the scope stack (respecting block vs. module boundaries).
    fn resolve<'a>(&'a self, name: &str, scopes: &[ScopeFrame]) -> Option<&'a Item<'i>> {
        // Walk scopes from innermost to outermost, stopping at module boundaries.
        for scope in scopes.iter().rev() {
            // Explicit imports take priority over globs.
            if let Some(segments) = scope.imports.get(name) {
                return self.resolve_path(segments);
            }
            // Try glob imports: check if any glob prefix contains this name.
            for glob_prefix in &scope.globs {
                let mut full_path = glob_prefix.clone();
                full_path.push(name.to_string());
                if let Some(item) = self.resolve_path(&full_path) {
                    return Some(item);
                }
            }
            if scope.kind == ScopeKind::Module {
                break;
            }
        }
        None
    }

    /// Resolve a full path (e.g. ["foo", "bar"]) through the module tree.
    fn resolve_path(&self, segments: &[String]) -> Option<&Item<'i>> {
        let (last, modules) = segments.split_last()?;
        let mut ctx = self;
        for seg in modules {
            ctx = ctx.modules.get(seg)?;
        }
        ctx.registry.get(last)
    }

    fn expand_item<I: ItemLike + Parse + ToTokens + Clone>(&self, mut item: I, scopes: &[ScopeFrame]) -> Vec<I> {
        for i in 0..item.attrs_mut().len() {
            let path = item.attrs_mut()[i].path().to_token_stream().to_string();
            if let Some(Item::ProcMacroAttribute(f)) = self.resolve(&path, scopes) {
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
                        self.expand_item(item, scopes)
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
                    .partition_map::<Vec<_>, Vec<_>, _, _, _>(|ident| match self.resolve(&ident.to_string(), scopes) {
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
                    .flat_map(|item| self.expand_item(item, scopes))
                    .collect();
            }
        }
        let item_macro = match item.try_into_macro() {
            Err(item) => return vec![item],
            Ok(item_macro) => item_macro,
        };
        let path = item_macro.as_macro().path.to_token_stream().to_string();
        let Some(Item::ProcMacro(f)) = self.resolve(&path, scopes) else {
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
                self.expand_item(item, scopes)
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
    scopes: Vec<ScopeFrame>,
}

impl<'i> ProcMacroVisitor<'i> {
    fn resolve_macro(&self, name: &str) -> Option<&Item<'i>> {
        self.ctx.resolve(name, &self.scopes)
    }
}

impl<'i> VisitMut for ProcMacroVisitor<'i> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let syn::Expr::Macro(expr_macro) = expr {
            let path = expr_macro.mac.path.to_token_stream().to_string();
            if let Some(Item::ProcMacro(f)) = self.resolve_macro(&path) {
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
            if let Some(Item::ProcMacro(f)) = self.resolve_macro(&path) {
                let input_tokens = ty_macro.mac.tokens.clone();
                let output_tokens = f(input_tokens);
                *ty = syn::parse2(output_tokens).unwrap();
            }
        }
        syn::visit_mut::visit_type_mut(self, ty)
    }

    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        let mut frame = ScopeFrame::new(ScopeKind::Block);
        frame.collect_imports_from_stmts(&block.stmts);
        self.scopes.push(frame);

        block.stmts = take(&mut block.stmts)
            .into_iter()
            .flat_map(|stmt| match stmt {
                syn::Stmt::Item(item) => self
                    .ctx
                    .expand_item(item, &self.scopes)
                    .into_iter()
                    .map(syn::Stmt::Item)
                    .collect(),
                syn::Stmt::Macro(stmt_macro) => {
                    let path = stmt_macro.mac.path.to_token_stream().to_string();
                    if let Some(Item::ProcMacro(f)) = self.resolve_macro(&path) {
                        let output_tokens = f(stmt_macro.mac.tokens.clone());
                        parse_repeated::<syn::Item>(output_tokens)
                            .unwrap()
                            .into_iter()
                            .map(syn::Stmt::Item)
                            .collect()
                    } else {
                        vec![syn::Stmt::Macro(stmt_macro)]
                    }
                }
                _ => vec![stmt],
            })
            .collect();
        syn::visit_mut::visit_block_mut(self, block);

        self.scopes.pop();
    }

    fn visit_file_mut(&mut self, file: &mut syn::File) {
        let mut frame = ScopeFrame::new(ScopeKind::Module);
        frame.collect_imports_from_items(&file.items);
        self.scopes.push(frame);

        file.items = take(&mut file.items)
            .into_iter()
            .flat_map(|item| self.ctx.expand_item(item, &self.scopes))
            .collect();
        syn::visit_mut::visit_file_mut(self, file);

        self.scopes.pop();
    }

    fn visit_item_mod_mut(&mut self, item_mod: &mut syn::ItemMod) {
        let Some((_, items)) = &mut item_mod.content else {
            return;
        };

        let mut frame = ScopeFrame::new(ScopeKind::Module);
        frame.collect_imports_from_items(items);
        self.scopes.push(frame);

        *items = take(items)
            .into_iter()
            .flat_map(|item| self.ctx.expand_item(item, &self.scopes))
            .collect();
        syn::visit_mut::visit_item_mod_mut(self, item_mod);

        self.scopes.pop();
    }

    fn visit_item_trait_mut(&mut self, item_trait: &mut syn::ItemTrait) {
        item_trait.items = take(&mut item_trait.items)
            .into_iter()
            .flat_map(|trait_item| self.ctx.expand_item(trait_item, &self.scopes))
            .collect();
        syn::visit_mut::visit_item_trait_mut(self, item_trait)
    }

    fn visit_item_impl_mut(&mut self, item_impl: &mut syn::ItemImpl) {
        item_impl.items = take(&mut item_impl.items)
            .into_iter()
            .flat_map(|impl_item| self.ctx.expand_item(impl_item, &self.scopes))
            .collect();
        syn::visit_mut::visit_item_impl_mut(self, item_impl)
    }

    fn visit_item_foreign_mod_mut(&mut self, item_foreign_mod: &mut syn::ItemForeignMod) {
        item_foreign_mod.items = take(&mut item_foreign_mod.items)
            .into_iter()
            .flat_map(|foreign_item| self.ctx.expand_item(foreign_item, &self.scopes))
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
