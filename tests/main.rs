use macro_expand::Context;
use proc_macro2::TokenStream;
use quote::quote;

fn dummy_expand(input: TokenStream) -> TokenStream {
    let _ = input;
    quote! { const EXPANDED: bool = true; }
}

#[test]
fn module_basic_use() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::bar;
        bar!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::bar;
            const EXPANDED: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_no_use_no_expand() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        bar!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            bar!();
        }
        .to_string()
    );
}

#[test]
fn module_block_scope_inherits() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::bar;
        fn test() {
            bar!();
        }
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::bar;
            fn test() {
                const EXPANDED: bool = true;
            }
        }
        .to_string()
    );
}

#[test]
fn module_mod_scope_isolates() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::bar;
        mod inner {
            bar!();
        }
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::bar;
            mod inner {
                bar!();
            }
        }
        .to_string()
    );
}

#[test]
fn module_mod_with_own_use() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        mod inner {
            use foo::bar;
            bar!();
        }
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            mod inner {
                use foo::bar;
                const EXPANDED: bool = true;
            }
        }
        .to_string()
    );
}

#[test]
fn module_block_scope_local_use() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        bar!();
        fn test() {
            use foo::bar;
            bar!();
        }
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            bar!();
            fn test() {
                use foo::bar;
                const EXPANDED: bool = true;
            }
        }
        .to_string()
    );
}

#[test]
fn module_nested_use() {
    let mut ctx = Context::new();
    ctx.module("foo").module("bar").proc_macro("baz", dummy_expand);

    let input = quote! {
        use foo::bar::baz;
        baz!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::bar::baz;
            const EXPANDED: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_grouped_use() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::{bar};
        bar!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::{bar};
            const EXPANDED: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_rename_use() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::bar as qux;
        qux!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::bar as qux;
            const EXPANDED: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_glob_use() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::*;
        bar!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::*;
            const EXPANDED: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_glob_no_expand_without_use() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use baz::*;
        bar!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use baz::*;
            bar!();
        }
        .to_string()
    );
}

#[test]
fn module_glob_nested() {
    let mut ctx = Context::new();
    ctx.module("foo").module("bar").proc_macro("baz", dummy_expand);

    let input = quote! {
        use foo::bar::*;
        baz!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::bar::*;
            const EXPANDED: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_glob_explicit_name_takes_priority() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);
    ctx.module("other").proc_macro("bar", |_: TokenStream| {
        quote! { const OTHER: bool = true; }
    });

    let input = quote! {
        use foo::*;
        use other::bar;
        bar!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::*;
            use other::bar;
            const OTHER: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_glob_multiple_macros() {
    let mut ctx = Context::new();
    ctx.module("foo")
        .proc_macro("bar", |_: TokenStream| {
            quote! { const BAR: bool = true; }
        })
        .proc_macro("baz", |_: TokenStream| {
            quote! { const BAZ: bool = true; }
        });

    let input = quote! {
        use foo::*;
        bar!();
        baz!();
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::*;
            const BAR: bool = true;
            const BAZ: bool = true;
        }
        .to_string()
    );
}

#[test]
fn module_glob_mod_scope_isolates() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::*;
        mod inner {
            bar!();
        }
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::*;
            mod inner {
                bar!();
            }
        }
        .to_string()
    );
}

#[test]
fn module_glob_block_scope_inherits() {
    let mut ctx = Context::new();
    ctx.module("foo").proc_macro("bar", dummy_expand);

    let input = quote! {
        use foo::*;
        fn test() {
            bar!();
        }
    };
    assert_eq!(
        ctx.transform(input).to_string(),
        quote! {
            use foo::*;
            fn test() {
                const EXPANDED: bool = true;
            }
        }
        .to_string()
    );
}
