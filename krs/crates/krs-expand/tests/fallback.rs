//! Expands every tour-minimal invocation in an ordinary (non-proc-macro)
//! process, where `proc_macro2` uses its fallback implementation. A surviving
//! `proc_macro`-only call panics here.

mod support;

use krs_syntax::surface::{AttributeMacro, FunctionMacro};
use proc_macro2::TokenStream;
use support::{Expansion, TestEnvironment, expand_tour_minimal};

/// Every expansion's kind and output, each nested invocation right after its
/// parent.
fn flatten(expansions: &[Expansion], output: &mut Vec<(&'static str, TokenStream)>) {
    for expansion in expansions {
        output.push((expansion.kind, expansion.output.clone()));
        let nested = expansion
            .nested
            .iter()
            .map(|(_, _, nested)| nested)
            .collect::<Vec<_>>();
        for nested in nested {
            flatten(std::slice::from_ref(nested), output);
        }
    }
}

fn tour_minimal_outputs() -> Vec<(&'static str, TokenStream)> {
    let (_, expansions) = expand_tour_minimal();
    let mut outputs = Vec::new();
    flatten(&expansions, &mut outputs);
    outputs
}

#[test]
fn tour_minimal_expands_in_a_fallback_process() {
    let outputs = tour_minimal_outputs();
    let kinds = outputs.iter().map(|(kind, _)| *kind).collect::<Vec<_>>();
    assert_eq!(
        kinds,
        [
            FunctionMacro::Sorts.name(),
            AttributeMacro::Constructors.name(),
            AttributeMacro::Configuration.name(),
            AttributeMacro::Init.name(),
            FunctionMacro::Rules.name(),
        ]
    );
    let outputs = outputs
        .into_iter()
        .map(|(_, output)| output)
        .collect::<Vec<_>>();
    let sorts = outputs[0].to_string();
    assert!(sorts.contains(":: k :: __krs_host_provenance (\"\" , const { const __KRS_AUTHORED"));
    assert!(sorts.contains("& :: k :: __KrsRawProvenance :: new (& [\"src/lib.rs\"]"));
    // `k::sorts! { ... }` spans 10:1 through 12:2 of the authored file.
    assert!(sorts.contains(
        ":: k :: __KrsRawAnchor :: new (0usize , false , (10u32 , 1u32) , (12u32 , 2u32) , true)"
    ));
    // The clause range ends on tokens `krs-syntax` re-quotes at the call site;
    // the environment locates them at `k::rules!`, so the nonce is rustc's
    // (native `krs emit-k` build of tour-minimal, display file `src/lib.rs`).
    assert!(
        outputs[4]
            .to_string()
            .contains("__krs_head_rule_sort_edc54d797361b2d2")
    );
    assert!(outputs.iter().all(|output| !output.is_empty()));
}

#[test]
fn every_builtin_token_island_expands_in_a_fallback_process() {
    let env = TestEnvironment::new(None);
    for (entry, input) in [
        (FunctionMacro::Id, "\"$x\""),
        (FunctionMacro::Bytes, "b\"\\x00\""),
        (FunctionMacro::Anonymous, ""),
        (FunctionMacro::OrBool, "a, b"),
    ] {
        let output = krs_expand::expand_function(entry, &env, input.parse().unwrap()).unwrap();
        assert!(output.to_string().contains("has no runtime value"));
    }
    let error =
        krs_expand::expand_function(FunctionMacro::Id, &env, "\"x\"".parse().unwrap()).unwrap_err();
    assert_eq!(error.to_string(), "invalid builtin `Id` token");
}

/// A failed `#[k::init]` leaves a stand-in for the payload function the
/// configuration names, under the method's `#[cfg]`, and nothing else; a
/// successful one emits no stand-in.
#[test]
fn a_failed_initializer_leaves_a_payload_stand_in() {
    let env = TestEnvironment::new(None);
    let failing = r#"
        #[cfg(feature = "machine")]
        pub fn init(pgm: Stmt) -> Self {
            Self { k: k::k![pgm], mem: k::anonymous!(Bytes, "_M") }
        }
    "#;
    let error = krs_expand::expand_attribute(
        AttributeMacro::Init,
        &env,
        TokenStream::new(),
        failing.parse().unwrap(),
    )
    .unwrap_err();
    let stand_in = error.stand_in().to_string();
    assert!(
        stand_in.starts_with("# [cfg (feature = \"machine\")] # [doc (hidden)] pub (crate) fn __krs_initializer_payload ()"),
        "{stand_in}"
    );
    assert!(stand_in.contains(":: core :: unreachable !"), "{stand_in}");
    assert!(!stand_in.contains("fn init"), "{stand_in}");
    let rendered = error
        .into_compile_error(proc_macro2::Span::call_site())
        .to_string();
    assert!(
        rendered.starts_with(":: core :: compile_error !"),
        "{rendered}"
    );
    assert!(rendered.ends_with(&stand_in), "{rendered}");

    let body_shape = r"
        pub fn init(pgm: Stmt) -> Self {
            let x = 1;
            Self { k: k::k![pgm] }
        }
    ";
    let error = krs_expand::expand_attribute(
        AttributeMacro::Init,
        &env,
        TokenStream::new(),
        body_shape.parse().unwrap(),
    )
    .unwrap_err();
    assert!(
        error
            .stand_in()
            .to_string()
            .starts_with("# [doc (hidden)] pub (crate) fn __krs_initializer_payload")
    );
}

#[test]
fn entry_point_names_round_trip() {
    for &entry in AttributeMacro::ALL {
        assert_eq!(AttributeMacro::from_name(entry.name()), Some(entry));
    }
    for &entry in FunctionMacro::ALL {
        assert_eq!(FunctionMacro::from_name(entry.name()), Some(entry));
    }
    assert_eq!(AttributeMacro::from_name("sorts"), None);
    assert_eq!(FunctionMacro::from_name("sort"), None);
}

/// Expands a failing attribute and returns its stand-in items, parsed.
fn failed_stand_in(entry: AttributeMacro, attributes: &str, item: &str) -> Vec<syn::Item> {
    let env = TestEnvironment::new(None);
    let error = krs_expand::expand_attribute(
        entry,
        &env,
        attributes.parse().unwrap(),
        item.parse().unwrap(),
    )
    .unwrap_err();
    syn::parse_file(&error.stand_in().to_string())
        .unwrap()
        .items
}

fn tokens(item: &impl quote::ToTokens) -> String {
    quote::ToTokens::to_token_stream(item).to_string()
}

/// A failed `#[k::constructors]` enum leaves the enum with its name,
/// documentation, and `#[cfg]`, field-less variants of the same kinds without
/// their KRS helpers, and the generated interface other expansions name: a
/// marker function and a rule-application impl per variant, under the enum's
/// and the variant's `#[cfg]`. The enum loses its generics.
#[test]
fn a_failed_enum_family_leaves_its_names_and_interface() {
    let items = failed_stand_in(
        AttributeMacro::Constructors,
        "sort = ObjectTerm",
        r#"
        #[cfg(feature = "objects")]
        /// Objects.
        enum Object<T> {
            /// The empty object.
            #[k::syntax("foo")]
            Foo(),
            #[cfg(feature = "bar")]
            #[k::syntax("bar({value})")]
            Bar { value: Int, rest: T },
            #[k::syntax("baz")]
            Baz,
        }
        "#,
    );
    let syn::Item::Enum(stand_in) = &items[0] else {
        panic!("{items:?}");
    };
    assert_eq!(stand_in.ident, "Object");
    assert!(stand_in.generics.params.is_empty());
    assert_eq!(
        stand_in.attrs.iter().map(tokens).collect::<Vec<_>>(),
        [
            "# [cfg (feature = \"objects\")]",
            "# [doc = \" Objects.\"]",
            "# [allow (dead_code)]",
        ]
    );
    assert_eq!(
        stand_in.variants.iter().map(tokens).collect::<Vec<_>>(),
        [
            "# [doc = \" The empty object.\"] Foo ()",
            "# [cfg (feature = \"bar\")] Bar { }",
            "Baz",
        ]
    );
    let syn::Item::Impl(markers) = &items[1] else {
        panic!("{items:?}");
    };
    assert!(markers.trait_.is_none());
    assert_eq!(
        markers
            .items
            .iter()
            .map(|item| {
                let syn::ImplItem::Fn(function) = item else {
                    panic!("{item:?}");
                };
                function.sig.ident.to_string()
            })
            .collect::<Vec<_>>(),
        [
            "__krs_variant_type_id_Foo",
            "__krs_variant_type_id_Bar",
            "__krs_variant_type_id_Baz",
        ]
    );
    let applications = items[2..]
        .iter()
        .map(|item| {
            let syn::Item::Impl(implementation) = item else {
                panic!("{item:?}");
            };
            let (_, path, _) = implementation.trait_.as_ref().unwrap();
            assert_eq!(
                tokens(&path.segments.last().unwrap().ident),
                "__KrsRuleApplication"
            );
            implementation.attrs.iter().map(tokens).collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        applications,
        [
            vec!["# [cfg (feature = \"objects\")]"],
            vec![
                "# [cfg (feature = \"objects\")]",
                "# [cfg (feature = \"bar\")]"
            ],
            vec!["# [cfg (feature = \"objects\")]"],
        ]
    );
}

/// A failed `#[k::syntax_list]` enum also leaves its sort marker trait and
/// its `KItemSort` impl, which `k::sorts!` membership lines name.
#[test]
fn a_failed_syntax_list_leaves_its_sort_marker() {
    let items = failed_stand_in(
        AttributeMacro::SyntaxList,
        "separator = \",\", bogus",
        "pub enum Objects { Cons { head: Int, tail: Objects }, Nil() }",
    );
    let rendered = items.iter().map(tokens).collect::<Vec<_>>();
    assert_eq!(rendered[0], "pub enum Objects { Cons { } , Nil () , }");
    assert_eq!(rendered.len(), 6, "{rendered:?}");
    assert!(
        rendered[4].ends_with("pub trait ObjectsSort : :: k :: KItemSort { }"),
        "{rendered:?}"
    );
    assert_eq!(rendered[5], "impl :: k :: KItemSort for Objects { }");
}

/// A failed `#[k::spec_module]` leaves an empty module of the same name and
/// visibility under its `#[cfg]`, which another spec module's `imports`
/// names; its items are not re-emitted.
#[test]
fn a_failed_spec_module_leaves_an_empty_module() {
    let items = failed_stand_in(
        AttributeMacro::SpecModule,
        "imports = [crate], bogus",
        "#[cfg(test)] /// Proofs.\n pub(crate) mod first { fn helper() {} }",
    );
    assert_eq!(
        items.iter().map(tokens).collect::<Vec<_>>(),
        ["# [cfg (test)] # [allow (dead_code)] pub (crate) mod first { }"]
    );
}
