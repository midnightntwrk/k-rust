//! A helper's class does not depend on where it stands beside its item's marker (NT-33): a
//! helper written before the marker is handed to the marker, which accepts or refuses it as it
//! does after it, for every marker a helper is handed to and every item a marker expands.

mod support;

use krs_syntax::surface::AttributeMacro;
use proc_macro2::TokenStream;
use support::TestEnvironment;

/// The outcome of one expansion: accepted, or the code and message of each diagnostic.
fn outcome(result: &krs_expand::Result<TokenStream>) -> Result<(), Vec<(String, String)>> {
    match result {
        Ok(_) => Ok(()),
        Err(error) => Err(error
            .diagnostics()
            .map(|diagnostic| {
                (
                    diagnostic.code.as_str().to_owned(),
                    diagnostic.message.clone(),
                )
            })
            .collect()),
    }
}

/// Expands `item` with the helper `#[k::helper(payload)]` written before the marker
/// `#[k::marker(keys)]` (rustc expands the helper first) and after it (the marker first).
fn before_and_after(
    helper: AttributeMacro,
    payload: &str,
    marker: AttributeMacro,
    keys: &str,
    item: &str,
) -> [Result<(), Vec<(String, String)>>; 2] {
    let env = TestEnvironment::new(None);
    let marker_attribute = if keys.is_empty() {
        format!("#[k::{}]", marker.name())
    } else {
        format!("#[k::{}({keys})]", marker.name())
    };
    let helper_attribute = format!("#[k::{}({payload})]", helper.name());
    let before = krs_expand::expand_attribute(
        helper,
        &env,
        payload.parse().unwrap(),
        format!("{marker_attribute}\n{item}").parse().unwrap(),
    );
    let after = krs_expand::expand_attribute(
        marker,
        &env,
        keys.parse().unwrap(),
        format!("{helper_attribute}\n{item}").parse().unwrap(),
    );
    [outcome(&before), outcome(&after)]
}

/// A `fn` whose result holds `name @ pattern`, which is no Rust item.
const ALIAS_BODY: &str =
    "fn hold(k::term![Cmd::Go(x)]: Term<Cmd>) -> Term<Cmd> { y @ Cmd::Hold(_) }";

/// A function shorthand, whose body states its function's equation.
const SHORTHAND: &str = "pub fn Twice(x: Term<Int>) -> Term<Int> { int::add(x, x) }";

/// An initializer.
const INITIALIZER: &str = "pub fn init(pgm: Exp) -> Self { Self { k: k::k![pgm] } }";

#[test]
fn a_helper_before_its_marker_is_answered_as_after_it() {
    use AttributeMacro::{Ensures, Function, Init, Priority, Requires, Rule};
    let cases = [
        (Requires, "int::gt(x, 0)", Rule, "", ALIAS_BODY),
        (Priority, "20", Rule, "", ALIAS_BODY),
        (Requires, "int::gt(x, 0)", Function, "total", SHORTHAND),
        (Ensures, "int::gt(x, 0)", Function, "total", SHORTHAND),
        (Priority, "20", Function, "total", SHORTHAND),
        (Requires, "true", Init, "", INITIALIZER),
        (Priority, "20", Init, "", INITIALIZER),
    ];
    for (helper, payload, marker, keys, item) in cases {
        let [before, after] = before_and_after(helper, payload, marker, keys, item);
        assert_eq!(
            before,
            after,
            "#[k::{}] before #[k::{}] on {item}",
            helper.name(),
            marker.name()
        );
        if let Err(diagnostics) = &before {
            assert!(
                diagnostics
                    .iter()
                    .all(|(code, _)| code != "krs::expand::orphan-helper"),
                "{diagnostics:?}"
            );
        }
    }
}

/// The retired `#[k::priority(N)]` before a rule's marker names the rule's own order key, also
/// on an item that is no Rust item.
#[test]
fn a_retired_priority_before_a_rule_names_the_rule_s_key() {
    let [before, _] = before_and_after(
        AttributeMacro::Priority,
        "20",
        AttributeMacro::Rule,
        "",
        ALIAS_BODY,
    );
    let diagnostics = before.unwrap_err();
    assert_eq!(
        diagnostics,
        [(
            "krs::syntax::retired-attribute".to_owned(),
            "`#[k::priority(..)]` is retired; write `#[k::rule(priority = 20)]`".to_owned()
        )]
    );
}
