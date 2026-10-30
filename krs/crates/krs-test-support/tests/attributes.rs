//! The attribute axis (K8, `class_matrix::attributes`): the attribute list read from the
//! product's parsers, every attribute on every form, and the priorities K7's runs rely on.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use krs_test_support::class_matrix::attributes::{
    Attribute, BASE_KEYS, CASE_PRIORITY, DECLARATION_MACROS, DRIVER_PRIORITY, FORMS, MALFORMED,
    OWISE_SIBLING_PRIORITY, PRIORITY_SIBLING_PRIORITY, Pair, SENTENCE_MACROS, Written, pairs,
};
use krs_test_support::class_matrix::k7::K7;
use krs_test_support::class_matrix::oracle::Outcome;
use krs_test_support::class_matrix::{self, Base, Family};
use syn::visit::Visit;

/// The parsers of a sentence's attribute keys, in `krs-syntax/src/attribute/`: each file, and in
/// it each function (`Type::function` for a method) whose recognized keys the axis must cover.
const PARSERS: [(&str, &[&str]); 2] = [
    (
        "rule.rs",
        &[
            "parse_rule_stream",
            "parse_context_stream",
            "ClaimAttribute::parse_with_label",
        ],
    ),
    (
        "sort.rs",
        &[
            "parse_equation_stream",
            "MatchRestriction::parse_key",
            "parse_simplification_stream",
            "parse_static_clause_tokens",
            "DesugarAttribute::parse_tokens",
            "parse_context_alias_stream",
        ],
    ),
];

/// The string literals a parser compares a key with: a match arm's pattern, an operand of `==`
/// or `!=`.
#[derive(Default)]
struct Keys(BTreeSet<String>);

impl<'ast> Visit<'ast> for Keys {
    fn visit_arm(&mut self, arm: &'ast syn::Arm) {
        Patterns(&mut self.0).visit_pat(&arm.pat);
        syn::visit::visit_arm(self, arm);
    }

    fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
        if matches!(binary.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_)) {
            for side in [&*binary.left, &*binary.right] {
                if let syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(literal),
                    ..
                }) = side
                {
                    self.0.insert(literal.value());
                }
            }
        }
        syn::visit::visit_expr_binary(self, binary);
    }
}

/// The string literals of a pattern.
struct Patterns<'a>(&'a mut BTreeSet<String>);

impl<'ast> Visit<'ast> for Patterns<'_> {
    fn visit_pat(&mut self, pattern: &'ast syn::Pat) {
        if let syn::Pat::Lit(syn::ExprLit {
            lit: syn::Lit::Str(literal),
            ..
        }) = pattern
        {
            self.0.insert(literal.value());
        }
        syn::visit::visit_pat(self, pattern);
    }
}

/// The keys each parser function of [`PARSERS`] recognizes, by `file::function`.
fn parser_keys() -> BTreeMap<String, BTreeSet<String>> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../krs-syntax/src/attribute");
    let mut found = BTreeMap::new();
    for (file, functions) in PARSERS {
        let path = directory.join(file);
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        let parsed = syn::parse_file(&text).unwrap_or_else(|error| panic!("{file}: {error}"));
        let mut take = |name: String, block: &syn::Block| {
            if functions.contains(&name.as_str()) {
                let mut keys = Keys::default();
                keys.visit_block(block);
                found.insert(format!("{file}::{name}"), keys.0);
            }
        };
        for item in &parsed.items {
            match item {
                syn::Item::Fn(function) => take(function.sig.ident.to_string(), &function.block),
                syn::Item::Impl(implementation) => {
                    let syn::Type::Path(owner) = &*implementation.self_ty else {
                        continue;
                    };
                    let Some(owner) = owner.path.segments.last() else {
                        continue;
                    };
                    for inner in &implementation.items {
                        if let syn::ImplItem::Fn(function) = inner {
                            take(
                                format!("{}::{}", owner.ident, function.sig.ident),
                                &function.block,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }
    found
}

#[test]
fn every_key_the_attribute_parsers_recognize_is_an_attribute_of_the_axis() {
    let found = parser_keys();
    let missing = PARSERS
        .iter()
        .flat_map(|(file, functions)| functions.iter().map(move |name| format!("{file}::{name}")))
        .filter(|name| !found.contains_key(name))
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty(),
        "the attribute parsers moved; update PARSERS: {missing:?}"
    );
    let recognized = found.values().flatten().cloned().collect::<BTreeSet<_>>();
    let covered = Attribute::ALL
        .iter()
        .flat_map(|attribute| attribute.keys().iter().copied())
        .chain(BASE_KEYS.iter().flat_map(|(_, keys)| keys.iter().copied()))
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    let uncovered = recognized.difference(&covered).collect::<Vec<_>>();
    assert!(
        uncovered.is_empty(),
        "keys a sentence's attribute parser recognizes that no attribute of the axis writes: {uncovered:?}"
    );
    let stale = covered.difference(&recognized).collect::<Vec<_>>();
    assert!(
        stale.is_empty(),
        "keys the axis writes that no parser recognizes: {stale:?}"
    );
}

#[test]
fn every_attribute_macro_is_a_sentence_marker_a_helper_or_a_declaration() {
    use krs_syntax::surface::AttributeMacro;
    let named = SENTENCE_MACROS
        .iter()
        .chain(DECLARATION_MACROS.iter())
        .copied()
        .collect::<BTreeSet<_>>();
    let entries = AttributeMacro::ALL
        .iter()
        .map(|entry| entry.name())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        entries, named,
        "every attribute macro of krs-macros is a sentence's marker or helper, or a declaration's"
    );
    let cases = class_matrix::cases();
    let written = cases
        .iter()
        .filter(|case| case.family == Family::Attributes)
        .flat_map(|case| {
            case.item()
                .match_indices("#[k::")
                .map(|(at, open)| {
                    let rest = &case.item()[at + open.len()..];
                    rest[..rest.find(['(', ']']).unwrap_or(rest.len())].to_owned()
                })
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    for name in SENTENCE_MACROS {
        assert!(
            written.contains(name),
            "no attribute case writes #[k::{name}]"
        );
    }
}

/// What a pair writes.
const fn text(written: Written) -> &'static str {
    match written {
        Written::Key(text) | Written::Modality(text) | Written::Helper(text) => text,
    }
}

#[test]
fn every_term_slot_form_has_an_attribute_form_and_every_pair_a_case() {
    let cases = class_matrix::cases();
    let term_forms = cases
        .iter()
        .filter(|case| case.family == Family::Terms)
        .filter_map(|case| case.id.split('/').nth(1))
        .collect::<BTreeSet<_>>();
    let forms = FORMS.iter().map(|form| form.name).collect::<BTreeSet<_>>();
    assert_eq!(
        term_forms, forms,
        "each term slot form is an attribute form"
    );
    let attribute_cases = cases
        .iter()
        .filter(|case| case.family == Family::Attributes)
        .collect::<Vec<_>>();
    assert_eq!(
        attribute_cases.len(),
        FORMS.len() * Attribute::ALL.len() + MALFORMED.len()
    );
    assert_eq!(attribute_cases.len(), pairs().len());
    for case in &attribute_cases {
        let pair = case.attribute.expect("an attribute case carries its pair");
        let written = text(pair.written());
        assert_eq!(case.id, format!("attrs/{}/{written}", pair.form().name));
        assert!(case.oracle().is_some(), "{}: the oracle judges it", case.id);
        let rendered = case.render();
        let placed = &rendered.cases[0];
        assert_eq!(
            &rendered.source[placed.spelling.clone()],
            written.replace("TAG", &case.tag()),
            "{}: the spelling is the attribute",
            case.id
        );
    }
}

#[test]
fn an_attribute_cases_priorities_lie_after_the_driver_rules_and_apart_from_them() {
    assert_eq!(
        Attribute::Priority.text(),
        format!("priority = {CASE_PRIORITY}")
    );
    // The driver rules of the terms base, which set a run's cells up and apply the equation
    // forms' functions, are its only sentences with a priority.
    let base = Base::Terms.preamble();
    let priorities = base
        .match_indices("priority = ")
        .map(|(at, key)| {
            let rest = &base[at + key.len()..];
            rest[..rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len())]
                .parse::<u32>()
                .expect("a priority is an integer")
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(priorities, BTreeSet::from([DRIVER_PRIORITY]));
    for priority in [
        CASE_PRIORITY,
        PRIORITY_SIBLING_PRIORITY,
        OWISE_SIBLING_PRIORITY,
    ] {
        assert!(
            priority > DRIVER_PRIORITY,
            "a case's or a sibling's priority, {priority}, lies after the drivers'"
        );
    }
    // The default priority is 50, `owise`'s 200.
    const {
        assert!(CASE_PRIORITY < PRIORITY_SIBLING_PRIORITY && PRIORITY_SIBLING_PRIORITY < 50);
        assert!(OWISE_SIBLING_PRIORITY > 50 && OWISE_SIBLING_PRIORITY < 200);
    }
    // No case names a driver command: its sentences match only its own command, which no
    // driver rule matches.
    for case in class_matrix::cases()
        .iter()
        .filter(|case| case.family == Family::Attributes)
    {
        for driver in [
            "Then",
            "SetEnv",
            "SetStack",
            "SetSeq",
            "AddMember",
            "AddToken",
            "AddRow",
            "Call",
            "SizeOf",
        ] {
            assert!(
                !case.item().contains(&format!("Cmd::{driver}(")),
                "{}: names the driver command {driver}",
                case.id
            );
        }
        if case.oracle() == Some(Outcome::Accept) && case.item().contains("priority = ") {
            let command = case
                .command()
                .expect("a case with a priority has a command");
            assert!(
                case.item().contains(&format!("Cmd::{}(", command.name)),
                "{}: an accepted case with a priority matches its own command",
                case.id
            );
        }
    }
}

/// What K7 shows of each accepted attribute a form's driver can run: the case's run, and the
/// counter run where the attribute keeps the sentence from applying.
#[test]
fn k7_shows_what_each_accepted_attribute_does() {
    let cases = class_matrix::cases();
    let mut shown = BTreeMap::<String, Vec<String>>::new();
    for case in cases
        .iter()
        .filter(|case| case.family == Family::Attributes)
    {
        let Some(Pair::Attribute(form, attribute)) = case.attribute else {
            continue;
        };
        if case.oracle() != Some(Outcome::Accept) {
            continue;
        }
        let K7::Run(run) = &case.k7 else {
            continue;
        };
        let counter = case
            .k7_counter
            .as_ref()
            .map_or_else(String::new, |counter| {
                format!(" | counter {} {}", counter.steps, counter.program)
            });
        shown
            .entry(format!("{attribute:?}"))
            .or_default()
            .push(format!(
                "{}: {} {}{counter}",
                form.name,
                run.steps,
                run.status.name()
            ));
    }
    let forms = |attribute: &str| {
        let mut forms = shown[attribute]
            .iter()
            .map(|entry| entry.split(':').next().unwrap_or_default().to_owned())
            .collect::<Vec<_>>();
        forms.sort();
        forms
    };
    // A condition that does not hold, and `symbolic` on concrete values, leave the sentence
    // unapplied: no step of the case's (an equation's call takes its own).
    for attribute in ["RequiresFails", "Symbolic"] {
        for entry in &shown[attribute] {
            assert!(
                entry.contains(": 0 ")
                    || entry.starts_with("equation")
                    || entry.starts_with("table"),
                "{attribute}: {entry}"
            );
        }
    }
    // `owise`, `heat` and `cool` have a counter run; `priority` runs where both sentences match.
    for attribute in ["Owise", "Heat", "Cool"] {
        assert!(
            shown[attribute]
                .iter()
                .all(|entry| entry.contains(" | counter ")),
            "{attribute}: {:?}",
            shown[attribute]
        );
    }
    assert!(shown["Priority"].iter().all(|entry| !entry.contains(" | ")));
    let transitions = [
        "cells",
        "cells-local",
        "local-rule",
        "readable",
        "rule",
        "sort-rule",
    ];
    let with_equations = [
        "cells",
        "cells-local",
        "equation",
        "local-rule",
        "readable",
        "rule",
        "sort-rule",
        "table",
    ];
    assert_eq!(forms("Owise"), with_equations);
    assert_eq!(forms("Priority"), with_equations);
    assert_eq!(forms("Heat"), transitions);
    assert_eq!(forms("Cool"), transitions);
    assert_eq!(forms("RequiresFails").len(), 9);
    assert_eq!(
        forms("Label"),
        [
            "cells",
            "cells-local",
            "context",
            "equation",
            "local-rule",
            "readable",
            "rule",
            "sort-rule",
            "table"
        ]
    );
    assert_eq!(forms("Anywhere"), ["local-rule", "rule", "sort-rule"]);
}

/// A class whose code's registry summary advises a form names an advised case: the registry's
/// own text is advice the full tier's messages may not show (`class_matrix::advice`).
#[test]
fn a_class_whose_registry_summary_advises_names_an_advised_case() {
    use krs_test_support::class_matrix::advice::advised_in_message;
    use krs_test_support::class_matrix::table::Table;
    let read = |file: &str| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/class-matrix")
            .join(file);
        std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
    };
    let table = Table::parse(&read("expected.toml")).unwrap_or_else(|errors| panic!("{errors:#?}"));
    let unadvised = table
        .classes
        .iter()
        .filter_map(|(name, class)| {
            let summary = krs_diagnostic::codes::info(&class.code)?.summary;
            let form = advised_in_message(summary)?;
            class
                .advice
                .is_none()
                .then(|| format!("{name} ({}: `{form}`)", class.code))
        })
        .collect::<Vec<_>>();
    assert!(
        unadvised.is_empty(),
        "classes whose code's summary advises a form and that name no advised case: {unadvised:?}"
    );
}

#[test]
#[ignore = "prints the form each message of a file advises, one message a line"]
fn advice_detector_over_messages() {
    use krs_test_support::class_matrix::advice::advised_in_message;
    let path = std::env::var("ADVICE_MESSAGES").expect("ADVICE_MESSAGES names a file");
    for line in std::fs::read_to_string(path)
        .expect("the file is read")
        .lines()
    {
        println!("{}\t{line}", advised_in_message(line).unwrap_or("-"));
    }
}

#[test]
#[ignore = "prints the (attribute, form) table the oracle states"]
fn print_the_attribute_table() {
    use krs_test_support::class_matrix::attributes::expected;
    let mut line = String::from("attribute");
    for form in FORMS {
        line.push('\t');
        line.push_str(form.name);
    }
    println!("{line}");
    for attribute in Attribute::ALL {
        let mut line = attribute.text().to_owned();
        for form in FORMS {
            line.push('\t');
            line.push_str(match expected(form.sentence, attribute) {
                Outcome::Accept => "accept",
                Outcome::Refuse(refusal) => refusal.class.name(),
            });
        }
        println!("{line}");
    }
}
