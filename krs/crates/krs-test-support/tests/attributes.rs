//! The attribute axis (K8, `class_matrix::attributes`): the attribute list read from the
//! product's parsers, every attribute on every form, and the priorities K7's runs rely on.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use krs_test_support::class_matrix::attributes::{
    Attribute, BASE_KEYS, CASE_PRIORITY, DECLARATION_MACROS, DRIVER_PRIORITY, EXTRAS, FORMS,
    LATE_CASE_PRIORITY, MALFORMED, OWISE_SIBLING_PRIORITY, PRIORITY_SIBLING_PRIORITY, Pair,
    SENTENCE_MACROS, Written, pairs,
};
use krs_test_support::class_matrix::k7::K7;
use krs_test_support::class_matrix::oracle::Outcome;
use krs_test_support::class_matrix::{self, Base, Family};
use syn::visit::Visit;

/// The directory of the product's attribute parsers, `krs-syntax/src/attribute/`, every file of
/// which the key scan reads.
fn attribute_parsers() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../krs-syntax/src/attribute")
}

/// The functions of the attribute parsers whose compared literals are a declaration's keys, not
/// a sentence's, by `file::function` (`Type::function` for a method), with the declaration: the
/// key scan reads every other function's literals as a sentence's keys. A function the scan
/// finds that compares literals and is in neither the axis's keys nor this list fails it.
const DECLARATION_PARSERS: [(&str, &str); 16] = [
    (
        "constructor.rs::ConstructorKey::parse",
        "a constructor's keys",
    ),
    (
        "constructor.rs::ProductionColors::parse",
        "a production's colors",
    ),
    (
        "constructor.rs::VariantSyntaxKey::parse",
        "a variant's syntax keys",
    ),
    (
        "constructor.rs::parse_constructor_stream",
        "#[k::constructor]",
    ),
    (
        "constructor.rs::parse_constructors_stream",
        "#[k::constructors]",
    ),
    (
        "constructor.rs::parse_function_keys",
        "#[k::function], a function shorthand's marker included",
    ),
    (
        "constructor.rs::parse_function_smt",
        "a function's solver keys",
    ),
    (
        "constructor.rs::parse_variant_syntax_stream",
        "a variant's syntax",
    ),
    ("constructor.rs::placement_flag", "a production's placement"),
    (
        "constructor.rs::preference_conflict",
        "a production's preference",
    ),
    ("sort.rs::parse_sort_stream", "#[k::sort]"),
    ("sort.rs::parse_subsort_stream", "#[k::subsort]"),
    (
        "spec_module.rs::parse_attribute_stream",
        "#[k::spec_module]",
    ),
    ("state.rs::parse_cell_stream", "#[k::cell]"),
    (
        "state.rs::parse_configuration_stream",
        "#[k::configuration]",
    ),
    ("state.rs::validate_multiplicity", "a cell's multiplicity"),
];

/// The string literals a parser compares a key with: a match arm's pattern, an operand of `==`
/// or `!=`, a pattern of `matches!`, each directly or through a `&str` constant of the file.
struct Keys<'c> {
    constants: &'c BTreeMap<String, String>,
    found: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for Keys<'_> {
    fn visit_arm(&mut self, arm: &'ast syn::Arm) {
        Patterns(self.constants, &mut self.found).visit_pat(&arm.pat);
        syn::visit::visit_arm(self, arm);
    }

    fn visit_expr_binary(&mut self, binary: &'ast syn::ExprBinary) {
        if matches!(binary.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_)) {
            for side in [&*binary.left, &*binary.right] {
                let side = match side {
                    syn::Expr::Reference(reference) => &*reference.expr,
                    side => side,
                };
                match side {
                    syn::Expr::Lit(syn::ExprLit {
                        lit: syn::Lit::Str(literal),
                        ..
                    }) => {
                        self.found.insert(literal.value());
                    }
                    syn::Expr::Path(path) => {
                        if let Some(value) = path
                            .path
                            .get_ident()
                            .and_then(|ident| self.constants.get(&ident.to_string()))
                        {
                            self.found.insert(value.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        syn::visit::visit_expr_binary(self, binary);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if mac.path.is_ident("matches") {
            let parsed = mac.parse_body_with(|input: syn::parse::ParseStream<'_>| {
                input.parse::<syn::Expr>()?;
                input.parse::<syn::Token![,]>()?;
                syn::Pat::parse_multi_with_leading_vert(input)
            });
            if let Ok(pattern) = parsed {
                Patterns(self.constants, &mut self.found).visit_pat(&pattern);
            }
        }
        syn::visit::visit_macro(self, mac);
    }
}

/// The string literals of a pattern, and the values of the `&str` constants it names.
struct Patterns<'a>(&'a BTreeMap<String, String>, &'a mut BTreeSet<String>);

impl<'ast> Visit<'ast> for Patterns<'_> {
    fn visit_pat(&mut self, pattern: &'ast syn::Pat) {
        match pattern {
            syn::Pat::Lit(syn::ExprLit {
                lit: syn::Lit::Str(literal),
                ..
            }) => {
                self.1.insert(literal.value());
            }
            syn::Pat::Path(path) => {
                if let Some(value) = path
                    .path
                    .get_ident()
                    .and_then(|ident| self.0.get(&ident.to_string()))
                {
                    self.1.insert(value.clone());
                }
            }
            _ => {}
        }
        syn::visit::visit_pat(self, pattern);
    }
}

/// The `&str` constants of a file, by name.
fn constants(file: &syn::File) -> BTreeMap<String, String> {
    #[derive(Default)]
    struct Constants(BTreeMap<String, String>);
    impl<'ast> Visit<'ast> for Constants {
        fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
            if let syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Str(literal),
                ..
            }) = &*item.expr
            {
                self.0.insert(item.ident.to_string(), literal.value());
            }
        }
    }
    let mut found = Constants::default();
    found.visit_file(file);
    found.0
}

/// Every function of the Rust files under `directory`, by `file::function`
/// (`file::Type::function` for a method), with the literals it compares a key with.
fn compared_literals(directory: &Path) -> BTreeMap<String, BTreeSet<String>> {
    let mut found = BTreeMap::new();
    let mut files = std::fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("{}: {error}", directory.display()))
        .map(|entry| entry.expect("a directory entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "rs"))
        .collect::<Vec<_>>();
    files.sort();
    for path in files {
        let file = path
            .file_name()
            .and_then(|name| name.to_str())
            .expect("a file name")
            .to_owned();
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        let parsed = syn::parse_file(&text).unwrap_or_else(|error| panic!("{file}: {error}"));
        let constants = constants(&parsed);
        let mut take = |name: String, block: &syn::Block| {
            let mut keys = Keys {
                constants: &constants,
                found: BTreeSet::new(),
            };
            keys.visit_block(block);
            if !keys.found.is_empty() {
                found.insert(format!("{file}::{name}"), keys.found);
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
#[ignore = "prints every function of the attribute parsers and the literals it compares"]
fn print_the_attribute_parsers_literals() {
    for (function, literals) in compared_literals(&attribute_parsers()) {
        println!("{function}\t{literals:?}");
    }
}

#[test]
fn every_key_the_attribute_parsers_recognize_is_an_attribute_of_the_axis() {
    let found = compared_literals(&attribute_parsers());
    let stale = DECLARATION_PARSERS
        .iter()
        .filter(|(function, _)| !found.contains_key(*function))
        .collect::<Vec<_>>();
    assert!(
        stale.is_empty(),
        "declaration parsers the scan no longer finds comparing literals: {stale:?}"
    );
    let recognized = found
        .iter()
        .filter(|(function, _)| {
            !DECLARATION_PARSERS
                .iter()
                .any(|(declaration, _)| declaration == function)
        })
        .flat_map(|(function, keys)| {
            keys.iter()
                .map(move |key| (key.as_str(), function.as_str()))
        })
        .collect::<BTreeMap<_, _>>();
    let covered = Attribute::ALL
        .iter()
        .flat_map(|attribute| attribute.keys().iter().copied())
        .chain(BASE_KEYS.iter().flat_map(|(_, keys)| keys.iter().copied()))
        .chain(PRODUCTION_KEYS)
        .collect::<BTreeSet<_>>();
    let uncovered = recognized
        .iter()
        .filter(|(key, _)| !covered.contains(*key))
        .collect::<Vec<_>>();
    assert!(
        uncovered.is_empty(),
        "keys a sentence's attribute parser recognizes that no attribute of the axis writes, with a function that compares each: {uncovered:?}"
    );
    let stale = covered
        .iter()
        .filter(|key| !recognized.contains_key(*key))
        .collect::<Vec<_>>();
    assert!(
        stale.is_empty(),
        "keys the axis writes that no parser recognizes: {stale:?}"
    );
}

/// The keys of a static production's own marker the axis writes ([`EXTRAS`]).
const PRODUCTION_KEYS: [&str; 1] = ["recursive"];

/// The attribute names the function-like clause macros (`k::rules!`, `k::claims!`,
/// `k::equations!`) recognize on a clause, read from their takers in `krs-syntax/src/rule/`: a
/// literal compared with an attribute path's name, or an `AttributeMacro` variant matched.
fn clause_attribute_names() -> BTreeSet<String> {
    const TAKERS: [(&str, &str); 3] = [
        ("block.rs", "take_rule_clause_attribute"),
        ("block.rs", "take_claim_clause_attribute"),
        ("equation_table.rs", "row_attributes"),
    ];
    #[derive(Default)]
    struct Variants(BTreeSet<String>);
    impl<'ast> Visit<'ast> for Variants {
        fn visit_path(&mut self, path: &'ast syn::Path) {
            let segments = path.segments.iter().collect::<Vec<_>>();
            if let [.., owner, variant] = segments.as_slice()
                && owner.ident == "AttributeMacro"
            {
                let mut name = String::new();
                for (at, character) in variant.ident.to_string().char_indices() {
                    if character.is_uppercase() && at > 0 {
                        name.push('_');
                    }
                    name.push(character.to_ascii_lowercase());
                }
                self.0.insert(name);
            }
            syn::visit::visit_path(self, path);
        }
    }
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../krs-syntax/src/rule");
    let found = compared_literals(&directory);
    let mut names = BTreeSet::new();
    for (file, function) in TAKERS {
        if let Some(literals) = found.get(&format!("{file}::{function}")) {
            names.extend(literals.iter().cloned());
        }
        let text = std::fs::read_to_string(directory.join(file)).expect("the taker's file");
        let parsed = syn::parse_file(&text).expect("the taker's file parses");
        let taker = parsed
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(item) if item.sig.ident == function => Some(item),
                _ => None,
            })
            .unwrap_or_else(|| panic!("the clause taker {file}::{function} moved"));
        let mut variants = Variants::default();
        variants.visit_block(&taker.block);
        names.extend(variants.0);
    }
    names
}

#[test]
fn every_attribute_a_clause_macro_recognizes_is_a_sentence_macro_the_axis_writes_on_a_clause() {
    let names = clause_attribute_names();
    assert!(
        names.contains("rule") && names.contains("claim") && names.contains("equation"),
        "the scan reads the clause takers: {names:?}"
    );
    let not_sentence = names
        .iter()
        .filter(|name| !SENTENCE_MACROS.contains(&name.as_str()))
        .collect::<Vec<_>>();
    assert!(
        not_sentence.is_empty(),
        "attributes a clause macro recognizes that are no sentence macro: {not_sentence:?}"
    );
    // Each is written on a clause form: a `for Sort` clause, a readable clause, a table row or a
    // `k::claims!` clause.
    let cases = class_matrix::cases();
    let clause_items = cases
        .iter()
        .filter(|case| case.family == Family::Attributes)
        .filter(|case| {
            ["sort-rule", "readable", "table", "claim"]
                .contains(&case.id.split('/').nth(1).unwrap_or_default())
        })
        .map(krs_test_support::class_matrix::Case::item)
        .collect::<Vec<_>>();
    for name in &names {
        assert!(
            clause_items
                .iter()
                .any(|item| item.contains(&format!("#[k::{name}"))),
            "no attribute case writes #[k::{name}] on a clause"
        );
    }
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
    // The sentence macros are exactly the forms' markers and the axis's helpers, and the cases
    // write each where the axis says: every case of a form with a marker writes it, and every
    // helper is written on every form.
    let markers = FORMS
        .iter()
        .map(|form| form.marker)
        .collect::<BTreeSet<_>>();
    let helpers = Attribute::ALL
        .iter()
        .filter_map(|attribute| match attribute.written() {
            Written::Helper(text) => text
                .strip_prefix("#[k::")
                .and_then(|rest| rest.split(['(', ']']).next()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    assert!(markers.is_disjoint(&helpers), "{markers:?} {helpers:?}");
    assert_eq!(
        markers.union(&helpers).copied().collect::<BTreeSet<_>>(),
        SENTENCE_MACROS.iter().copied().collect::<BTreeSet<_>>(),
        "the sentence macros are the forms' markers and the axis's helpers"
    );
    let cases = class_matrix::cases();
    let clause_forms = ["sort-rule", "readable", "table"];
    for case in cases
        .iter()
        .filter(|case| case.family == Family::Attributes)
    {
        let Some(pair) = case.attribute else {
            continue;
        };
        let form = pair.form();
        let item = case.item();
        if !clause_forms.contains(&form.name) {
            assert!(
                item.contains(&format!("#[k::{}", form.marker)),
                "{}: does not write its form's marker #[k::{}]",
                case.id,
                form.marker
            );
        }
        if let Written::Helper(text) = pair.written() {
            assert!(
                item.contains(&text.replace("TAG", &case.tag())),
                "{}",
                case.id
            );
        }
    }
    for helper in &helpers {
        for form in FORMS {
            assert!(
                cases.iter().any(|case| case.family == Family::Attributes
                    && case
                        .id
                        .starts_with(&format!("attrs/{}/#[k::{helper}", form.name))),
                "#[k::{helper}] is not written on {}",
                form.name
            );
        }
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
        FORMS.len() * Attribute::ALL.len() + MALFORMED.len() + EXTRAS.len()
    );
    assert_eq!(attribute_cases.len(), pairs().len());
    for case in &attribute_cases {
        let pair = case.attribute.expect("an attribute case carries its pair");
        assert_eq!(
            case.id,
            format!("attrs/{}/{}", pair.form().name, pair.name())
        );
        assert!(case.oracle().is_some(), "{}: the oracle judges it", case.id);
        let rendered = case.render();
        let placed = &rendered.cases[0];
        // A production's key is written on the case's command: its spelling is the clause's
        // marker.
        let spelled = match pair.written() {
            Written::Production(_) => format!("#[k::{}]", pair.form().marker),
            written => written.text().replace("TAG", &case.tag()),
        };
        assert_eq!(
            &rendered.source[placed.spelling.clone()],
            spelled,
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
        LATE_CASE_PRIORITY,
        PRIORITY_SIBLING_PRIORITY,
        OWISE_SIBLING_PRIORITY,
    ] {
        assert!(
            priority > DRIVER_PRIORITY,
            "a case's or a sibling's priority, {priority}, lies after the drivers'"
        );
    }
    assert_eq!(
        Attribute::PriorityLate.text(),
        format!("priority = {LATE_CASE_PRIORITY}")
    );
    // The default priority is 50, `owise`'s 200; the two priority cases lie on either side of
    // their sibling, so they have opposite winners.
    const {
        assert!(CASE_PRIORITY < PRIORITY_SIBLING_PRIORITY && PRIORITY_SIBLING_PRIORITY < 50);
        assert!(
            PRIORITY_SIBLING_PRIORITY < LATE_CASE_PRIORITY && LATE_CASE_PRIORITY < 50,
            "a late case's priority lies after its sibling's and before the default"
        );
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
            .k7_counters
            .first()
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
                .is_empty()
                .then(|| format!("{name} ({}: `{}`)", class.code, form.form))
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
        let form = advised_in_message(line).map(|advice| advice.form);
        println!("{}\t{line}", form.as_deref().unwrap_or("-"));
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
