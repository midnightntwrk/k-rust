//! Stable-identity adversaries for every symbol-bearing readable IMP construct.

use k::KResult;
use k::builtin::{Id, Int, KSequence, Map, map};

#[allow(dead_code)]
mod baseline {
    use super::*;

    k::sorts! {
        #[k::bracket("(", ")")]
        Expr;
        impl Expr for Id;

        Value: Expr + KResult;
        impl Value for Int;
    }

    #[k::constructors(sort = Expr, result = KResult)]
    #[k::precedence((Wrap) > left pair (Pair) > (Ready))]
    #[rustfmt::skip]
    pub enum Op {
        #[k::syntax("wrap {value}")] #[k::strict]
        Wrap { value: Expr },
        #[k::syntax("{lhs} pair {rhs}")] #[k::seqstrict]
        Pair { lhs: Expr, rhs: Expr },
        #[k::syntax("ready")]
        Ready(),
    }

    #[k::configuration]
    pub struct Machine {
        #[k::cell]
        pub k: KSequence,
        #[k::cell]
        pub env: Map<Id, Value>,
    }

    impl Machine {
        #[k::init]
        pub fn init(pgm: Expr, env: Map<Id, Value>) -> Self {
            Self { k: k![pgm], env }
        }
    }

    k::rules! {
        for Expr;
        use Op::*;

        fold:   Wrap { value } => value where value: Value;
        splice: Pair(lhs, rhs) => k![lhs, rhs];
        erase:  Ready() => ();
    }

    k::rules! {
        for Machine;
        use Op::Pair;

        lookup: {
            k: [name, ..],
            env: { name -> value, .. },
        } => {
            k: [value, ..],
        }
        where name: Id;

        assign: {
            k: [Pair(name, value), ..],
            env: state,
        } => {
            k: [..],
            env: map::update(state, name, value),
        }
        where name: Id, value: Value;
    }
}

// Same declarations, intentionally moved and reformatted. Variant and rule
// order are non-semantic; every generated stable ID must match `baseline`.
#[allow(dead_code)]
mod reordered {
    use super::*;

    #[k::configuration]
    pub struct Machine {
        #[k::cell]
        pub k: KSequence,

        #[k::cell]
        pub env: Map<Id, Value>,
    }

    impl Machine {
        #[k::init]
        pub fn init(
            pgm: Expr,
            env: Map<Id, Value>,
        ) -> Self {
            Self {
                k: k![pgm],
                env,
            }
        }
    }

    k::rules! {
        for Machine;
        use Op::Pair;

        assign: {
            env: state,
            k: [Pair(name, value), ..],
        } => {
            env: map::update(state, name, value),
            k: [..],
        }
        where name: Id, value: Value;

        lookup: {
            env: { name -> value, .. },
            k: [name, ..],
        } => {
            k: [value, ..],
        }
        where name: Id;
    }

    #[k::constructors(sort = Expr, result = KResult)]
    #[k::precedence((Wrap) > left pair (Pair) > (Ready))]
    #[rustfmt::skip]
    pub enum Op {
        #[k::syntax("ready")]
        Ready(),
        #[k::syntax("{lhs} pair {rhs}")] #[k::seqstrict]
        Pair { lhs: Expr, rhs: Expr },
        #[k::syntax("wrap {value}")] #[k::strict]
        Wrap { value: Expr },
    }

    k::sorts! {
        Value: Expr + KResult;
        impl Value for Int;

        #[k::bracket("(", ")")]
        Expr;
        impl Expr for Id;
    }

    k::rules! {
        for Expr;
        use Op::*;

        erase: Ready() => ();
        splice: Pair(lhs, rhs) => k![lhs, rhs];
        fold: Wrap { value } => value
            where value: Value;
    }
}

// A semantic rename must change the affected public IDs rather than retaining
// a stale span-derived identity. The test below freezes the exact old/new map.
#[allow(dead_code)]
mod renamed {
    use super::*;

    k::sorts! {
        #[k::bracket("(", ")")]
        Expression;
        impl Expression for Id;

        Evaluated: Expression + KResult;
        impl Evaluated for Int;
    }

    #[k::constructors(sort = Expression, result = KResult)]
    #[k::precedence((Boxed) > left joined (Joined) > (Finished))]
    #[rustfmt::skip]
    pub enum Operator {
        #[k::syntax("wrap {value}")] #[k::strict]
        Boxed { value: Expression },
        #[k::syntax("{lhs} pair {rhs}")] #[k::seqstrict]
        Joined { lhs: Expression, rhs: Expression },
        #[k::syntax("ready")]
        Finished(),
    }

    #[k::configuration]
    pub struct State {
        #[k::cell]
        pub k: KSequence,
        #[k::cell]
        pub env: Map<Id, Evaluated>,
    }

    impl State {
        #[k::init]
        pub fn init(pgm: Expression, env: Map<Id, Evaluated>) -> Self {
            Self { k: k![pgm], env }
        }
    }

    k::rules! {
        for Expression;
        use Operator::*;

        simplify: Boxed { value } => value where value: Evaluated;
        continue_with: Joined(lhs, rhs) => k![lhs, rhs];
        finish: Finished() => ();
    }

    k::rules! {
        for State;
        use Operator::Joined;

        load: {
            k: [name, ..],
            env: { name -> value, .. },
        } => {
            k: [value, ..],
        }
        where name: Id;

        store: {
            k: [Joined(name, value), ..],
            env: state,
        } => {
            k: [..],
            env: map::update(state, name, value),
        }
        where name: Id, value: Evaluated;
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Identity {
    kind: String,
    name: String,
    disambiguator: String,
}

fn identity(kind: &str, name: &str, disambiguator: &str) -> Identity {
    Identity {
        kind: kind.to_owned(),
        name: name.to_owned(),
        disambiguator: disambiguator.to_owned(),
    }
}

fn identities(module: &str) -> Vec<Identity> {
    // These fixtures must coexist in one test binary, so their full host IDs
    // necessarily differ in the final `module_path!()` segment. Project only
    // that deliberate sandbox boundary and compare the complete remaining
    // `(kind, item_name, disambiguator)` identity. The existing stable-name
    // move fixtures separately freeze module-path sensitivity and pinning.
    let mut identities = k::host_descriptors()
        .filter(|descriptor| {
            descriptor
                .id
                .rust_module_path()
                .last()
                .is_some_and(|segment| segment == module)
        })
        .map(|descriptor| Identity {
            kind: serde_json::to_value(descriptor.id.item_kind())
                .unwrap()
                .as_str()
                .unwrap()
                .to_owned(),
            name: descriptor.id.item_name().to_owned(),
            disambiguator: descriptor.id.disambiguator().to_owned(),
        })
        .collect::<Vec<_>>();
    identities.sort();
    identities
}

fn baseline_descriptor(name: &str) -> k::HostDescriptor {
    k::host_descriptors()
        .find(|descriptor| {
            descriptor
                .id
                .rust_module_path()
                .last()
                .is_some_and(|segment| segment == "baseline")
                && descriptor.id.item_name() == name
        })
        .unwrap_or_else(|| panic!("missing baseline descriptor `{name}`"))
}

#[test]
fn identity_fixture_reaches_every_readable_payload_class() {
    let wrap = baseline_descriptor("Wrap");
    let k::HostDescriptorPayload::Constructor(wrap) = &wrap.payload else {
        panic!("Wrap did not register as a constructor")
    };
    assert_eq!(wrap.syntax.as_deref(), Some("wrap {value}"));
    assert_eq!(wrap.fields.len(), 1);

    let wrap_grammar = baseline_descriptor("__krs_grammar_Op_Wrap");
    let k::HostDescriptorPayload::Grammar(wrap_grammar) = &wrap_grammar.payload else {
        panic!("Wrap grammar did not register")
    };
    let k::HostGrammarDescriptor::Production(wrap_grammar) = wrap_grammar.as_ref() else {
        panic!("Wrap grammar was not a production")
    };
    assert!(wrap_grammar.template_key.is_some());
    assert!(wrap_grammar.attributes.iter().any(|attribute| matches!(
        attribute,
        k::HostProductionAttribute::Strictness { .. }
    )));

    assert!(matches!(
        baseline_descriptor("__krs_grammar_Op_precedence").payload,
        k::HostDescriptorPayload::Grammar(grammar)
            if matches!(grammar.as_ref(), k::HostGrammarDescriptor::Precedence { .. })
    ));
    assert!(matches!(
        baseline_descriptor("__krs_grammar_Op_associativity").payload,
        k::HostDescriptorPayload::Grammar(grammar)
            if matches!(grammar.as_ref(), k::HostGrammarDescriptor::Associativity { .. })
    ));
    assert!(matches!(
        baseline_descriptor("__krs_grammar_bracket_Expr_0").payload,
        k::HostDescriptorPayload::Grammar(grammar)
            if matches!(grammar.as_ref(), k::HostGrammarDescriptor::Production(_))
    ));

    let machine = baseline_descriptor("Machine");
    machine.validate_v7_ownership().unwrap();
    let k::HostDescriptorPayload::FixedConfiguration(machine) = machine.payload else {
        panic!("Machine did not register as a fixed configuration")
    };
    assert_eq!(machine.declaration.fields.len(), 2);
    assert_eq!(machine.initializer.variables.len(), 2);
    assert_eq!(machine.initializer.cells.len(), 2);

    let fold = baseline_descriptor("fold");
    let k::HostDescriptorPayload::HeadRule(fold) = fold.payload else {
        panic!("fold did not register as a head rule")
    };
    assert!(fold.head_sort.is_some());
    assert!(fold.configuration.is_none());
    assert!(fold.bindings.iter().any(|binding| {
        binding.name == "value" && binding.refinement.is_some()
    }));
    assert!(matches!(fold.result, k::HostHeadRuleResult::Replace(_)));

    let splice = baseline_descriptor("splice");
    assert!(matches!(
        splice.payload,
        k::HostDescriptorPayload::HeadRule(rule)
            if matches!(rule.result, k::HostHeadRuleResult::Splice(ref items) if items.len() == 2)
    ));
    let erase = baseline_descriptor("erase");
    assert!(matches!(
        erase.payload,
        k::HostDescriptorPayload::HeadRule(rule)
            if matches!(rule.result, k::HostHeadRuleResult::Erase)
    ));
    let lookup = baseline_descriptor("lookup");
    assert!(matches!(
        lookup.payload,
        k::HostDescriptorPayload::HeadRule(rule)
            if rule.configuration.is_some()
                && rule.computation_cell_name.as_deref() == Some("k")
                && matches!(rule.extras.as_slice(), [k::HostHeadRuleExtra::HaveMap { .. }])
    ));
    let assign = baseline_descriptor("assign");
    assert!(matches!(
        assign.payload,
        k::HostDescriptorPayload::HeadRule(rule)
            if rule.configuration.is_some()
                && matches!(rule.extras.as_slice(), [k::HostHeadRuleExtra::UpdateMap { .. }])
    ));
}

#[test]
fn readable_identities_ignore_layout_and_unrelated_declaration_order() {
    let baseline = identities("baseline");
    let reordered = identities("reordered");
    assert_eq!(baseline, reordered);
    let mut expected = vec![
        identity("configuration", "Machine", ""),
        identity("constructor", "Pair", "enum:Op"),
        identity("constructor", "Ready", "enum:Op"),
        identity("constructor", "Wrap", "enum:Op"),
        identity("grammar", "__krs_grammar_Op_Pair", "enum:Op"),
        identity("grammar", "__krs_grammar_Op_Ready", "enum:Op"),
        identity("grammar", "__krs_grammar_Op_Wrap", "enum:Op"),
        identity(
            "grammar",
            "__krs_grammar_Op_associativity",
            "enum-associativity:Op",
        ),
        identity(
            "grammar",
            "__krs_grammar_Op_precedence",
            "enum-precedence:Op",
        ),
        identity("grammar", "__krs_grammar_bracket_Expr_0", "bracket:0"),
        identity(
            "grammar",
            "__krs_grammar_subsort(member=relative:Id;supersort=relative:Expr)",
            "subsort",
        ),
        identity(
            "grammar",
            "__krs_grammar_subsort(member=relative:Int;supersort=relative:Value)",
            "subsort",
        ),
        identity("rule", "assign", ""),
        identity("rule", "erase", ""),
        identity("rule", "fold", ""),
        identity("rule", "lookup", ""),
        identity("rule", "splice", ""),
        identity("sort", "Expr", ""),
        identity("sort", "Value", ""),
    ];
    expected.sort();
    assert_eq!(baseline, expected);
}

#[test]
#[allow(clippy::too_many_lines)] // One reviewed old/new map freezes the complete ID catalog.
fn readable_semantic_renames_change_the_exact_affected_identities() {
    let baseline = identities("baseline");
    let renamed = identities("renamed");
    assert_eq!(baseline.len(), renamed.len());
    assert_ne!(baseline, renamed);

    for (old, new) in [
        (("sort", "Expr", ""), ("sort", "Expression", "")),
        (("sort", "Value", ""), ("sort", "Evaluated", "")),
        (
            ("grammar", "__krs_grammar_bracket_Expr_0", "bracket:0"),
            ("grammar", "__krs_grammar_bracket_Expression_0", "bracket:0"),
        ),
        (
            (
                "grammar",
                "__krs_grammar_subsort(member=relative:Id;supersort=relative:Expr)",
                "subsort",
            ),
            (
                "grammar",
                "__krs_grammar_subsort(member=relative:Id;supersort=relative:Expression)",
                "subsort",
            ),
        ),
        (
            (
                "grammar",
                "__krs_grammar_subsort(member=relative:Int;supersort=relative:Value)",
                "subsort",
            ),
            (
                "grammar",
                "__krs_grammar_subsort(member=relative:Int;supersort=relative:Evaluated)",
                "subsort",
            ),
        ),
        (
            ("constructor", "Wrap", "enum:Op"),
            ("constructor", "Boxed", "enum:Operator"),
        ),
        (
            ("constructor", "Pair", "enum:Op"),
            ("constructor", "Joined", "enum:Operator"),
        ),
        (
            ("constructor", "Ready", "enum:Op"),
            ("constructor", "Finished", "enum:Operator"),
        ),
        (
            ("grammar", "__krs_grammar_Op_Wrap", "enum:Op"),
            (
                "grammar",
                "__krs_grammar_Operator_Boxed",
                "enum:Operator",
            ),
        ),
        (
            ("grammar", "__krs_grammar_Op_Pair", "enum:Op"),
            (
                "grammar",
                "__krs_grammar_Operator_Joined",
                "enum:Operator",
            ),
        ),
        (
            ("grammar", "__krs_grammar_Op_Ready", "enum:Op"),
            (
                "grammar",
                "__krs_grammar_Operator_Finished",
                "enum:Operator",
            ),
        ),
        (
            (
                "grammar",
                "__krs_grammar_Op_precedence",
                "enum-precedence:Op",
            ),
            (
                "grammar",
                "__krs_grammar_Operator_precedence",
                "enum-precedence:Operator",
            ),
        ),
        (
            (
                "grammar",
                "__krs_grammar_Op_associativity",
                "enum-associativity:Op",
            ),
            (
                "grammar",
                "__krs_grammar_Operator_associativity",
                "enum-associativity:Operator",
            ),
        ),
        (("configuration", "Machine", ""), ("configuration", "State", "")),
        (("rule", "fold", ""), ("rule", "simplify", "")),
        (("rule", "splice", ""), ("rule", "continue_with", "")),
        (("rule", "erase", ""), ("rule", "finish", "")),
        (("rule", "lookup", ""), ("rule", "load", "")),
        (("rule", "assign", ""), ("rule", "store", "")),
    ] {
        let old = identity(old.0, old.1, old.2);
        let new = identity(new.0, new.1, new.2);
        assert!(baseline.contains(&old), "missing old identity {old:?}");
        assert!(!renamed.contains(&old), "rename retained stale identity {old:?}");
        assert!(renamed.contains(&new), "missing renamed identity {new:?}");
    }
}
