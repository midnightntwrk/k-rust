use std::sync::atomic::{AtomicUsize, Ordering};

extern crate language_host as k;

use krs_macros::{constructor, rule, sort, term};
use language_host::{
    HostApplicationIdentity, HostDescriptorPayload, HostGrammarDescriptor, HostProductionAttribute,
    HostProductionItem, HostProductionOwner, HostTerm, HostTermArgument, ItemKind, ProtocolVersion,
    Term, configuration, init, k,
};

mod split_config;
mod split_init;

static RUNTIME_CELL_CONSTRUCTIONS: AtomicUsize = AtomicUsize::new(0);

mod instrumented {
    use std::marker::PhantomData;

    use super::{Ordering, RUNTIME_CELL_CONSTRUCTIONS};

    pub struct KCell<T> {
        marker: PhantomData<fn() -> T>,
    }

    impl KCell<language_host::builtin::KSequence> {
        pub fn new(_contents: language_host::builtin::KSequence) -> Self {
            RUNTIME_CELL_CONSTRUCTIONS.fetch_add(1, Ordering::SeqCst);
            Self {
                marker: PhantomData,
            }
        }
    }
}

#[sort]
pub trait KItem {}

#[sort]
#[language_host::bracket("({value})")]
pub trait Expr: KItem {}

#[sort]
pub trait KResult: KItem {}

#[sort]
pub trait Value: Expr + KResult {}

#[constructor(sort = Expr, syntax = "halt", group = "atoms")]
pub struct Halt;

#[constructor(
    sort = Expr,
    syntax = "{second} pair {first}",
    group = "pair",
    avoid = true,
    format = "%1 %2 %3"
)]
#[language_host::seqstrict(sequence = [first, second], result = KResult)]
pub struct Pair {
    pub first: Term<dyn Expr>,
    pub second: Term<dyn Expr>,
}

#[constructor(sort = Expr, syntax = "wrap({value})")]
pub struct Wrap {
    pub value: Term<dyn Expr>,
}

#[language_host::token(regex = r"[a-zA-Z][a-zA-Z0-9_]*", prec = 2)]
pub struct Identifier(pub String);

impl KItem for Identifier {}
impl Expr for Identifier {}
impl KResult for Identifier {}

#[language_host::subsort]
impl Value for Identifier {}

#[language_host::constructors(sort = Value)]
pub enum Boolean {
    #[k::syntax("true", group = "atoms")]
    True,
    #[k::syntax("false", group = "atoms")]
    False,
    #[k::syntax("tag {value}", group = "atoms", format = "%1%2")]
    Tagged { value: Term<dyn Expr> },
}

impl KItem for Boolean {}
impl Expr for Boolean {}
impl KResult for Boolean {}
impl Value for Boolean {}

use Boolean as Truth;

language_host::precedence! {
    pair > atoms;
}

language_host::associativity! {
    left: pair;
    non_associative: atoms;
}

#[configuration(root = "machine")]
pub struct Machine {
    pub k: instrumented::KCell<language_host::builtin::KSequence>,
}

impl Machine {
    #[init]
    pub fn init() -> Self {
        Self {
            k: instrumented::KCell::new(k![Halt]),
        }
    }
}

#[configuration(root = "secondary")]
pub struct Secondary {
    pub k: language_host::configuration::KCell<language_host::builtin::KSequence>,
}

impl Secondary {
    #[init]
    pub fn init(
        #[language_host::config_var(name = "PGM", main)] program: Term<dyn KItem>,
    ) -> Self {
        Self {
            k: language_host::configuration::KCell::new(k![program]),
        }
    }
}

#[rule]
pub fn native_pair(
    Pair { first, second }: Term<dyn Expr>,
) -> Term<dyn Expr> {
    Pair {
        first: second,
        second: first,
    }
}

#[rule]
pub fn macro_pair(
    term![Pair { first, second }]: Term<dyn Expr>,
) -> Term<dyn Expr> {
    term![Wrap { value: first }]
}

#[rule]
pub fn binder_gap(
    term![Pair {
        first: 日本,
        second: nested::Done,
    }]: Term<dyn Expr>,
) -> Term<dyn Expr> {
    term![nested::Keep { value: 日本, marker: nested::Done }]
}

#[rule]
pub fn enum_alias(Truth::False: Term<Boolean>) -> Term<Boolean> {
    Truth::True
}

#[rule]
pub fn enum_record(
    Truth::Tagged { value }: Term<Boolean>,
) -> Term<Boolean> {
    Truth::Tagged { value }
}

#[rule]
pub fn subject_wildcard(
    Pair {
        first: _,
        second: value,
    }: Term<dyn Expr>,
) -> Term<dyn Expr> {
    value
}

#[rule]
pub fn boolean_literal(false: Term<language_host::builtin::bool::Bool>) -> Term<language_host::builtin::bool::Bool> {
    true
}

#[rule]
pub fn builtin_application(
    term![Pair {
        first: lhs,
        second: rhs,
    }]: Term<dyn Expr>,
) -> Term<language_host::builtin::int::Int> {
    term![language_host::builtin::int::add(lhs, rhs)]
}

pub mod nested {
    use super::{Expr, Term, constructor, rule};

    #[constructor(sort = Expr, syntax = "done")]
    pub struct Done;

    #[constructor(sort = Expr)]
    pub struct Keep {
        pub value: Term<dyn Expr>,
        pub marker: Term<dyn Expr>,
    }

    #[rule]
    pub fn stay(Done: Term<dyn Expr>) -> Term<dyn Expr> {
        Done
    }
}

#[allow(dead_code)]
fn standalone_term(value: Term<dyn Expr>) -> Term<dyn Expr> {
    term![Wrap { value }]
}

fn main() {
    let _: fn(Term<dyn Expr>) -> Term<dyn Expr> = macro_pair;
    let _: fn() -> Machine = Machine::init;
    let _: fn(Term<dyn KItem>) -> Secondary = Secondary::init;
    let _: fn() -> split_config::Split = split_config::Split::init;

    let mut descriptors = language_host::host_descriptors().collect::<Vec<_>>();
    descriptors.sort_by(|left, right| left.id.cmp(&right.id));
    assert_eq!(descriptors.len(), 40);
    assert_eq!(kind_count(&descriptors, ItemKind::Sort), 6);
    assert_eq!(kind_count(&descriptors, ItemKind::Constructor), 8);
    assert_eq!(kind_count(&descriptors, ItemKind::Grammar), 14);
    assert_eq!(kind_count(&descriptors, ItemKind::Rule), 9);
    assert_eq!(
        descriptors
            .iter()
            .filter(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
            .count(),
        3
    );
    assert_eq!(ProtocolVersion::CURRENT, ProtocolVersion(6));
    assert!(
        descriptors
            .iter()
            .all(|descriptor| descriptor.protocol_version == ProtocolVersion::CURRENT)
    );
    assert!(descriptors.iter().all(|descriptor| {
        descriptor
            .provenance
            .authored()
            .iter()
            .all(|anchor| !anchor.anchor().display_file().starts_with('/'))
    }));
    assert_eq!(RUNTIME_CELL_CONSTRUCTIONS.load(Ordering::SeqCst), 0);

    let machine = descriptor(&descriptors, "Machine", ItemKind::Configuration);
    machine.validate_configuration_pairing().unwrap();
    let HostDescriptorPayload::Configuration(machine) = &machine.payload else {
        panic!("Machine must be a configuration descriptor")
    };
    assert_eq!(machine.root, "machine");
    assert_eq!(machine.cell.name, "k");
    assert_eq!(machine.cell.content_sort, language_host::BuiltinSort::KSequence);
    assert!(machine.main_variable.is_none());
    assert_eq!(machine.initializer.name, "init");
    assert_eq!(machine.initializer.term, "Halt");
    assert_eq!(machine.initializer.references.len(), 1);
    assert_eq!(
        machine.initializer.references[0].key.role(),
        "initializer_term_path"
    );
    assert_eq!(machine.initializer.references[0].key.ordinal(), 0);
    assert_eq!(
        machine.initializer.references[0].target.key.resolve(),
        std::any::TypeId::of::<Halt>()
    );
    let machine_roles = machine
        .initializer
        .provenance
        .authored()
        .iter()
        .map(|anchor| anchor.key().role())
        .collect::<Vec<_>>();
    assert!(machine_roles.contains(&"initializer_declaration"));
    assert!(machine_roles.contains(&"initializer_term_path"));

    let secondary = descriptor(&descriptors, "Secondary", ItemKind::Configuration);
    secondary.validate_configuration_pairing().unwrap();
    let HostDescriptorPayload::Configuration(secondary) = &secondary.payload else {
        panic!("Secondary must be a configuration descriptor")
    };
    let variable = secondary.main_variable.as_ref().unwrap();
    assert_eq!(variable.binding, "program");
    assert_eq!(variable.external_name, "PGM");
    assert_eq!(variable.sort.key.role(), "configuration_variable_type");
    assert_eq!(variable.sort.key.ordinal(), 0);
    assert_eq!(
        variable.sort.target.key.resolve(),
        std::any::TypeId::of::<dyn KItem>()
    );
    assert_eq!(secondary.initializer.term, "program");
    assert!(secondary.initializer.references.is_empty());

    let split = descriptor(&descriptors, "Split", ItemKind::Configuration);
    split.validate_configuration_pairing().unwrap();
    let HostDescriptorPayload::Configuration(split_payload) = &split.payload else {
        panic!("Split must be a configuration descriptor")
    };
    assert_eq!(
        split.provenance.invocation().display_file(),
        "src/split_config.rs"
    );
    assert_eq!(
        split_payload.initializer.provenance.invocation().display_file(),
        "src/split_init.rs"
    );
    assert_ne!(
        split.provenance.invocation().display_file(),
        split_payload
            .initializer
            .provenance
            .invocation()
            .display_file()
    );

    let value = descriptor(&descriptors, "Value", ItemKind::Sort);
    let HostDescriptorPayload::Sort(value) = &value.payload else {
        panic!("Value must be a sort descriptor")
    };
    assert_eq!(value.parents.len(), 2);

    let pair = descriptor(&descriptors, "Pair", ItemKind::Constructor);
    let HostDescriptorPayload::Constructor(pair) = &pair.payload else {
        panic!("Pair must be a constructor descriptor")
    };
    assert_eq!(pair.fields.len(), 2);
    assert_eq!(pair.fields[0].name, "first");
    assert_eq!(pair.fields[1].name, "second");

    let pair_grammar = descriptor(&descriptors, "__krs_grammar_Pair", ItemKind::Grammar);
    let HostDescriptorPayload::Grammar(pair_grammar) = &pair_grammar.payload else {
        panic!("Pair grammar descriptor has the wrong payload")
    };
    let HostGrammarDescriptor::Production(pair_production) = pair_grammar.as_ref() else {
        panic!("Pair grammar must be a production")
    };
    let HostProductionOwner::Constructor { constructor } = &pair_production.owner else {
        panic!("Pair production must have constructor ownership")
    };
    assert_eq!(
        constructor.target.resolve(),
        HostApplicationIdentity::Nominal(std::any::TypeId::of::<Pair>())
    );
    assert!(matches!(
        &pair_production.items[0],
        HostProductionItem::NonTerminal { field, .. } if field.as_str() == "second"
    ));
    assert!(matches!(
        &pair_production.items[2],
        HostProductionItem::NonTerminal { field, .. } if field.as_str() == "first"
    ));
    assert!(pair_production.attributes.iter().any(|attribute| matches!(
        attribute,
        HostProductionAttribute::Group { reference } if reference.group.as_str() == "pair"
    )));
    assert!(pair_production
        .attributes
        .iter()
        .any(|attribute| matches!(attribute, HostProductionAttribute::Avoid { .. })));
    assert!(pair_production.attributes.iter().any(|attribute| matches!(
        attribute,
        HostProductionAttribute::Format { fragments, .. } if fragments.len() == 5
    )));
    assert!(pair_production.attributes.iter().any(|attribute| matches!(
        attribute,
        HostProductionAttribute::Strictness { fields, .. }
            if fields.iter().map(|field| field.field.as_str()).collect::<Vec<_>>() == ["first", "second"]
    )));

    let false_constructor = descriptors
        .iter()
        .find(|descriptor| {
            descriptor.id.item_name() == "False"
                && descriptor.id.item_kind() == ItemKind::Constructor
                && descriptor.id.disambiguator() == "enum:Boolean"
        })
        .expect("False enum variant constructor is registered");
    assert_eq!(
        false_constructor
            .declared_type
            .expect("enum variants expose an exact declaration key")
            .resolve(),
        HostApplicationIdentity::EnumVariant {
            enum_type: std::any::TypeId::of::<Boolean>(),
            variant: Truth::__krs_variant_type_id_False(),
        }
    );

    let token_grammar = descriptor(
        &descriptors,
        "__krs_grammar_token_Identifier",
        ItemKind::Grammar,
    );
    let HostDescriptorPayload::Grammar(token_grammar) = &token_grammar.payload else {
        panic!("token grammar has the wrong payload")
    };
    let HostGrammarDescriptor::Production(token) = token_grammar.as_ref() else {
        panic!("token grammar must be a production")
    };
    assert!(matches!(token.owner, HostProductionOwner::TokenSort { .. }));
    assert!(matches!(
        &token.items[..],
        [HostProductionItem::RegexTerminal { regex, .. }] if regex == "[a-zA-Z][a-zA-Z0-9_]*"
    ));
    assert!(matches!(
        &token.attributes[..],
        [HostProductionAttribute::Token { lexical_precedence: Some(precedence), .. }]
            if precedence.value == 2
    ));

    assert!(descriptors.iter().any(|descriptor| {
        matches!(
            &descriptor.payload,
            HostDescriptorPayload::Grammar(grammar)
                if matches!(grammar.as_ref(), HostGrammarDescriptor::Precedence { chains, .. } if chains.len() == 1)
        )
    }));
    assert!(descriptors.iter().any(|descriptor| {
        matches!(
            &descriptor.payload,
            HostDescriptorPayload::Grammar(grammar)
                if matches!(grammar.as_ref(), HostGrammarDescriptor::Associativity { sentences, .. } if sentences.len() == 2)
        )
    }));

    let gap_descriptor = descriptor(&descriptors, "binder_gap", ItemKind::Rule);
    let HostDescriptorPayload::StructuredRule(gap_rule) = &gap_descriptor.payload else {
        panic!("binder_gap must be a structured rule descriptor")
    };
    assert_eq!(gap_rule.bindings, ["日本"]);
    let keys = gap_descriptor
        .provenance
        .authored()
        .iter()
        .map(|anchor| (anchor.key().role(), anchor.key().ordinal()))
        .collect::<Vec<_>>();
    assert!(keys.contains(&("rule_left_path", 0)));
    assert!(keys.contains(&("rule_left_path", 1)));
    assert!(keys.contains(&("rule_left_path", 2)));
    assert!(keys.contains(&("rule_right_path", 0)));
    assert!(keys.contains(&("rule_right_path", 1)));
    assert!(keys.contains(&("rule_right_path", 2)));
    assert!(keys.contains(&("rule_left_application_head", 0)));
    assert!(keys.contains(&("rule_right_application_head", 0)));

    let enum_rule = descriptor(&descriptors, "enum_alias", ItemKind::Rule);
    let HostDescriptorPayload::StructuredRule(enum_rule) = &enum_rule.payload else {
        panic!("enum_alias must be structured")
    };
    let HostTerm::Application { reference, .. } = &enum_rule.subject else {
        panic!("enum subject is a zero-argument application")
    };
    assert_eq!(
        reference.target.resolve(),
        HostApplicationIdentity::EnumVariant {
            enum_type: std::any::TypeId::of::<Boolean>(),
            variant: Truth::__krs_variant_type_id_False(),
        }
    );

    let record_rule = descriptor(&descriptors, "enum_record", ItemKind::Rule);
    let HostDescriptorPayload::StructuredRule(record_rule) = &record_rule.payload else {
        panic!("enum_record must be structured")
    };
    let HostTerm::Application { arguments, .. } = &record_rule.result else {
        panic!("enum record result must be an application")
    };
    assert!(matches!(
        &arguments[..],
        [HostTermArgument::Named { field, .. }] if field.as_str() == "value"
    ));

    let wildcard_rule = descriptor(&descriptors, "subject_wildcard", ItemKind::Rule);
    let HostDescriptorPayload::StructuredRule(wildcard_rule) = &wildcard_rule.payload else {
        panic!("subject_wildcard must be structured")
    };
    let HostTerm::Application { arguments, .. } = &wildcard_rule.subject else {
        panic!("wildcard subject must be an application")
    };
    assert!(matches!(
        &arguments[0],
        HostTermArgument::Named { value, .. } if matches!(value.as_ref(), HostTerm::Wildcard { .. })
    ));

    let literal_rule = descriptor(&descriptors, "boolean_literal", ItemKind::Rule);
    let HostDescriptorPayload::StructuredRule(literal_rule) = &literal_rule.payload else {
        panic!("boolean_literal must be structured")
    };
    assert!(matches!(literal_rule.subject, HostTerm::Literal { .. }));
    assert!(matches!(literal_rule.result, HostTerm::Literal { .. }));

    let builtin_rule = descriptor(&descriptors, "builtin_application", ItemKind::Rule);
    let HostDescriptorPayload::StructuredRule(builtin_rule) = &builtin_rule.payload else {
        panic!("builtin_application must be structured")
    };
    let HostTerm::Application { reference, .. } = &builtin_rule.result else {
        panic!("builtin result must be an application")
    };
    assert_eq!(
        reference.target.resolve(),
        HostApplicationIdentity::Nominal(std::any::TypeId::of::<
            language_host::builtin::int::add,
        >())
    );

    let nested_anchor = gap_descriptor
        .provenance
        .authored()
        .iter()
        .find(|anchor| anchor.key().role() == "rule_right_path" && anchor.key().ordinal() == 2)
        .expect("nested path anchor exists")
        .anchor();
    let source_line = include_str!("main.rs")
        .lines()
        .nth((nested_anchor.start().line() - 1) as usize)
        .expect("anchor line exists");
    let nested_byte = source_line
        .find("nested::Done")
        .expect("nested path remains on the Unicode-bearing line");
    assert_eq!(
        nested_anchor.start().scalar_column() as usize,
        source_line[..nested_byte].chars().count() + 1
    );

    for descriptor in &descriptors {
        println!(
            "{}|{}|{:?}|{}",
            descriptor.id.rust_module_path().join("::"),
            descriptor.id.item_name(),
            descriptor.id.item_kind(),
            descriptor.provenance.authored().len()
        );
    }
}

fn kind_count(descriptors: &[language_host::HostDescriptor], kind: ItemKind) -> usize {
    descriptors
        .iter()
        .filter(|descriptor| descriptor.id.item_kind() == kind)
        .count()
}

fn descriptor<'a>(
    descriptors: &'a [language_host::HostDescriptor],
    name: &str,
    kind: ItemKind,
) -> &'a language_host::HostDescriptor {
    descriptors
        .iter()
        .find(|descriptor| descriptor.id.item_name() == name && descriptor.id.item_kind() == kind)
        .unwrap_or_else(|| panic!("missing {kind:?} descriptor `{name}`"))
}
