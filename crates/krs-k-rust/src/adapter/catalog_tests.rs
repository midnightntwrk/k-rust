//! The builtin catalog against the pinned native prelude (S5).
//!
//! (1) Every catalog row names a production the prepared prelude declares, with
//! the row's hook, signature, and module. (3) One ground application of every
//! exposed operation evaluates natively; an operation that does not would be
//! left out of the catalog (exposure policy S3). The console hooks `IO.write`
//! and `IO.putc` are the exception (KF-035): k-rust performs them only in
//! committed execution with console state, which its request API does not
//! supply, so they are pinned as unevaluated here, and the `native-rust` route
//! refuses a definition that uses them (`ConsoleWriteHook`).

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    backend::{Backend as NativeBackend, BackendOptions, ExecuteRequest},
    definition::{FlatImport, FlatModule, ProductionItem, Sentence},
    kast::identifier::encode_label,
    kore::parser::parse_pattern,
};
use krs_ir::{
    BuiltinOperation, BuiltinSort, CollectionOperandSort, CollectionOperationSpec,
    CollectionResultSort, ListOperation, MapOperation, OperationSort, SetOperation,
};

use crate::{
    Backend, CompileOptions, adapt_definition, compile_loaded_definition, prepare_definition,
    test_fixtures::smoke_definition,
};

/// The impure console hooks k-rust's request API leaves unevaluated, because it
/// supplies no console state (k-rust docs/compatibility.md, "Console IO").
const CONSOLE_HOOK_LABELS: &[&str] =
    &["#write(_,_)_K-IO_K_Int_String", "#putc(_,_)_K-IO_K_Int_Int"];

/// Every builtin module the catalog's rows name, imported by the evaluation definition.
const CATALOG_MODULES: &[&str] = &[
    "BOOL",
    "BYTES",
    "COLLECTIONS",
    "FLOAT",
    "INT",
    "K-EQUAL",
    "K-IO",
    "LIST",
    "MAP",
    "SET",
    "STRING",
];

/// A prelude production: its declaring module, hook, result sort, parameters,
/// and nonterminal sorts.
struct PreludeProduction {
    module: String,
    hook: Option<String>,
    sort: String,
    parameters: Vec<String>,
    arguments: Vec<String>,
    /// Whether the production carries `smt-hook` or `smtlib` (KF-043).
    smt: bool,
}

struct Prelude {
    productions: BTreeMap<String, PreludeProduction>,
    imports: BTreeMap<String, Vec<String>>,
}

impl Prelude {
    fn load() -> Self {
        let adapted = adapt_definition(&smoke_definition()).unwrap();
        let loaded = prepare_definition(adapted.definition, Backend::Llvm).unwrap();
        let mut productions = BTreeMap::new();
        let mut imports = BTreeMap::new();
        for module in &loaded.definition().modules {
            imports.insert(
                module.name.clone(),
                module
                    .imports
                    .iter()
                    .map(|import| import.name.clone())
                    .collect(),
            );
            collect_productions(module, &mut productions);
        }
        Self {
            productions,
            imports,
        }
    }

    /// Whether `module` is `root` or is imported by it, directly or transitively.
    fn reaches(&self, root: &str, module: &str) -> bool {
        let mut pending = vec![root.to_owned()];
        let mut visited = BTreeSet::new();
        while let Some(next) = pending.pop() {
            if next == module {
                return true;
            }
            if visited.insert(next.clone()) {
                pending.extend(self.imports.get(&next).into_iter().flatten().cloned());
            }
        }
        false
    }

    /// Requires the labelled production to exist in the catalog's module with the
    /// catalog's hook and signature.
    fn require(
        &self,
        label: &str,
        hook: Option<&str>,
        k_module: &str,
        result: &str,
        arguments: &[String],
    ) {
        let production = self
            .productions
            .get(label)
            .unwrap_or_else(|| panic!("the native prelude has no production labelled {label}"));
        assert_eq!(production.hook.as_deref(), hook, "hook of {label}");
        assert!(
            self.reaches(k_module, &production.module),
            "{label} is declared in {}, which {k_module} does not import",
            production.module
        );
        assert_eq!(production.sort, result, "result sort of {label}");
        assert_eq!(production.arguments, arguments, "argument sorts of {label}");
    }
}

fn collect_productions(module: &FlatModule, productions: &mut BTreeMap<String, PreludeProduction>) {
    for sentence in &module.local_sentences {
        if let Sentence::Production {
            label: Some(label),
            parameters,
            sort,
            items,
            attributes,
        } = &**sentence
        {
            productions.insert(
                label.name.clone(),
                PreludeProduction {
                    module: module.name.clone(),
                    hook: attributes.get_str("hook").map(str::to_owned),
                    smt: attributes.get_str("smt-hook").is_some()
                        || attributes.get_str("smtlib").is_some(),
                    sort: sort.name.clone(),
                    parameters: parameters
                        .iter()
                        .map(|parameter| parameter.name.clone())
                        .collect(),
                    arguments: items
                        .iter()
                        .filter_map(|item| match item {
                            ProductionItem::NonTerminal { sort, .. } => Some(sort.name.clone()),
                            _ => None,
                        })
                        .collect(),
                },
            );
        }
    }
}

/// The prelude spelling of a builtin operation sort; `Parameter` is the
/// production's sort parameter.
fn operation_sort(sort: OperationSort, parameter: Option<&String>) -> String {
    match sort {
        OperationSort::Builtin(sort) => sort.k_name().to_owned(),
        OperationSort::K => "K".to_owned(),
        OperationSort::Parameter => parameter
            .cloned()
            .expect("a sort-parametric operation's production has a parameter"),
    }
}

fn require_collection(prelude: &Prelude, spec: &CollectionOperationSpec) {
    let arguments = spec
        .operand_sorts
        .iter()
        .map(|sort| match sort {
            CollectionOperandSort::Builtin(sort) => sort.k_name().to_owned(),
            CollectionOperandSort::Element => "KItem".to_owned(),
        })
        .collect::<Vec<_>>();
    let result = match spec.result_sort {
        CollectionResultSort::Builtin(sort) => sort.k_name(),
        CollectionResultSort::Projected => "KItem",
    };
    prelude.require(spec.k_label, spec.k_hook, spec.k_module, result, &arguments);
}

#[test]
fn every_catalog_row_matches_the_pinned_native_prelude() {
    let prelude = Prelude::load();
    for operation in BuiltinOperation::ALL {
        let spec = operation.spec();
        let production = prelude
            .productions
            .get(spec.k_label)
            .unwrap_or_else(|| panic!("no native production labelled {}", spec.k_label));
        let parameter = production.parameters.first();
        let arguments = spec
            .argument_sorts
            .iter()
            .map(|sort| operation_sort(*sort, parameter))
            .collect::<Vec<_>>();
        prelude.require(
            spec.k_label,
            spec.k_hook,
            spec.k_module,
            &operation_sort(spec.result_sort, parameter),
            &arguments,
        );
        assert!(
            CATALOG_MODULES.contains(&spec.k_module),
            "{operation:?} names module {} that the evaluation test does not import",
            spec.k_module
        );
    }
    for operation in MapOperation::ALL {
        require_collection(&prelude, operation.spec());
    }
    for operation in ListOperation::ALL {
        require_collection(&prelude, operation.spec());
    }
    for operation in SetOperation::ALL {
        require_collection(&prelude, operation.spec());
    }
    for sort in BuiltinSort::ALL {
        if let Some(module) = sort.spec().k_module {
            assert!(
                prelude.imports.contains_key(module),
                "{sort:?} names K module {module}, which the prelude lacks"
            );
        }
    }
}

fn apply(label: &str, arguments: &[String]) -> String {
    format!("{}{{}}({})", encode_label(label), arguments.join(", "))
}

fn int(value: i64) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

fn boolean(value: bool) -> String {
    format!("\\dv{{SortBool{{}}}}(\"{value}\")")
}

fn builtin(operation: BuiltinOperation, arguments: &[String]) -> String {
    apply(operation.spec().k_label, arguments)
}

fn float(token: &str) -> String {
    format!("\\dv{{SortFloat{{}}}}(\"{token}\")")
}

fn string(value: &str) -> String {
    format!("\\dv{{SortString{{}}}}(\"{value}\")")
}

/// The one-item computation `value ~> .K`, a ground term of sort `K`.
fn sequence(value: i64) -> String {
    format!("kseq{{}}({}, dotk{{}}())", item(value))
}

fn item(value: i64) -> String {
    format!("inj{{SortInt{{}}, SortKItem{{}}}}({})", int(value))
}

/// `Int2Bytes(2, 258, BE)`, the bytes `\x01\x02`.
fn two_bytes() -> String {
    builtin(
        BuiltinOperation::BytesFromInt,
        &[
            int(2),
            int(258),
            builtin(BuiltinOperation::BytesBigEndian, &[]),
        ],
    )
}

fn map_of(entries: &[(i64, i64)]) -> String {
    entries
        .iter()
        .map(|(key, value)| {
            apply(
                MapOperation::Item.spec().k_label,
                &[item(*key), item(*value)],
            )
        })
        .reduce(|left, right| apply(MapOperation::CONCATENATION.k_label, &[left, right]))
        .unwrap_or_else(|| apply(MapOperation::Empty.spec().k_label, &[]))
}

fn set_of(values: &[i64]) -> String {
    values
        .iter()
        .map(|value| apply(SetOperation::Item.spec().k_label, &[item(*value)]))
        .reduce(|left, right| apply(SetOperation::Concat.spec().k_label, &[left, right]))
        .unwrap_or_else(|| apply(SetOperation::Empty.spec().k_label, &[]))
}

fn list_of(values: &[i64]) -> String {
    values
        .iter()
        .map(|value| apply(ListOperation::Item.spec().k_label, &[item(*value)]))
        .reduce(|left, right| apply(ListOperation::Concat.spec().k_label, &[left, right]))
        .unwrap_or_else(|| apply(ListOperation::Empty.spec().k_label, &[]))
}

/// Ground arguments of one application of each builtin operation.
#[expect(
    clippy::too_many_lines,
    reason = "One arm per group of catalog operations."
)]
fn builtin_arguments(operation: BuiltinOperation) -> Vec<String> {
    use BuiltinOperation as Op;
    match operation {
        Op::IntAdd
        | Op::IntSub
        | Op::IntMul
        | Op::IntTDiv
        | Op::IntMod
        | Op::IntShiftRight
        | Op::IntShiftLeft
        | Op::IntBitAnd
        | Op::IntBitXor
        | Op::IntBitOr
        | Op::IntGreaterEqual
        | Op::IntGreater
        | Op::IntLessEqual
        | Op::IntLess
        | Op::IntEqual
        | Op::IntNotEqual
        | Op::IntTMod
        | Op::IntEDiv
        | Op::IntPow
        | Op::IntMin
        | Op::IntMax
        | Op::IntDivides => vec![int(-7), int(3)],
        Op::IntPowMod | Op::IntBitRange | Op::IntSignExtendBitRange => {
            vec![int(4660), int(4), int(8)]
        }
        Op::IntLog2 | Op::IntBitNot | Op::IntAbs => vec![int(1024)],
        Op::BoolNot | Op::StringFromBool => vec![boolean(true)],
        Op::BoolEqual
        | Op::BoolNotEqual
        | Op::BoolAnd
        | Op::BoolOr
        | Op::BoolXor
        | Op::BoolImplies
        | Op::BoolAndThen
        | Op::BoolOrElse => vec![boolean(true), boolean(false)],
        Op::BytesEmpty
        | Op::BytesLittleEndian
        | Op::BytesBigEndian
        | Op::BytesSigned
        | Op::BytesUnsigned => Vec::new(),
        Op::BytesLength | Op::BytesReverse | Op::BytesToString => vec![two_bytes()],
        Op::BytesGet => vec![two_bytes(), int(1)],
        Op::BytesUpdate | Op::BytesPadRight | Op::BytesPadLeft | Op::BytesSubstring => {
            vec![two_bytes(), int(1), int(2)]
        }
        Op::BytesConcat => vec![two_bytes(), two_bytes()],
        Op::BytesReplaceAt => vec![two_bytes(), int(0), two_bytes()],
        Op::BytesFromInt => vec![
            int(4),
            int(-2),
            builtin(BuiltinOperation::BytesLittleEndian, &[]),
        ],
        Op::BytesFromIntNoLen => vec![
            int(-2),
            builtin(BuiltinOperation::BytesBigEndian, &[]),
            builtin(BuiltinOperation::BytesSigned, &[]),
        ],
        Op::BytesToInt => vec![
            two_bytes(),
            builtin(BuiltinOperation::BytesLittleEndian, &[]),
            builtin(BuiltinOperation::BytesUnsigned, &[]),
        ],
        Op::StringConcat
        | Op::StringEqual
        | Op::StringNotEqual
        | Op::StringLess
        | Op::StringLessEqual
        | Op::StringGreater
        | Op::StringGreaterEqual => vec![string("ab"), string("ac")],
        Op::StringLength | Op::StringToBool => vec![string("true")],
        Op::StringSubstring => vec![string("hello"), int(1), int(3)],
        Op::StringFind => vec![string("hello"), string("l"), int(0)],
        Op::StringChr => vec![int(65)],
        Op::StringOrd => vec![string("A")],
        Op::StringFromInt => vec![int(-42)],
        Op::StringToInt => vec![string("42")],
        Op::BytesFromString => vec![string("hi")],
        Op::KEqualEq | Op::KEqualNe => vec![sequence(1), sequence(2)],
        Op::KEqualIte => vec![boolean(false), int(1), int(2)],
        Op::FloatAdd
        | Op::FloatSub
        | Op::FloatMul
        | Op::FloatDiv
        | Op::FloatEqual
        | Op::FloatNotEqual
        | Op::FloatLess
        | Op::FloatLessEqual
        | Op::FloatGreater
        | Op::FloatGreaterEqual
        | Op::FloatMin
        | Op::FloatMax => vec![float("1.5"), float("0.25")],
        Op::FloatNeg
        | Op::FloatAbs
        | Op::FloatFloor
        | Op::FloatCeil
        | Op::FloatTrunc
        | Op::FloatSqrt
        | Op::FloatIsNan
        | Op::FloatIsInfinite
        | Op::FloatSign
        | Op::FloatPrecision
        | Op::FloatExponentBits
        | Op::FloatToInt => vec![float("2.25")],
        Op::FloatRound => vec![float("1.5"), int(24), int(8)],
        Op::FloatRoot => vec![float("2.25"), int(2)],
        Op::FloatMaxValue => vec![int(53), int(11)],
        Op::FloatFromInt => vec![int(5), int(53), int(11)],
        Op::IoWrite => vec![int(1), string("x")],
        Op::IoPutc => vec![int(1), int(120)],
        Op::IoLog => vec![string("x")],
    }
}

fn map_arguments(operation: MapOperation) -> Vec<String> {
    let map = map_of(&[(1, 10), (2, 20)]);
    match operation {
        MapOperation::Empty => Vec::new(),
        MapOperation::Item => vec![item(1), item(10)],
        MapOperation::Update => vec![map, item(3), item(30)],
        MapOperation::Get | MapOperation::Remove => vec![map, item(1)],
        MapOperation::InKeys => vec![item(1), map],
        MapOperation::RemoveAll => vec![map, set_of(&[1, 3])],
        MapOperation::Keys | MapOperation::KeysList | MapOperation::Values | MapOperation::Size => {
            vec![map]
        }
        MapOperation::UpdateAll => vec![map, map_of(&[(2, 99)])],
        MapOperation::GetOrDefault => vec![map, item(9), item(0)],
    }
}

fn list_arguments(operation: ListOperation) -> Vec<String> {
    let list = list_of(&[1, 2]);
    match operation {
        ListOperation::Empty => Vec::new(),
        ListOperation::Item => vec![item(1)],
        ListOperation::Concat => vec![list.clone(), list],
        ListOperation::Get => vec![list, int(1)],
        ListOperation::Update => vec![list, int(1), item(7)],
        ListOperation::Size => vec![list],
        ListOperation::Make => vec![int(2), item(7)],
        ListOperation::Range => vec![list, int(1), int(0)],
        ListOperation::UpdateAll => vec![list, int(1), list_of(&[7])],
        ListOperation::Contains => vec![item(2), list],
    }
}

fn set_arguments(operation: SetOperation) -> Vec<String> {
    match operation {
        SetOperation::Empty => Vec::new(),
        SetOperation::Item => vec![item(1)],
        SetOperation::Concat => vec![set_of(&[1]), set_of(&[2])],
        SetOperation::Union
        | SetOperation::Difference
        | SetOperation::Intersect
        | SetOperation::IsSubset => vec![set_of(&[1, 2]), set_of(&[2, 3])],
        SetOperation::Contains => vec![item(2), set_of(&[1, 2])],
        SetOperation::Size | SetOperation::ToList => vec![set_of(&[1, 2])],
        SetOperation::FromList => vec![list_of(&[1, 1])],
    }
}

/// The KORE of the smoke definition with every catalog module imported, so it
/// declares every catalog symbol.
fn evaluation_kore() -> (String, String) {
    let mut adapted = adapt_definition(&smoke_definition()).unwrap();
    let main = adapted.definition.main_module.clone();
    let module = adapted
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == main)
        .unwrap();
    module
        .imports
        .extend(CATALOG_MODULES.iter().map(|name| FlatImport {
            name: (*name).to_owned(),
            public: true,
        }));
    let loaded = prepare_definition(adapted.definition, Backend::Llvm).unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    (artifacts.definition_kore, main)
}

#[test]
fn one_ground_application_of_every_exposed_operation_evaluates_natively() {
    let (kore, main) = evaluation_kore();
    let mut backend = NativeBackend::new(&kore, &main, BackendOptions::default()).unwrap();
    let mut cases = Vec::new();
    for operation in BuiltinOperation::ALL {
        let spec = operation.spec();
        let arguments = builtin_arguments(operation);
        // A sort-parametric symbol takes its instance as a KORE sort parameter.
        let pattern = if spec.result_sort == OperationSort::Parameter {
            format!(
                "{}{{SortInt{{}}}}({})",
                encode_label(spec.k_label),
                arguments.join(", ")
            )
        } else {
            apply(spec.k_label, &arguments)
        };
        cases.push((spec.k_label, spec.functional, pattern));
    }
    for operation in MapOperation::ALL {
        let label = operation.spec().k_label;
        cases.push((label, true, apply(label, &map_arguments(operation))));
    }
    for operation in ListOperation::ALL {
        let label = operation.spec().k_label;
        cases.push((label, true, apply(label, &list_arguments(operation))));
    }
    for operation in SetOperation::ALL {
        let label = operation.spec().k_label;
        cases.push((label, true, apply(label, &set_arguments(operation))));
    }
    for (label, functional, pattern) in cases {
        let result = backend
            .execute(ExecuteRequest::new(parse_pattern(&pattern).unwrap()))
            .unwrap_or_else(|error| panic!("{label}: {error}"));
        assert_eq!(result.leaves.len(), 1, "{label}: {result:#?}");
        // The state is KORE JSON: `#Bottom` is the tag `Bottom`, and a symbol
        // application names its symbol as a JSON string.
        let rendered = result.leaves[0].state.to_string();
        assert!(
            !rendered.contains("\"Bottom\""),
            "{label} is undefined: {rendered}"
        );
        let symbol = format!("\"{}\"", encode_label(label));
        if CONSOLE_HOOK_LABELS.contains(&label) {
            assert!(
                rendered.contains(&symbol),
                "{label} now evaluates without console state; drop it from CONSOLE_HOOK_LABELS: {rendered}"
            );
            continue;
        }
        // A function evaluates away; a constructor is its own value, and an
        // associative unit or item may remain as the value's structure.
        if functional
            && !matches!(
                label,
                ".Map" | "_|->_" | ".List" | "ListItem" | "_List_" | ".Set" | "SetItem" | "_Set_"
            )
        {
            assert!(
                !rendered.contains(&symbol),
                "{label} remained unevaluated: {rendered}"
            );
        }
    }
}

/// The catalog's SMT-translation fact (KF-043) is exactly the prelude's
/// `smt-hook`/`smtlib` attributes: an `smt_lemma` may mention an operation only
/// when Z3 can see it.
#[test]
fn catalog_smt_translations_match_the_pinned_native_prelude() {
    let prelude = Prelude::load();
    let smt = |label: &str| {
        prelude
            .productions
            .get(label)
            .unwrap_or_else(|| panic!("no native production labelled {label}"))
            .smt
    };
    for operation in BuiltinOperation::ALL {
        assert_eq!(
            operation.has_smt_translation(),
            smt(operation.spec().k_label),
            "SMT translation of {operation:?}"
        );
    }
    for operation in MapOperation::ALL {
        assert_eq!(
            operation.has_smt_translation(),
            smt(operation.spec().k_label),
            "SMT translation of {operation:?}"
        );
    }
    for operation in ListOperation::ALL {
        assert_eq!(
            operation.has_smt_translation(),
            smt(operation.spec().k_label),
            "SMT translation of {operation:?}"
        );
    }
    for operation in SetOperation::ALL {
        assert_eq!(
            operation.has_smt_translation(),
            smt(operation.spec().k_label),
            "SMT translation of {operation:?}"
        );
    }
}
