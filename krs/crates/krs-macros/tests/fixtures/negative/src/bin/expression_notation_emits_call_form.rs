//@ check-pass
//! Two rules that differ only in how their condition and result are spelled,
//! as builtin calls and as expression notation, under the renamed facade and
//! without importing a builtin module, emit the same K up to their names.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};
use renamed_krs::builtin::int::Int;

#[renamed_krs::sort(alias = Obj, parents = [renamed_krs::KResult])]
pub trait ObjSort: renamed_krs::KResultSort {}
pub type Obj = renamed_krs::Term<dyn ObjSort>;

#[renamed_krs::constructor(sort = Obj, syntax = "called({value}, {limit})")]
pub struct Called {
    pub value: renamed_krs::Term<Int>,
    pub limit: renamed_krs::Term<Int>,
}

#[renamed_krs::constructor(sort = Obj, syntax = "noted({value}, {limit})")]
pub struct Noted {
    pub value: renamed_krs::Term<Int>,
    pub limit: renamed_krs::Term<Int>,
}

#[renamed_krs::constructor(sort = Obj, syntax = "halt")]
pub struct Halt;

#[renamed_krs::constructor(sort = Obj, syntax = "verdict({flag})")]
pub struct Verdict {
    pub flag: renamed_krs::Term<renamed_krs::builtin::bool::Bool>,
}

#[renamed_krs::configuration(root = "machine")]
pub struct Machine {
    pub k: renamed_krs::configuration::KCell<renamed_krs::builtin::KSequence>,
}

impl Machine {
    #[renamed_krs::init]
    pub fn init() -> Self {
        Self {
            k: renamed_krs::configuration::KCell::new(renamed_krs::k![Halt]),
        }
    }
}

#[renamed_krs::rule]
#[renamed_krs::requires(renamed_krs::builtin::bool::and_then(
    renamed_krs::builtin::int::gt(value, 0),
    renamed_krs::builtin::bool::or_else(
        renamed_krs::builtin::int::lt(value, limit),
        renamed_krs::builtin::int::ne(renamed_krs::builtin::int::bit_and(limit, value), limit)
    )
))]
pub fn called(
    Called { value, limit }: renamed_krs::Term<dyn ObjSort>,
) -> renamed_krs::Term<dyn ObjSort> {
    Verdict {
        flag: renamed_krs::builtin::bool::or_else(
            renamed_krs::builtin::kequal::eq(value, limit),
            renamed_krs::builtin::bool::not(renamed_krs::builtin::int::le(value, limit)),
        ),
    }
}

#[renamed_krs::rule]
#[renamed_krs::requires(
    value.gt::<Int>(0) && (value.lt::<Int>(limit) || limit.bit_and::<Int>(value).ne::<Int>(limit))
)]
pub fn noted(
    Noted { value, limit }: renamed_krs::Term<dyn ObjSort>,
) -> renamed_krs::Term<dyn ObjSort> {
    Verdict {
        flag: value.eq::<K>(limit) || value.le::<Int>(limit).not::<Bool>(),
    }
}

fn main() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("Cargo.toml")
        .canonicalize()
        .unwrap();
    let context = PackageContext::new(
        "KRS-EXPRESSION-NOTATION",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "expression_notation_emits_call_form",
        manifest,
    )
    .unwrap();
    let bundle = collect_host_descriptors_with_builtins(
        [context],
        renamed_krs::host_descriptors(),
        &renamed_krs::builtin_registry(),
    )
    .unwrap();
    let theory = lower_descriptor_bundle(&bundle).unwrap();
    let lowered = lower_semantic_theory(&theory).unwrap();
    let emitted = emit_k(&lowered).unwrap();
    // Each rule's sentence without its generated label.
    let rule = |name: &str| {
        let source = emitted.source();
        let start = source
            .find(&format!("rule {name} ("))
            .unwrap_or_else(|| panic!("no rule rewrites `{name}`:\n{source}"));
        let end = start
            + source[start..]
                .find(" [label(")
                .expect("a rule has a label");
        source[start..end].to_owned()
    };
    let called = rule("called");
    let noted = rule("noted");
    assert_eq!(
        called.replacen("called", "noted", 1),
        noted,
        "the two spellings emitted different K"
    );
    println!("{noted}");
}
