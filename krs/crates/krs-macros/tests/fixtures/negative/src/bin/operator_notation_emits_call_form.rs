//@ check-pass
//! Two rules that differ only in how their condition and result are spelled,
//! as builtin calls and as operators, under the renamed facade and without
//! importing a builtin module, emit the same K up to their names: each
//! operator denotes the operation of the domain its operands' sorts choose.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};
use renamed_krs::builtin::int::Int;

#[renamed_krs::sort(alias = Obj, parents = [renamed_krs::KResult])]
pub trait ObjSort: renamed_krs::KResultSort {}
pub type Obj = renamed_krs::Term<dyn ObjSort>;

#[renamed_krs::constructor(sort = Obj, syntax = "called({value}, {limit}, {flag})")]
pub struct Called {
    pub value: renamed_krs::Term<Int>,
    pub limit: renamed_krs::Term<Int>,
    pub flag: renamed_krs::Term<renamed_krs::builtin::bool::Bool>,
}

#[renamed_krs::constructor(sort = Obj, syntax = "operated({value}, {limit}, {flag})")]
pub struct Operated {
    pub value: renamed_krs::Term<Int>,
    pub limit: renamed_krs::Term<Int>,
    pub flag: renamed_krs::Term<renamed_krs::builtin::bool::Bool>,
}

#[renamed_krs::constructor(sort = Obj, syntax = "halt")]
pub struct Halt;

#[renamed_krs::constructor(sort = Obj, syntax = "result({value}, {flag})")]
pub struct Outcome {
    pub value: renamed_krs::Term<Int>,
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
    renamed_krs::builtin::bool::and_then(
        renamed_krs::builtin::int::eq(
            renamed_krs::builtin::int::add(
                renamed_krs::builtin::int::bit_and(value, 15),
                renamed_krs::builtin::int::bit_and(limit, 15)
            ),
            renamed_krs::builtin::int::shift_left(1, 4)
        ),
        renamed_krs::builtin::bool::not(renamed_krs::builtin::bool::eq(flag, true))
    ),
    renamed_krs::builtin::int::ge(
        renamed_krs::builtin::int::bit_xor(
            renamed_krs::builtin::int::bit_or(value, limit),
            renamed_krs::builtin::int::bit_not(limit)
        ),
        renamed_krs::builtin::int::shift_right(value, 2)
    )
))]
pub fn called(
    Called { value, limit, flag }: renamed_krs::Term<dyn ObjSort>,
) -> renamed_krs::Term<dyn ObjSort> {
    Outcome {
        value: renamed_krs::builtin::int::sub(
            renamed_krs::builtin::int::mul(renamed_krs::builtin::int::sub(0, value), limit),
            renamed_krs::builtin::int::rem(renamed_krs::builtin::int::div(value, limit), -3),
        ),
        flag: renamed_krs::builtin::bool::ne(
            renamed_krs::builtin::bool::not(flag),
            renamed_krs::builtin::int::lt(value, limit),
        ),
    }
}

#[renamed_krs::rule]
#[renamed_krs::requires(
    (value & 15) + (limit & 15) == 1 << 4 && !(flag == true) && (value | limit) ^ !limit >= value >> 2
)]
pub fn operated(
    Operated { value, limit, flag }: renamed_krs::Term<dyn ObjSort>,
) -> renamed_krs::Term<dyn ObjSort> {
    Outcome {
        value: -value * limit - value / limit % -3,
        flag: !flag != (value < limit),
    }
}

fn main() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("Cargo.toml")
        .canonicalize()
        .unwrap();
    let context = PackageContext::new(
        "KRS-OPERATOR-NOTATION",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "operator_notation_emits_call_form",
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
    let operated = rule("operated");
    assert_eq!(
        called.replacen("called", "operated", 1),
        operated,
        "the two spellings emitted different K"
    );
    println!("{operated}");
}
