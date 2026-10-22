//@ check-pass
//! `a & b` on two `Bool` operands: `&` is no `Bool` connective, and the
//! error points to `&&` and to the strict `bool::and`.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{DescriptorLoweringError, OperatorProblem, lower_descriptor_bundle};

#[renamed_krs::sort(alias = Obj, parents = [renamed_krs::KResult])]
pub trait ObjSort: renamed_krs::KResultSort {}
pub type Obj = renamed_krs::Term<dyn ObjSort>;

#[renamed_krs::constructor(sort = Obj, syntax = "same({left}, {right})")]
pub struct Same {
    pub left: renamed_krs::Term<renamed_krs::builtin::bool::Bool>,
    pub right: renamed_krs::Term<renamed_krs::builtin::bool::Bool>,
}

#[renamed_krs::constructor(sort = Obj, syntax = "halt")]
pub struct Halt;

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
#[renamed_krs::requires(left & right)]
pub fn same(Same { left, right }: renamed_krs::Term<dyn ObjSort>) -> renamed_krs::Term<dyn ObjSort> {
    Halt
}

fn main() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("Cargo.toml")
        .canonicalize()
        .unwrap();
    let context = PackageContext::new(
        "KRS-OPERATOR-BOOL-BITAND",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "operator_bool_bitand",
        manifest,
    )
    .unwrap();
    let bundle = collect_host_descriptors_with_builtins(
        [context],
        renamed_krs::host_descriptors(),
        &renamed_krs::builtin_registry(),
    )
    .unwrap();
    let error = lower_descriptor_bundle(&bundle).unwrap_err();
    let DescriptorLoweringError::InvalidOperator {
        problem: OperatorProblem::Undefined,
        reason,
        range: Some(_),
        ..
    } = error
    else {
        panic!("unexpected typed error: {error}");
    };
    println!("{reason}");
}
