//@ check-pass
//! `a == b` on two binders of a user sort: no operand's sort lies in a
//! builtin domain, so the operator denotes no one operation and the error
//! names the explicit forms.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{DescriptorLoweringError, OperatorProblem, lower_descriptor_bundle};

#[renamed_krs::sort(alias = Obj, parents = [renamed_krs::KResult])]
pub trait ObjSort: renamed_krs::KResultSort {}
pub type Obj = renamed_krs::Term<dyn ObjSort>;

#[renamed_krs::constructor(sort = Obj, syntax = "same({left}, {right})")]
pub struct Same {
    pub left: renamed_krs::Term<dyn ObjSort>,
    pub right: renamed_krs::Term<dyn ObjSort>,
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
#[renamed_krs::requires(left == right)]
pub fn same(Same { left, right }: renamed_krs::Term<dyn ObjSort>) -> renamed_krs::Term<dyn ObjSort> {
    Halt
}

fn main() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("Cargo.toml")
        .canonicalize()
        .unwrap();
    let context = PackageContext::new(
        "KRS-OPERATOR-AMBIGUOUS",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "operator_ambiguous",
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
        problem: OperatorProblem::Ambiguous,
        reason,
        range: Some(_),
        ..
    } = error
    else {
        panic!("unexpected typed error: {error}");
    };
    println!("{reason}");
}
