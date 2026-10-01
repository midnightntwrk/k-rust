//@ check-pass
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{DescriptorLoweringError, lower_descriptor_bundle};

#[renamed_krs::sort]
pub trait KItem {}

#[renamed_krs::sort]
pub trait KResult: KItem {}

#[renamed_krs::sort]
pub trait Obj: KResult {}

#[renamed_krs::constructor(sort = Obj, syntax = "guarded({value})")]
pub struct Guarded {
    pub value: renamed_krs::Term<renamed_krs::builtin::int::Int>,
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
#[renamed_krs::requires(renamed_krs::builtin::int::add(value, 1))]
pub fn guarded(
    Guarded { value }: renamed_krs::Term<dyn Obj>,
) -> renamed_krs::Term<dyn Obj> {
    Guarded { value }
}

fn main() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("Cargo.toml")
        .canonicalize()
        .unwrap();
    let context = PackageContext::new(
        "KRS-REQUIRES-NON-BOOL",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "requires_non_bool",
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
    let DescriptorLoweringError::InvalidTerm { detail, .. } = error else {
        panic!("unexpected typed error: {error}");
    };
    println!("{detail}");
}
