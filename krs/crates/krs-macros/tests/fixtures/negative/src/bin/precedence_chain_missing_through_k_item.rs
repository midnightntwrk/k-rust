//@ check-pass
//! A field of sort `KItem` admits every sort, so a family whose template
//! ends with one needs a chain.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{DescriptorLoweringError, lower_descriptor_bundle};
use renamed_krs as k;

k::sorts! {
    Step: k::KItem;
}

#[k::constructors(sort = Step, result = k::KResult)]
pub enum Steps {
    #[k::syntax("idle")]
    Idle(),
    #[k::syntax("#then({count}) {next}")]
    Then {
        count: k::builtin::Int,
        next: k::KItem,
    },
}

#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Step) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![pgm]),
        }
    }
}

fn main() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("Cargo.toml")
        .canonicalize()
        .unwrap();
    let context = PackageContext::new(
        "KRS-PRECEDENCE-CHAIN",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "precedence_chain_missing_through_k_item",
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
    let DescriptorLoweringError::MissingPrecedenceChain { .. } = error else {
        panic!("unexpected typed error: {error}");
    };
    println!("{error}");
}
