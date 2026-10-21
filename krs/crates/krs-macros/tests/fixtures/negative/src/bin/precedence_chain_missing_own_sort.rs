//@ check-pass
//! A family without `#[k::precedence]` whose `+` begins and ends with
//! the family's own sort needs a chain.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{DescriptorLoweringError, lower_descriptor_bundle};
use renamed_krs as k;

k::sorts! {
    Exp: k::KItem;
}

#[k::constructors(sort = Exp, result = k::KResult)]
pub enum Op {
    #[k::syntax("lit")]
    Lit(),
    #[k::syntax("{lhs} + {rhs}")]
    Add { lhs: Exp, rhs: Exp },
}

#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Exp) -> Self {
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
        "precedence_chain_missing_own_sort",
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
