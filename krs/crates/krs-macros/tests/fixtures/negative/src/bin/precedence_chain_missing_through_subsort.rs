//@ check-pass
//! A family whose template ends with a field of a supersort of the
//! family's sort needs a chain: `wrap wrap leaf` nests `Wrap` in `Wrap`.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{DescriptorLoweringError, lower_descriptor_bundle};
use renamed_krs as k;

k::sorts! {
    Exp: k::KItem;
    Atom: Exp;
}

#[k::constructors(sort = Atom, result = k::KResult)]
pub enum AtomSyntax {
    #[k::syntax("leaf")]
    Leaf(),
    #[k::syntax("wrap {inner}")]
    Wrap { inner: Exp },
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
        "precedence_chain_missing_through_subsort",
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
