use krs_compiler::{PackageContext, collect_host_descriptors_with_builtins};
use renamed_krs::builtin::{KSequence, Map};

#[renamed_krs::sort]
pub trait Expr {}

#[renamed_krs::constructor(sort = Expr, syntax = "wrap({value})")]
pub struct Wrap {
    pub value: renamed_krs::Term<dyn Expr>,
}

#[renamed_krs::constructor(sort = Expr, syntax = "halt")]
pub struct Halt;

#[renamed_krs::configuration]
pub struct Machine {
    #[renamed_krs::cell]
    pub k: KSequence,
    #[renamed_krs::cell]
    pub env: Map,
}

impl Machine {
    #[renamed_krs::init]
    pub fn init(env: Map) -> Self {
        Self {
            k: renamed_krs::k![Halt],
            env,
        }
    }
}

mod impostor {
    pub struct Update(pub (), pub (), pub ());
    pub use Update as update;
}

renamed_krs::rules! {
    for Machine;

    bad: {
        k: [Wrap(value), ..],
        env: map,
    } => {
        k: [..],
        env: impostor::update(map, value, value),
    };
}

fn main() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("Cargo.toml")
        .canonicalize()
        .unwrap();
    let context = PackageContext::new(
        "KRS-MAP-UPDATE-LOOKALIKE",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        "readable_rule_update_lookalike",
        manifest,
    )
    .unwrap();
    let error = collect_host_descriptors_with_builtins(
        [context],
        renamed_krs::host_descriptors(),
        &renamed_krs::builtin_registry(),
    )
    .unwrap_err();
    println!("{}", error.detail());
}
