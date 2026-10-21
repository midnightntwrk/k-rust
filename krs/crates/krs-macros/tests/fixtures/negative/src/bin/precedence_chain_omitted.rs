//@ check-pass
//! Families whose templates never place a field that admits the family's
//! sort at an edge need no chain: `{op} a, {src}` begins and ends with fields
//! of other sorts, and `#unimplemented({opcode})` encloses its field. They
//! emit no production group.
use krs_collector::{PackageContext, collect_host_descriptors_with_builtins};
use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};
use renamed_krs as k;

k::sorts! {
    Instr: k::KItem;
    AluOp;
    Operand8;
}

#[k::constructors(sort = AluOp, result = k::KResult)]
pub enum Alu {
    #[k::syntax("add")]
    Add,
    #[k::syntax("xor")]
    Xor,
}

#[k::constructors(sort = Operand8, result = k::KResult)]
pub enum Operand {
    #[k::syntax("reg({index})")]
    Reg { index: k::builtin::Int },
    #[k::syntax("(hl)")]
    HlIndirect,
}

#[k::constructors(sort = Instr, result = k::KResult)]
pub enum Instruction {
    #[k::syntax("nop")]
    Nop,
    #[k::syntax("ld {dst}, {src}")]
    Ld8 { dst: Operand8, src: Operand8 },
    #[k::syntax("{op} a, {src}")]
    Alu8 { op: AluOp, src: Operand8 },
    #[k::syntax("#unimplemented({opcode})")]
    Unimplemented { opcode: Instr },
}

#[k::configuration(root = "machine")]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Instr) -> Self {
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
        "precedence_chain_omitted",
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
    let source = emitted.source();
    assert!(
        !source.contains("group("),
        "a chain-less family emitted a group:\n{source}"
    );
    for line in source.lines().map(str::trim) {
        if line.starts_with("syntax Instr ::=") {
            println!("{line}");
        }
    }
}
