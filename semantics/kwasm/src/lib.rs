//! Readable qualification slice for `KWasm` integer arithmetic.
//!
//! The source mapping is pinned in `../../tests/kwasm/source-map.md`.
//! This definition preserves `KWasm`'s constant normalization, value transfer,
//! operand loading, functional arithmetic, and division traps.

use k::KResult;
use k::builtin::{Int, KSequence, int};

k::sorts! {
    IValType;
    IBinOp;
    Instr: k::KItem;
    Instrs: k::KItem;
    Val: KResult;
    ValStack;
}

#[k::constructors(sort = IValType, result = KResult)]
#[k::precedence((I32, I64))]
pub enum IntegerType {
    #[k::syntax("i32")]
    I32,
    #[k::syntax("i64")]
    I64,
}

#[k::constructors(sort = IBinOp, result = KResult)]
#[k::precedence((Add, Sub, Mul, DivU))]
pub enum IntegerBinOp {
    #[k::syntax("add")]
    Add,
    #[k::syntax("sub")]
    Sub,
    #[k::syntax("mul")]
    Mul,
    #[k::syntax("div_u")]
    DivU,
}

#[k::constructors(sort = Val, result = KResult)]
#[k::precedence((Integer, Undefined))]
pub enum Value {
    #[k::syntax("< {ty} > {value}")]
    Integer { ty: IValType, value: Int },
    #[k::syntax("undefined")]
    Undefined(),
}

#[k::constructors(sort = ValStack, result = KResult)]
#[k::precedence((Empty, Cons))]
pub enum Stack {
    #[k::syntax(".ValStack")]
    Empty(),
    #[k::syntax("{head} : {tail}")]
    Cons { head: Val, tail: ValStack },
}

#[k::constructors(sort = Instr, result = KResult)]
#[k::precedence((Const, Binary, Trap))]
pub enum Instruction {
    #[k::syntax("{ty}.const {value}")]
    Const { ty: IValType, value: Int },
    #[k::syntax("{ty}.{op}")]
    Binary { ty: IValType, op: IBinOp },
    #[k::syntax("trap")]
    Trap(),
}

/// A concrete right-recursive program list, corresponding to `KWasm`'s `Instrs`.
#[k::constructors(sort = Instrs, result = KResult)]
#[k::precedence((InstrEmpty, InstrCons))]
pub enum InstrList {
    #[k::syntax(".Instrs")]
    InstrEmpty(),
    #[k::syntax("{head} ; {tail}")]
    InstrCons { head: Instr, tail: Instrs },
}

#[k::function(total, sort = Val, syntax = "#kwasmChop({ty}, {value})")]
pub struct Chop {
    pub ty: k::Term<IValType>,
    pub value: k::Term<Int>,
}

#[k::function(
    total,
    sort = Val,
    syntax = "#kwasmIntBinOp({ty}, {op}, {lhs}, {rhs})"
)]
pub struct IntBinOp {
    pub ty: k::Term<IValType>,
    pub op: k::Term<IBinOp>,
    pub lhs: k::Term<Int>,
    pub rhs: k::Term<Int>,
}

#[k::equation]
fn chop_i32(k::term![Chop(IntegerType::I32, value)]: k::Term<Val>) -> k::Term<Val> {
    k::term![Value::Integer(
        IntegerType::I32,
        int::sub(
            value,
            int::mul(int::div(value, 4_294_967_296), 4_294_967_296)
        ),
    )]
}

#[k::equation]
fn chop_i64(k::term![Chop(IntegerType::I64, value)]: k::Term<Val>) -> k::Term<Val> {
    k::term![Value::Integer(
        IntegerType::I64,
        int::sub(
            value,
            int::mul(
                int::div(value, 18_446_744_073_709_551_616),
                18_446_744_073_709_551_616,
            ),
        ),
    )]
}

#[k::equation]
fn add(k::term![IntBinOp(ty, IntegerBinOp::Add, lhs, rhs)]: k::Term<Val>) -> k::Term<Val> {
    k::term![Chop(ty, int::add(lhs, rhs))]
}

#[k::equation]
fn sub_i32(
    k::term![IntBinOp(IntegerType::I32, IntegerBinOp::Sub, lhs, rhs)]: k::Term<Val>,
) -> k::Term<Val> {
    k::term![Chop(
        IntegerType::I32,
        int::sub(int::add(lhs, 4_294_967_296), rhs)
    )]
}

#[k::equation]
fn sub_i64(
    k::term![IntBinOp(IntegerType::I64, IntegerBinOp::Sub, lhs, rhs)]: k::Term<Val>,
) -> k::Term<Val> {
    k::term![Chop(
        IntegerType::I64,
        int::sub(int::add(lhs, 18_446_744_073_709_551_616), rhs),
    )]
}

#[k::equation]
fn mul(k::term![IntBinOp(ty, IntegerBinOp::Mul, lhs, rhs)]: k::Term<Val>) -> k::Term<Val> {
    k::term![Chop(ty, int::mul(lhs, rhs))]
}

#[k::requires(int::ne(rhs, 0))]
#[k::equation]
fn div_u(k::term![IntBinOp(ty, IntegerBinOp::DivU, lhs, rhs)]: k::Term<Val>) -> k::Term<Val> {
    k::term![Value::Integer(ty, int::div(lhs, rhs))]
}

#[k::requires(int::eq(rhs, 0))]
#[k::equation]
fn div_u_zero(k::term![IntBinOp(_, IntegerBinOp::DivU, _, rhs)]: k::Term<Val>) -> k::Term<Val> {
    k::term![Value::Undefined()]
}

/// The two operational cells selected from `KWasm`'s `<wasm>` configuration.
#[k::configuration]
pub struct Machine {
    #[k::cell(name = "instrs")]
    pub instrs: KSequence,
    #[k::cell(name = "valstack")]
    pub valstack: ValStack,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] program: KSequence,
        #[k::config_var(name = "STACK")] stack: ValStack,
    ) -> Self {
        Self {
            instrs: k::k![program],
            valstack: stack,
        }
    }
}

k::rules! {
    for Machine;
    use InstrList::*;

    sequence_cons: {
        instrs: [InstrCons(head, tail), ..],
    } => {
        instrs: [head, tail, ..],
    }
    where head: Instr, tail: Instrs;

    sequence_empty: {
        instrs: [InstrEmpty(), ..],
    } => {
        instrs: [..],
    };
}

#[rustfmt::skip]
k::rules! {
    for Machine;
    use Instruction::*;

    constant_i32: {
        instrs: [Const(IntegerType::I32, value), ..],
    } => {
        instrs: [crate::Chop(IntegerType::I32, int::add(value, 4_294_967_296)), ..],
    }
    where value: Int;

    constant_i64: {
        instrs: [Const(IntegerType::I64, value), ..],
    } => {
        instrs: [crate::Chop(IntegerType::I64, int::add(value, 18_446_744_073_709_551_616),), ..],
    }
    where value: Int;

    undefined_traps: {
        instrs: [Value::Undefined(), ..],
    } => {
        instrs: [Trap(), ..],
    };

    load_binary_i32: {
        instrs: [Binary(IntegerType::I32, op), ..],
        valstack: Stack::Cons(Value::Integer(IntegerType::I32, rhs), Stack::Cons(Value::Integer(IntegerType::I32, lhs), rest),),
    } => {
        instrs: [crate::IntBinOp(IntegerType::I32, op, lhs, rhs), ..],
        valstack: rest,
    }
    where op: IBinOp, lhs: Int, rhs: Int, rest: ValStack;

    load_binary_i64: {
        instrs: [Binary(IntegerType::I64, op), ..],
        valstack: Stack::Cons(Value::Integer(IntegerType::I64, rhs), Stack::Cons(Value::Integer(IntegerType::I64, lhs), rest),),
    } => {
        instrs: [crate::IntBinOp(IntegerType::I64, op, lhs, rhs), ..],
        valstack: rest,
    }
    where op: IBinOp, lhs: Int, rhs: Int, rest: ValStack;

    push_value: {
        instrs: [Value::Integer(ty, value), ..],
        valstack: stack,
    } => {
        instrs: [..],
        valstack: Stack::Cons(Value::Integer(ty, value), stack),
    }
    where ty: IValType, value: Int, stack: ValStack;
}

/// Executable all-path claim corresponding to `KWasm`'s simple-addition claim shape.
#[k::claim(all_paths, label = "simple-addition")]
fn simple_addition(
    k::cells! {
        instrs: k::configuration::KCell(
            Instruction::Const(IntegerType::I32, 3),
            Instruction::Const(IntegerType::I32, 4),
            Instruction::Binary(IntegerType::I32, IntegerBinOp::Add)
        ),
        valstack: k::configuration::Cell(Stack::Empty()),
    }: Machine,
) -> Machine {
    k::cells! {
        instrs: k::configuration::KCell(.K),
        valstack: k::configuration::Cell(Stack::Cons(
            Value::Integer(IntegerType::I32, 7),
            Stack::Empty(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use krs_compiler::{
        PackageContext, collect_host_descriptors_with_builtins, emit_k, lower_descriptor_bundle,
        lower_semantic_theory,
    };

    fn package_context() -> PackageContext {
        PackageContext::new(
            "KRS-KWASM",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
            "workspace",
            "krs_kwasm_semantics",
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .expect("fixture package context is valid")
    }

    #[test]
    fn readable_kwasm_slice_collects_and_lowers_deterministically() {
        let descriptors = k::host_descriptors().collect::<Vec<_>>();
        let first = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.clone(),
            &k::builtin_registry(),
        )
        .expect("KWasm slice descriptors collect");
        let second = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.into_iter().rev(),
            &k::builtin_registry(),
        )
        .expect("reordered KWasm slice descriptors collect");
        assert_eq!(
            first.to_canonical_json().unwrap(),
            second.to_canonical_json().unwrap(),
            "descriptor JSON must not depend on inventory registration order",
        );

        let semantic = lower_descriptor_bundle(&first).expect("KWasm descriptors lower");
        let definition = lower_semantic_theory(&semantic)
            .expect("KWasm semantic theory lowers to Definition IR");
        let emitted = emit_k(&definition).expect("KWasm Definition IR emits K");
        let source = emitted.source();
        assert!(source.contains("<instrs>"));
        assert!(source.contains("<valstack>"));
        assert!(source.contains("load-binary-i32"));
        assert!(source.contains("load-binary-i64"));
        assert!(source.contains("# kwasmIntBinOp"));
        assert!(source.contains("div_u"));
        assert!(source.contains("=> undefined"));
        assert!(source.contains("undefined-traps"));
        assert!(source.contains("=/=Int"));
        assert!(source.contains("==Int"));
        assert!(source.contains("trap"));
        assert!(source.contains("4294967296"));
        assert!(source.contains("18446744073709551616"));
    }

    #[test]
    fn ordinary_valstack_rewrites_retain_exact_authored_anchors() {
        let bundle = collect_host_descriptors_with_builtins(
            [package_context()],
            k::host_descriptors(),
            &k::builtin_registry(),
        )
        .expect("KWasm slice descriptors collect");
        let json = bundle.to_canonical_json().unwrap();
        assert!(json.contains("rewrite_cell"));
        assert!(json.contains("rule_left_cells_field"));
        assert!(json.contains("rule_right_cells_field"));
        assert!(json.contains("rule_left_application_head"));
        assert!(json.contains("rule_right_application_head"));
        assert!(json.contains("valstack"));
    }
}
