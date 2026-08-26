//! Readable qualification slice for KMIR basic-block execution.
//!
//! The source mapping and adapter boundary are pinned in
//! `../../draft/readability/kmir/README.md`.

use k::KResult;
use k::builtin::{Bool, Int, KSequence, Map, int, map};
#[allow(unused_imports)]
use k::map;

k::sorts! {
    MirValue: KResult;
    Operand: k::KItem;
    Rvalue: k::KItem;
    Statement: k::KItem;
    Statements: k::KItem;
    Terminator: k::KItem;
    BasicBlock: k::KItem;
    BlockProgram: k::KItem;
    RetVal: k::KItem;
    Continuation: k::KItem;
    Command: k::KItem;
}

#[k::constructors(sort = MirValue, result = KResult)]
#[k::precedence((Integer, Boolean))]
pub enum Value {
    #[k::syntax("mirInt({value})")]
    Integer { value: Int },
    #[k::syntax("mirBool({value})")]
    Boolean { value: Bool },
}

#[k::constructors(sort = Operand, result = KResult)]
#[k::precedence((Constant, Copy))]
pub enum MirOperand {
    #[k::syntax("const({value})")]
    Constant { value: MirValue },
    #[k::syntax("copy(local({local}))")]
    Copy { local: Int },
}

#[k::constructors(sort = Rvalue, result = KResult)]
#[k::precedence((Use, Add))]
pub enum MirRvalue {
    #[k::syntax("use({operand})")]
    Use { operand: Operand },
    #[k::syntax("add({lhs}, {rhs})")]
    Add { lhs: Operand, rhs: Operand },
}

#[k::constructors(sort = Statement, result = KResult)]
#[k::precedence((Assign))]
pub enum MirStatement {
    #[k::syntax("assign(local({local}), {value})")]
    Assign { local: Int, value: Rvalue },
}

#[k::constructors(sort = Statements, result = KResult)]
#[k::precedence((StatementsEmpty, StatementsCons))]
pub enum StatementList {
    #[k::syntax(".Statements")]
    StatementsEmpty(),
    #[k::syntax("{head} ; {tail}")]
    StatementsCons { head: Statement, tail: Statements },
}

#[k::constructors(sort = Terminator, result = KResult)]
#[k::precedence((Goto, SwitchInt, Return))]
pub enum MirTerminator {
    #[k::syntax("goto({target})")]
    Goto { target: Int },
    #[k::syntax("switchInt({discr}, {true_target}, {false_target})")]
    SwitchInt {
        discr: Operand,
        true_target: Int,
        false_target: Int,
    },
    #[k::syntax("return")]
    Return(),
}

#[k::constructors(sort = BasicBlock, result = KResult)]
#[k::precedence((Block))]
pub enum BlockSyntax {
    #[k::syntax("basicBlock({statements}, {terminator})")]
    Block {
        statements: Statements,
        terminator: Terminator,
    },
}

/// Checked recursive adapter for KMIR's serialized `BasicBlocks` list.
#[k::constructors(sort = BlockProgram, result = KResult)]
#[k::precedence((ProgramEmpty, ProgramCons))]
pub enum Program {
    #[k::syntax(".BlockProgram")]
    ProgramEmpty(),
    #[k::syntax("blockEntry({index}, {block}, {tail})")]
    ProgramCons {
        index: Int,
        block: BasicBlock,
        tail: BlockProgram,
    },
}

#[k::constructors(sort = RetVal, result = KResult)]
#[k::precedence((NoReturn, Returned))]
pub enum ReturnValue {
    #[k::syntax("noReturn")]
    NoReturn(),
    #[k::syntax("return({value})")]
    Returned { value: MirValue },
}

#[k::constructors(sort = Continuation, result = KResult)]
#[k::precedence((StoreAt, AddRight, FinishAdd, SelectBool))]
pub enum EvaluationContinuation {
    #[k::syntax("#storeAt({local})")]
    StoreAt { local: Int },
    #[k::syntax("#addRight({local}, {rhs})")]
    AddRight { local: Int, rhs: Operand },
    #[k::syntax("#finishAdd({local}, {lhs})")]
    FinishAdd { local: Int, lhs: Int },
    #[k::syntax("#selectBool({true_target}, {false_target})")]
    SelectBool { true_target: Int, false_target: Int },
}

#[k::constructors(sort = Command, result = KResult)]
#[k::precedence((
    Run,
    Install,
    ExecBlockIdx,
    ExecBlock,
    ExecStmts,
    ExecStmt,
    EvalRvalue,
    EvalOperand,
    Continue,
    SetLocalValue,
    ExecTerminator,
    EndProgram,
))]
pub enum Execution {
    #[k::syntax("run")]
    Run(),
    #[k::syntax("#installBlocks({program})")]
    Install { program: BlockProgram },
    #[k::syntax("#execBlockIdx({index})")]
    ExecBlockIdx { index: Int },
    #[k::syntax("#execBlock({block})")]
    ExecBlock { block: BasicBlock },
    #[k::syntax("#execStmts({statements})")]
    ExecStmts { statements: Statements },
    #[k::syntax("#execStmt({statement})")]
    ExecStmt { statement: Statement },
    #[k::syntax("#evalRvalue({value}, {local})")]
    EvalRvalue { value: Rvalue, local: Int },
    #[k::syntax("#evalOperand({operand}, {continuation})")]
    EvalOperand {
        operand: Operand,
        continuation: Continuation,
    },
    #[k::syntax("#continue({value}, {continuation})")]
    Continue {
        value: MirValue,
        continuation: Continuation,
    },
    #[k::syntax("#setLocalValue({local}, {value})")]
    SetLocalValue { local: Int, value: MirValue },
    #[k::syntax("#execTerminator({terminator})")]
    ExecTerminator { terminator: Terminator },
    #[k::syntax("#EndProgram")]
    EndProgram(),
}

/// Operational state selected from KMIR's nested configuration.
#[k::configuration]
pub struct Machine {
    #[k::cell(name = "k")]
    pub k: KSequence,
    #[k::cell(name = "program")]
    pub program: BlockProgram,
    #[k::cell(name = "blocks")]
    pub blocks: Map<Int, BasicBlock>,
    #[k::cell(name = "locals")]
    pub locals: Map<Int, MirValue>,
    #[k::cell(name = "retVal")]
    pub ret_val: RetVal,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] command: KSequence,
        #[k::config_var(name = "PROGRAM")] program: BlockProgram,
        #[k::config_var(name = "BLOCKS")] blocks: Map<Int, BasicBlock>,
        #[k::config_var(name = "LOCALS")] locals: Map<Int, MirValue>,
        #[k::config_var(name = "RETVAL")] ret_val: RetVal,
    ) -> Self {
        Self {
            k: k::k![command],
            program,
            blocks,
            locals,
            ret_val,
        }
    }
}

k::rules! {
    for Machine;

    begin: {
        k: [Execution::Run(), ..],
        program: program,
    } => {
        k: [Execution::Install(program), ..],
        program: Program::ProgramEmpty(),
    }
    where program: BlockProgram;

    install_block: {
        k: [Execution::Install(Program::ProgramCons { index, block, tail }), ..],
        blocks: blocks,
    } => {
        k: [Execution::Install(tail), ..],
        blocks: map::update(blocks, index, block),
    }
    where index: Int, block: BasicBlock, tail: BlockProgram;

    install_done: {
        k: [Execution::Install(Program::ProgramEmpty()), ..],
    } => {
        k: [Execution::ExecBlockIdx(0), ..],
    };

    lookup_block: {
        k: [Execution::ExecBlockIdx(index), ..],
        blocks: { index -> block, .. },
    } => {
        k: [Execution::ExecBlock(block), ..],
    }
    where index: Int;

    exec_block: {
        k: [Execution::ExecBlock(BlockSyntax::Block { statements, terminator }), ..],
    } => {
        k: [Execution::ExecStmts(statements), Execution::ExecTerminator(terminator), ..],
    }
    where statements: Statements, terminator: Terminator;

    statements_done: {
        k: [Execution::ExecStmts(StatementList::StatementsEmpty()), ..],
    } => {
        k: [..],
    };

    statements_cons: {
        k: [Execution::ExecStmts(StatementList::StatementsCons { head, tail }), ..],
    } => {
        k: [Execution::ExecStmt(head), Execution::ExecStmts(tail), ..],
    }
    where head: Statement, tail: Statements;

    assign: {
        k: [Execution::ExecStmt(MirStatement::Assign { local, value }), ..],
    } => {
        k: [Execution::EvalRvalue { value, local }, ..],
    }
    where local: Int, value: Rvalue;
}

k::rules! {
    for Machine;

    eval_use: {
        k: [Execution::EvalRvalue { value: MirRvalue::Use(operand), local }, ..],
    } => {
        k: [Execution::EvalOperand { operand, continuation: EvaluationContinuation::StoreAt(local) }, ..],
    }
    where operand: Operand, local: Int;

    eval_add: {
        k: [Execution::EvalRvalue { value: MirRvalue::Add { lhs, rhs }, local }, ..],
    } => {
        k: [Execution::EvalOperand { operand: lhs, continuation: EvaluationContinuation::AddRight { local, rhs } }, ..],
    }
    where lhs: Operand, rhs: Operand, local: Int;

    eval_constant: {
        k: [Execution::EvalOperand { operand: MirOperand::Constant(value), continuation }, ..],
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    }
    where value: MirValue, continuation: Continuation;

    eval_copy: {
        k: [Execution::EvalOperand { operand: MirOperand::Copy(local), continuation }, ..],
        locals: { local -> value, .. },
    } => {
        k: [Execution::Continue { value, continuation }, ..],
    }
    where local: Int, continuation: Continuation;

    continue_store: {
        k: [Execution::Continue { value, continuation: EvaluationContinuation::StoreAt(local) }, ..],
    } => {
        k: [Execution::SetLocalValue { local, value }, ..],
    }
    where value: MirValue, local: Int;

    continue_add_right: {
        k: [Execution::Continue { value: Value::Integer(lhs), continuation: EvaluationContinuation::AddRight { local, rhs } }, ..],
    } => {
        k: [Execution::EvalOperand { operand: rhs, continuation: EvaluationContinuation::FinishAdd { local, lhs } }, ..],
    }
    where lhs: Int, local: Int, rhs: Operand;

    continue_finish_add: {
        k: [Execution::Continue { value: Value::Integer(rhs), continuation: EvaluationContinuation::FinishAdd { local, lhs } }, ..],
    } => {
        k: [Execution::SetLocalValue { local, value: Value::Integer(int::add(lhs, rhs)) }, ..],
    }
    where lhs: Int, rhs: Int, local: Int;

    set_local_value: {
        k: [Execution::SetLocalValue { local, value }, ..],
        locals: locals,
    } => {
        k: [..],
        locals: map::update(locals, local, value),
    }
    where value: MirValue, local: Int;
}

k::rules! {
    for Machine;

    goto: {
        k: [Execution::ExecTerminator(MirTerminator::Goto(target)), ..],
    } => {
        k: [Execution::ExecBlockIdx(target), ..],
    }
    where target: Int;

    switch_int: {
        k: [Execution::ExecTerminator(MirTerminator::SwitchInt { discr, true_target, false_target }), ..],
    } => {
        k: [Execution::EvalOperand { operand: discr, continuation: EvaluationContinuation::SelectBool { true_target, false_target } }, ..],
    }
    where discr: Operand, true_target: Int, false_target: Int;

    select_true: {
        k: [Execution::Continue { value: Value::Boolean(true), continuation: EvaluationContinuation::SelectBool { true_target, false_target: _ } }, ..],
    } => {
        k: [Execution::ExecBlockIdx(true_target), ..],
    }
    where true_target: Int;

    select_false: {
        k: [Execution::Continue { value: Value::Boolean(false), continuation: EvaluationContinuation::SelectBool { true_target: _, false_target } }, ..],
    } => {
        k: [Execution::ExecBlockIdx(false_target), ..],
    }
    where false_target: Int;

    top_level_return: {
        k: [Execution::ExecTerminator(MirTerminator::Return()), ..],
        locals: { 0 -> value, .. },
        ret_val: ReturnValue::NoReturn(),
    } => {
        k: [Execution::EndProgram(), ..],
        ret_val: ReturnValue::Returned(value),
    };

    end_program: {
        k: [Execution::EndProgram(), ..],
    } => {
        k: [..],
    };
}

/// All-path claim spanning body installation, local dataflow, graph control, and return.
#[k::claim(all_paths, label = "install-add-switch-return")]
fn install_add_switch_return(
    k::cells! {
        k: k::configuration::KCell(Execution::Run()),
        program: k::configuration::Cell(Program::ProgramCons(
            0,
            BlockSyntax::Block(
                StatementList::StatementsCons(
                    MirStatement::Assign(1, MirRvalue::Use(MirOperand::Constant(Value::Integer(20)))),
                    StatementList::StatementsCons(
                        MirStatement::Assign(2, MirRvalue::Use(MirOperand::Constant(Value::Integer(22)))),
                        StatementList::StatementsCons(
                            MirStatement::Assign(3, MirRvalue::Add(MirOperand::Copy(1), MirOperand::Copy(2))),
                            StatementList::StatementsCons(
                                MirStatement::Assign(4, MirRvalue::Use(MirOperand::Constant(Value::Boolean(true)))),
                                StatementList::StatementsEmpty(),
                            ),
                        ),
                    ),
                ),
                MirTerminator::Goto(1),
            ),
            Program::ProgramCons(
                1,
                BlockSyntax::Block(
                    StatementList::StatementsEmpty(),
                    MirTerminator::SwitchInt(MirOperand::Copy(4), 2, 3),
                ),
                Program::ProgramCons(
                    2,
                    BlockSyntax::Block(
                        StatementList::StatementsCons(
                            MirStatement::Assign(0, MirRvalue::Use(MirOperand::Copy(3))),
                            StatementList::StatementsEmpty(),
                        ),
                        MirTerminator::Return(),
                    ),
                    Program::ProgramCons(
                        3,
                        BlockSyntax::Block(
                            StatementList::StatementsCons(
                                MirStatement::Assign(0, MirRvalue::Use(MirOperand::Constant(Value::Integer(0)))),
                                StatementList::StatementsEmpty(),
                            ),
                            MirTerminator::Return(),
                        ),
                        Program::ProgramEmpty(),
                    ),
                ),
            ),
        )),
        blocks: k::configuration::Cell(map![.Map]),
        locals: k::configuration::Cell(map![.Map]),
        ret_val: k::configuration::Cell(ReturnValue::NoReturn()),
    }: Machine,
) -> Machine {
    k::cells! {
        k: k::configuration::KCell(.K),
        program: k::configuration::Cell(Program::ProgramEmpty()),
        blocks: k::configuration::Cell(map![
            0 -> BlockSyntax::Block(
                StatementList::StatementsCons(
                    MirStatement::Assign(1, MirRvalue::Use(MirOperand::Constant(Value::Integer(20)))),
                    StatementList::StatementsCons(
                        MirStatement::Assign(2, MirRvalue::Use(MirOperand::Constant(Value::Integer(22)))),
                        StatementList::StatementsCons(
                            MirStatement::Assign(3, MirRvalue::Add(MirOperand::Copy(1), MirOperand::Copy(2))),
                            StatementList::StatementsCons(
                                MirStatement::Assign(4, MirRvalue::Use(MirOperand::Constant(Value::Boolean(true)))),
                                StatementList::StatementsEmpty(),
                            ),
                        ),
                    ),
                ),
                MirTerminator::Goto(1),
            ),
            1 -> BlockSyntax::Block(
                StatementList::StatementsEmpty(),
                MirTerminator::SwitchInt(MirOperand::Copy(4), 2, 3),
            ),
            2 -> BlockSyntax::Block(
                StatementList::StatementsCons(
                    MirStatement::Assign(0, MirRvalue::Use(MirOperand::Copy(3))),
                    StatementList::StatementsEmpty(),
                ),
                MirTerminator::Return(),
            ),
            3 -> BlockSyntax::Block(
                StatementList::StatementsCons(
                    MirStatement::Assign(0, MirRvalue::Use(MirOperand::Constant(Value::Integer(0)))),
                    StatementList::StatementsEmpty(),
                ),
                MirTerminator::Return(),
            ),
        ]),
        locals: k::configuration::Cell(map![
            0 -> Value::Integer(42),
            1 -> Value::Integer(20),
            2 -> Value::Integer(22),
            3 -> Value::Integer(42),
            4 -> Value::Boolean(true),
        ]),
        ret_val: k::configuration::Cell(ReturnValue::Returned(Value::Integer(42))),
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
            "KRS-KMIR",
            env!("CARGO_PKG_NAME"),
            env!("CARGO_PKG_VERSION"),
            "workspace",
            "krs_kmir_semantics",
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"),
        )
        .expect("valid package context")
    }

    #[test]
    fn readable_kmir_slice_collects_and_lowers_deterministically() {
        let descriptors = k::host_descriptors().collect::<Vec<_>>();
        let first = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.clone(),
            &k::builtin_registry(),
        )
        .expect("KMIR slice lowers");
        let second = collect_host_descriptors_with_builtins(
            [package_context()],
            descriptors.into_iter().rev(),
            &k::builtin_registry(),
        )
        .expect("KMIR slice lowers twice");
        assert_eq!(
            first.to_canonical_json().unwrap(),
            second.to_canonical_json().unwrap()
        );
        let semantic = lower_descriptor_bundle(&first).expect("KMIR descriptors lower");
        let definition = lower_semantic_theory(&semantic).expect("KMIR theory lowers");
        let source = emit_k(&definition).expect("KMIR definition emits");
        assert!(source.source().contains("<blocks>"));
        assert!(source.source().contains("<locals>"));
        assert!(source.source().contains("#execBlockIdx"));
        assert!(source.source().contains("switchInt"));
        assert!(source.source().contains("#EndProgram"));
    }
}
