//! Shared execution orchestration and the CLI result contract (S13 and S14).

use k_rust_backend::{
    definition::BackendDefinition,
    rewrite::{ExecutionOptions, ExecutionResult, Pattern, execute_with_solver},
    smt::SmtSolver,
};

/// Execute one already-internalized pattern with the facade's cached solver.
pub fn run(
    definition: &BackendDefinition,
    initial: Pattern,
    options: ExecutionOptions,
    solver: &dyn SmtSolver,
) -> ExecutionResult {
    execute_with_solver(definition, initial, options, solver)
}
