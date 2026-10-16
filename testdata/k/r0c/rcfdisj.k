// Re-pin R0c (R0a review 1 minor; state-observations SO-09, attack (c)): an equation whose
// condition cannot be simplified, again at k-rust 501f18b9, where `rulecondfail.k`'s
// mismatched Float formats no longer fail (finding E-10). `f`'s condition calls `pick`, whose
// only equation is a simplification with two live alternatives (`X #Or 0`), so simplifying the
// condition fails with a disjunctive result: k-rust keeps the call `f(X)` unapplied and reports
// `RuleConditionFailed` for the attempt (k-rust simplify.rs `record_rule_condition_failure`,
// test `a_requires_with_a_disjunctive_result_records_the_rule_condition_failure`).
module RCFDISJ-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= f(Int) [function, symbol(f)]
               | pick(Int) [function, total, symbol(pick)]
  syntax Prog ::= run(Int) [symbol(run)]
                | done(Int) [symbol(done)]
                | "halt" [symbol(halt)]
endmodule

module RCFDISJ
  imports RCFDISJ-SYNTAX
  imports INT
  imports BOOL
  imports BASIC-K
  imports ML-SYNTAX
  configuration <k> .K </k>

  rule [pick]: pick(X) => X #Or 0 [simplification]
  rule [f]: f(X) => 1 requires pick(X) ==Int 2
  rule [run]: run(X) => done(f(X))
  rule [done]: done(_) => halt
endmodule
