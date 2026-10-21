// state-observations SO-09, attack (c): an equation whose condition cannot be simplified.
// The baseline's `f` adds a double-precision literal to its double-precision argument. The
// audit's mutant writes the literal single-precision (`1.0f`), which the FLOAT hooks refuse
// (mismatched formats): k-rust keeps the call `f(X)` unevaluated and, since 7d3d8e69, reports a
// `RuleConditionFailed` diagnostic for the attempt.
module RULECONDFAIL-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  syntax Int ::= f(Float) [function, symbol(f)]
  syntax Prog ::= run(Float) [symbol(run)]
                | done(Int) [symbol(done)]
                | "halt" [symbol(halt)]
endmodule

module RULECONDFAIL
  imports RULECONDFAIL-SYNTAX
  imports INT
  imports FLOAT
  imports BOOL
  imports BASIC-K
  configuration <k> .K </k>

  rule [f]: f(X) => 1 requires X +Float 1.0 >Float 0.0
  rule [run]: run(X) => done(f(X))
  rule [done]: done(_) => halt
endmodule
