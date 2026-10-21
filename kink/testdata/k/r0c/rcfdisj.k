// Re-pin R0c (R0a review 1 minor; state-observations SO-09, attack (c)): an equation whose
// condition cannot be simplified, again at k-rust 501f18b9, where `rulecondfail.k`'s
// mismatched Float formats no longer fail (finding E-10). `f`'s condition calls `pick`, whose
// only equation is a simplification with two live alternatives (`X #Or 0`), so simplifying the
// condition fails with a disjunctive result: k-rust keeps the call `f(X)` unapplied and reports
// `RuleConditionFailed` for the attempt (k-rust simplify.rs `record_rule_condition_failure`,
// test `a_requires_with_a_disjunctive_result_records_the_rule_condition_failure`).
//
// Re-pin P-2 (k-rust 8f8ad57c5; MLP/4b, head d5bead028, merge fede20744; k-rust's draft
// answers-add3 section 2.5 "MLP/4b" and workers/MLP-4b-report.md, "in equations an `#Or` with
// an unguarded alternative refused"): the unguarded `pick(X) => X #Or 0` is now refused at
// compile (stage "definition checks", "#Or where the simplification builds its result ... guard
// every alternative with a predicate"). Each alternative is now guarded, and both guards hold
// at every argument the tests use (X >=Int 1), so `pick(2)` still has two live alternatives, 2
// and 0, and the condition still fails with a disjunctive result. Measured at 8f8ad57c5 in both
// profiles: kink-native bridge.rs `audit_so_rule_condition_failed_leaf_is_never_complete` passes
// unchanged on this fixture (the same RuleConditionFailed leaves and rows).
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

  rule [pick]: pick(X) => ({X >=Int 0 #Equals true} #And X) #Or ({X >=Int 1 #Equals true} #And 0) [simplification]
  rule [f]: f(X) => 1 requires pick(X) ==Int 2
  rule [run]: run(X) => done(f(X))
  rule [done]: done(_) => halt
endmodule
