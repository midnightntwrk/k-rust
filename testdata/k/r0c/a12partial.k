// Re-pin R0c deliverable 4 (finding A-12): `mydiv` is a hooked division declared partial; the
// two definitions differ in nothing else. `go(X)` steps to `done(X)` when `mydiv(X, 0)` is 1,
// which the partial definition's definedness makes impossible and the total one does not.
module A12-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= mydiv(Int, Int) [function, hook(INT.tdiv), smt-hook(div), symbol(mydiv)]
  syntax Op ::= go(Int) [symbol(go)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
                | done(Int) [symbol(done)]
endmodule

module A12
  imports A12-SYNTAX
  imports INT
  imports BOOL
  imports BASIC-K
  configuration <k> .K </k>

  rule [go]: seq(go(X), _) => done(X) requires mydiv(X, 0) ==Int 1
endmodule
