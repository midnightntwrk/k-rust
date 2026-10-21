// EI-02b review regression (mutant): conflate.k with goPos and goNeg merged into one
// unguarded go rule; both definitions execute identically on every ground instance.
module CONFLATEM-SYNTAX
  imports INT-SYNTAX
  syntax Box ::= c(Int) [symbol(c)]
  syntax Op ::= check(Int) [symbol(check)] | check2(Int) [symbol(check2)] | go(Box) [symbol(go)]
  syntax Prog ::= "done" [symbol(done)] | "fail" [symbol(fail)] | seq(Op, Prog) [symbol(seq)]
endmodule

module CONFLATEM
  imports CONFLATEM-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>
  rule [check]:      seq(check(J), P) => P requires J <=Int 0
  rule [checkFail]:  seq(check(J), _) => fail requires J >Int 0
  rule [check2]:     seq(check2(J), P) => P requires J >Int 0
  rule [check2Fail]: seq(check2(J), _) => fail requires J <=Int 0
  rule [go]: seq(go(B), P) => P
endmodule
