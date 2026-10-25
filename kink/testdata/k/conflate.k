// EI-02b review regression (baseline): goPos and goNeg split go(c(I)) on I, so an
// execution of go(X:Box) narrows X to c(I) with a fresh I that k-rust prints as ExVarI<n>.
module CONFLATE-SYNTAX
  imports INT-SYNTAX
  syntax Box ::= c(Int) [symbol(c)]
  syntax Op ::= check(Int) [symbol(check)] | check2(Int) [symbol(check2)] | go(Box) [symbol(go)]
  syntax Prog ::= "done" [symbol(done)] | "fail" [symbol(fail)] | seq(Op, Prog) [symbol(seq)]
endmodule

module CONFLATE
  imports CONFLATE-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>
  rule [check]:      seq(check(J), P) => P requires J <=Int 0
  rule [checkFail]:  seq(check(J), _) => fail requires J >Int 0
  rule [check2]:     seq(check2(J), P) => P requires J >Int 0
  rule [check2Fail]: seq(check2(J), _) => fail requires J <=Int 0
  rule [goPos]: seq(go(c(I)), P) => P requires I >Int 0
  rule [goNeg]: seq(go(c(I)), P) => P requires I <=Int 0
endmodule
