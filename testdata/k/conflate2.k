module CONFLATE2-SYNTAX
  imports INT-SYNTAX
  syntax Box ::= c(Int) [symbol(c)]
  syntax Op ::= check(Int) [symbol(check)] | mk() [symbol(mk)] | go(Box) [symbol(go)] | t(Int) [symbol(t)]
  syntax Prog ::= "done" [symbol(done)] | "fail" [symbol(fail)] | "fail2" [symbol(fail2)] | seq(Op, Prog) [symbol(seq)]
endmodule

module CONFLATE2
  imports CONFLATE2-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>
  rule [check]:     seq(check(J), P) => P requires J <=Int 0
  rule [checkFail]: seq(check(J), _) => fail requires J >Int 0
  rule [mk]:        seq(mk(), P) => seq(go(?B:Box), P)
  rule [go]:        seq(go(c(I)), P) => seq(t(I), P)
  rule [tPos]:      seq(t(J), _) => done requires J >Int 0
  rule [tNeg]:      seq(t(J), _) => fail2 requires J <=Int 0
endmodule
