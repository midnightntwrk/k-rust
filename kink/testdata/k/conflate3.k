module CONFLATE3-SYNTAX
  imports INT-SYNTAX
  syntax Box ::= c(Int) [symbol(c)]
  syntax Op ::= "new1" [symbol(new1)] | "burnNew" [symbol(burnNew)] | "new2" [symbol(new2)]
              | go1(Box) [symbol(go1)] | burn(Box) [symbol(burn)] | go(Box) [symbol(go)]
              | t1(Int) [symbol(t1)] | t(Int) [symbol(t)]
  syntax Prog ::= "done" [symbol(done)] | "fail" [symbol(fail)] | "fail2" [symbol(fail2)] | seq(Op, Prog) [symbol(seq)]
endmodule

module CONFLATE3
  imports CONFLATE3-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>
  rule [new1]:    seq(new1, P) => seq(go1(?B:Box), P)
  rule [go1]:     seq(go1(c(I1)), P) => seq(t1(I1), P)
  rule [t1Pos]:   seq(t1(J), P) => P requires J <=Int 0
  rule [t1Neg]:   seq(t1(J), _) => fail requires J >Int 0
  rule [burnNew]: seq(burnNew, P) => seq(burn(?B:Box), P)
  rule [burn]:    seq(burn(c(Z)), P) => P
  rule [new2]:    seq(new2, P) => seq(go(?B:Box), P)
  rule [go]:      seq(go(c(I)), P) => seq(t(I), P)
  rule [tPos]:    seq(t(J), _) => done requires J >Int 0
  rule [tNeg]:    seq(t(J), _) => fail2 requires J <=Int 0
endmodule
