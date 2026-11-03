// CF-01: conditions whose \equals(C, true) leaves have a C that is a tree of andThenBool and
// andBool over atoms, under each matching-logic connective K writes (#And, #Or, #Not, #Implies,
// #Exists, #Forall; \iff, which K has no syntax for, is patched into cimp1's KORE by the test),
// and under the owise guard of each function, which negates the first equation's condition under
// \not, \or and \exists. The skippable operand X /Int Y is undefined where the program input Y
// is 0, but both readings make such a C true exactly where every atom is true (they differ only
// as false versus \bottom, and \equals(false, true) and \equals(\bottom, true) are both
// \bottom), so no leaf, no connective over it and no rule here depends on the reading. plain is
// Foldiboy's control: an owise over an andThenBool condition with X /Int Y.
module SCMLAT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= gp(Int, Int) [symbol(gp)] | go(Int, Int) [symbol(go)] | res(Int) [symbol(res)]
                | rand(Int, Int) [symbol(rand)] | ror(Int, Int) [symbol(ror)]
                | rnot(Int, Int) [symbol(rnot)] | rimp(Int, Int) [symbol(rimp)]
                | rex(Int, Int) [symbol(rex)] | rall(Int, Int) [symbol(rall)]
  syntax Int ::= plain(Int, Int) [function, symbol(plain)]
               | cand(Int, Int) [function, symbol(cand)]
               | cor(Int, Int) [function, symbol(cor)]
               | cnot(Int, Int) [function, symbol(cnot)]
               | cimp(Int, Int) [function, symbol(cimp)]
               | cex(Int, Int) [function, symbol(cex)]
               | call(Int, Int) [function, symbol(call)]
endmodule
module SCMLAT
  imports SCMLAT-SYNTAX
  imports INT
  imports BOOL
  imports ML-SYNTAX
  configuration <k> $PGM:Prog </k>
  rule [plain1]: plain(X, Y) => 1 requires X >=Int 0 andThenBool X /Int Y ==Int 0
  rule [plain2]: plain(_, _) => 0 [owise]
  rule [cand1]: cand(X, Y) => 1 requires (X >=Int 0) #And (Y =/=Int 0 andThenBool X /Int Y >Int 0)
  rule [cand2]: cand(_, _) => 0 [owise]
  rule [cor1]: cor(X, Y) => 1 requires (X >=Int 0) #Or (Y =/=Int 0 andThenBool X /Int Y >Int 0)
  rule [cor2]: cor(_, _) => 0 [owise]
  rule [cnot1]: cnot(X, Y) => 1 requires #Not(Y =/=Int 0 andThenBool X /Int Y >Int 0)
  rule [cnot2]: cnot(_, _) => 0 [owise]
  rule [cimp1]: cimp(X, Y) => 1 requires (Y =/=Int 0 andThenBool X /Int Y >Int 0) #Implies (X >=Int 0)
  rule [cimp2]: cimp(_, _) => 0 [owise]
  rule [cex1]: cex(X, Y) => 1 requires #Exists Z:Int . ((Y =/=Int 0 andThenBool X /Int Y ==Int Z) andBool Z >Int 0)
  rule [cex2]: cex(_, _) => 0 [owise]
  rule [call1]: call(X, Y) => 1 requires #Forall Z:Int . (Y =/=Int 0 andThenBool X /Int Y >Int Z)
  rule [call2]: call(_, _) => 0 [owise]
  rule [gp]: <k> gp(X, Y) => res(plain(X, Y)) </k>
  rule [go]: <k> go(X, Y) => res(cand(X, Y) +Int cor(X, Y) +Int cnot(X, Y) +Int cimp(X, Y) +Int cex(X, Y) +Int call(X, Y)) </k>
  rule [rand]: <k> rand(X, Y) => res(1) </k> requires (X >=Int 0) #And (Y =/=Int 0 andThenBool X /Int Y >Int 0)
  rule [ror]: <k> ror(X, Y) => res(1) </k> requires (X >=Int 0) #Or (Y =/=Int 0 andThenBool X /Int Y >Int 0)
  rule [rnot]: <k> rnot(X, Y) => res(1) </k> requires #Not(Y =/=Int 0 andThenBool X /Int Y >Int 0)
  rule [rimp]: <k> rimp(X, Y) => res(1) </k> requires (Y =/=Int 0 andThenBool X /Int Y >Int 0) #Implies (X >=Int 0)
  rule [rex]: <k> rex(X, Y) => res(1) </k> requires #Exists Z:Int . ((Y =/=Int 0 andThenBool X /Int Y ==Int Z) andBool Z >Int 0)
  rule [rall]: <k> rall(X, Y) => res(1) </k> requires #Forall Z:Int . (Y =/=Int 0 andThenBool X /Int Y >Int Z)
endmodule
