// CF-01: scmlat.k with each leaf's Bool term C = Y ==Int 0 orElseBool X /Int Y .. instead of an
// andThenBool tree. Where Y is 0 a short-circuiting backend gives C = true and k-rust's strict
// reading \bottom, so \equals(C, true) itself differs between the readings: the predicate-truth
// argument does not cover such a leaf, which keeps the operand-definedness analysis (X /Int Y is
// evaluated by no other operand and owes Y =/=Int 0 under the ceil theory). Every function, under
// its first equation and under its owise guard alone, and every rule, depends on the reading.
module SCMLOE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= go(Int, Int) [symbol(go)] | res(Int) [symbol(res)]
                | rand(Int, Int) [symbol(rand)] | ror(Int, Int) [symbol(ror)]
                | rnot(Int, Int) [symbol(rnot)] | rimp(Int, Int) [symbol(rimp)]
                | rex(Int, Int) [symbol(rex)] | rall(Int, Int) [symbol(rall)]
  syntax Int ::= cand(Int, Int) [function, symbol(cand)]
               | cor(Int, Int) [function, symbol(cor)]
               | cnot(Int, Int) [function, symbol(cnot)]
               | cimp(Int, Int) [function, symbol(cimp)]
               | cex(Int, Int) [function, symbol(cex)]
               | call(Int, Int) [function, symbol(call)]
endmodule
module SCMLOE
  imports SCMLOE-SYNTAX
  imports INT
  imports BOOL
  imports ML-SYNTAX
  configuration <k> $PGM:Prog </k>
  rule [cand1]: cand(X, Y) => 1 requires (X >=Int 0) #And (Y ==Int 0 orElseBool X /Int Y >Int 0)
  rule [cand2]: cand(_, _) => 0 [owise]
  rule [cor1]: cor(X, Y) => 1 requires (X >=Int 0) #Or (Y ==Int 0 orElseBool X /Int Y >Int 0)
  rule [cor2]: cor(_, _) => 0 [owise]
  rule [cnot1]: cnot(X, Y) => 1 requires #Not(Y ==Int 0 orElseBool X /Int Y >Int 0)
  rule [cnot2]: cnot(_, _) => 0 [owise]
  rule [cimp1]: cimp(X, Y) => 1 requires (Y ==Int 0 orElseBool X /Int Y >Int 0) #Implies (X >=Int 0)
  rule [cimp2]: cimp(_, _) => 0 [owise]
  rule [cex1]: cex(X, Y) => 1 requires #Exists Z:Int . (Y ==Int 0 orElseBool (X /Int Y ==Int Z andBool Z >Int 0))
  rule [cex2]: cex(_, _) => 0 [owise]
  rule [call1]: call(X, Y) => 1 requires #Forall Z:Int . (Y ==Int 0 orElseBool X /Int Y >Int Z)
  rule [call2]: call(_, _) => 0 [owise]
  rule [go]: <k> go(X, Y) => res(cand(X, Y) +Int cor(X, Y) +Int cnot(X, Y) +Int cimp(X, Y) +Int cex(X, Y) +Int call(X, Y)) </k>
  rule [rand]: <k> rand(X, Y) => res(1) </k> requires (X >=Int 0) #And (Y ==Int 0 orElseBool X /Int Y >Int 0)
  rule [ror]: <k> ror(X, Y) => res(1) </k> requires (X >=Int 0) #Or (Y ==Int 0 orElseBool X /Int Y >Int 0)
  rule [rnot]: <k> rnot(X, Y) => res(1) </k> requires #Not(Y ==Int 0 orElseBool X /Int Y >Int 0)
  rule [rimp]: <k> rimp(X, Y) => res(1) </k> requires (Y ==Int 0 orElseBool X /Int Y >Int 0) #Implies (X >=Int 0)
  rule [rex]: <k> rex(X, Y) => res(1) </k> requires #Exists Z:Int . (Y ==Int 0 orElseBool (X /Int Y ==Int Z andBool Z >Int 0))
  rule [rall]: <k> rall(X, Y) => res(1) </k> requires #Forall Z:Int . (Y ==Int 0 orElseBool X /Int Y >Int Z)
endmodule
