module SYMBOTTOM-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
                | stop(Int) [symbol(stop)]
                | apart(Int, Int) [symbol(apart)]
endmodule

module SYMBOTTOM
  imports SYMBOTTOM-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>

  rule [write]: seq(write(addr(A), V), P) => P
  rule [load]:  seq(load(addr(A), V), P) => P
  // `stop(1)` has no successor: its only rewrite is undefined (a `Trivial` leaf).
  rule [stop]:  stop(I) => halt ensures I <Int 0
  // Instances with A = B have an undefined-step Trivial leaf.
  rule [apart]: apart(A, B) => halt ensures A =/=Int B
endmodule
