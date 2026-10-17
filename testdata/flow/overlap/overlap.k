// Flow fixture (re-pin R0c-fix-3): a function with two guarded equations. Widening `pos`'s guard
// to `I >=Int -5` makes `pos` and `neg` both apply to -1 with different values: the mutant has no
// model, so the mutation is invalid (`inconsistent-mutant`) and its row names the pair. An edit of
// the rewrite rule `sgn` changes no equation and runs.
module OVERLAP-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | sgn(Exp) [strict, symbol(sgnexp)]
endmodule

module OVERLAP
  imports OVERLAP-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  syntax Int ::= sign(Int) [function, symbol(sign)]
  rule [pos]: sign(I) => 1 requires I >=Int 0
  rule [neg]: sign(I) => -1 requires I <Int 0
  rule [sgn]: sgn(I:Int) => sign(I)
endmodule
