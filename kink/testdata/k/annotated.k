// One variable written with and without a sort. The loader writes `put`'s `A:Nat` and
// `get`'s bare `A` alike, as the variable under a `Nat` cast, so a join that binds `A` in
// both rules meets a cast on one side and the variable under it on the other.
module ANNOTATED-SYNTAX
  syntax Nat ::= "z" [symbol(z)]
               | s(Nat) [symbol(s)]
  syntax State ::= put(Nat) [symbol(put)]
                 | kept(Nat) [symbol(kept)]
                 | get(Nat) [symbol(get)]
                 | got(Nat) [symbol(got)]
endmodule

module ANNOTATED
  imports ANNOTATED-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [put]: put(A:Nat) => kept(A)
  rule [get]: get(A) => got(A)
endmodule
