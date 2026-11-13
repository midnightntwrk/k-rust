// The Int and Bool hooks of the fragment, on negative operands too (truncating /Int and %Int).
module CASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax S ::= go(Int, Int) | r(Int, Int, Int, Int, Int) | q(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:S </k>
  rule <k> go(X, Y) => r(X +Int Y, X -Int Y, X *Int Y, X /Int Y, X %Int Y) </k> requires X <Int 0
  rule <k> r(A, B, C, D, E) => q(A <Int B, A <=Int B, C >Int D, C >=Int D, D ==Int E, D =/=Int E,
                                 A <Int B andBool C >Int D, A >Int B orBool C <Int D, notBool (E ==Int 0)) </k>
    requires #if A >Int 0 #then false #else true #fi
endmodule
