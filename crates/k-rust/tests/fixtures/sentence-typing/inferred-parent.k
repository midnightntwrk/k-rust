module INFERRED-PARENT
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax KItem ::= h(K) | g(Int)
  rule [ite]: h(X) => g(#if X ==K 0 #then {X}:>Int #else 0 #fi)
  rule [equals]: { C #Equals { C }:>Int } => #Exists I1. { C #Equals I1:Int } [simplification]
endmodule
