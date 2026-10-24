// KINK-SC-DEFINED (fz26 P7-SIMPLE-KINK review B3, the reviewer's pd probe): pd is defined exactly
// on negatives, and f's #if skips pd(A) where A >=Int 0. pd(A) occurs in no other operand, so on
// f(3) k-rust's reading is undefined where a short-circuiting backend gives 3: f stays flagged.
module SCPD-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | res(Int) [symbol(res)]
endmodule
module SCPD
  imports SCPD-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Int ::= pd(Int) [function, symbol(pd)] | f(Int) [function, symbol(f)]
  configuration <k> $PGM:Prog </k>
  rule pd(X) => 0 -Int X requires X <Int 0
  rule f(A) => #if A >=Int 0 #then A #else pd(A) #fi
  rule [go]: <k> go(I) => res(f(I)) </k>
endmodule
