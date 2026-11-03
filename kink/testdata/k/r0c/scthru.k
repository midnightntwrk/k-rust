// A cause chain through an operand: the rule go skips h(I) >Int 0 under andBool, and h(I) may be
// undefined because h's equation skips pd(A) under #if (as in scpd.k), so the chain names the
// andBool, then h with its equation, then the #if and pd(A).
module SCTHRU-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | res(Bool) [symbol(res)]
endmodule
module SCTHRU
  imports SCTHRU-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Int ::= pd(Int) [function, symbol(pd)] | h(Int) [function, symbol(h)]
  configuration <k> $PGM:Prog </k>
  rule pd(X) => 0 -Int X requires X <Int 0
  rule h(A) => #if A >=Int 0 #then A #else pd(A) #fi
  rule [go]: <k> go(I) => res(false andBool h(I) >Int 0) </k>
endmodule
