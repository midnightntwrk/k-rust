// KINK-SC-DEFINED (fz26 P7-SIMPLE-KINK review round 2, the reviewer's covered variant): the
// skippable pd(A) of f's #if also occurs in its condition, which every evaluation evaluates, so
// where the branch is skipped and pd(A) is undefined both readings are undefined: f is not
// flagged. f(-3) is 3 and f(3) is an undefined step in both readings.
module SCPDC-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | res(Int) [symbol(res)]
endmodule
module SCPDC
  imports SCPDC-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Int ::= pd(Int) [function, symbol(pd)] | f(Int) [function, symbol(f)]
  configuration <k> $PGM:Prog </k>
  rule pd(X) => 0 -Int X requires X <Int 0
  rule f(A) => #if pd(A) >Int 0 #then pd(A) #else 0 #fi
  rule [go]: <k> go(I) => res(f(I)) </k>
endmodule
