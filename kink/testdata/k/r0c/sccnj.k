// A conjunctive function, ok: its one equation is a conjunction of terms that depend on no
// reading, and its andThenBool skips pd(X), which may be undefined. Applied at the top of go's
// condition, where both readings make the rule inapplicable when pd(X) is undefined, it makes no
// visit; applied in go's right-hand side, it is the second application of ok in the rule's
// places, which a reader of the written rule counts in the same order.
module SCCNJ-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | res(Bool) [symbol(res)]
endmodule
module SCCNJ
  imports SCCNJ-SYNTAX
  imports INT
  imports BOOL
  syntax Int ::= pd(Int) [function, symbol(pd)]
  syntax Bool ::= ok(Int) [function, symbol(ok)]
  configuration <k> $PGM:Prog </k>
  rule pd(X) => 0 -Int X requires X <Int 0
  rule ok(X) => X <Int 0 andThenBool pd(X) >Int 0
  rule [go]: <k> go(I) => res(ok(I)) </k> requires ok(I)
endmodule
