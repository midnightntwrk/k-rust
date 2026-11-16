// `parsym.k` with the sort-parametric function applied in a rule: its instance `pair{C}` is read, a parameter (no equation).
module PARSYM-APP-SYNTAX
  syntax A ::= "a" [symbol(a)]
  syntax B ::= "b" [symbol(b)]
  syntax C ::= A | B
  syntax {S} S ::= pair(S, S) [symbol(pair), function]
  syntax Cmd ::= go() [symbol(go)] | pick(C) [symbol(pick)]
endmodule

module PARSYM-APP
  imports PARSYM-APP-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule [go]: <k> go() => pick(pair(a, b)) </k>
endmodule
