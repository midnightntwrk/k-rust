module PARAMETRIC
  imports BOOL
  imports INT
  syntax {S} S ::= sel(Bool, S, S) [function, symbol(sel)]
  rule sel(true, A, _) => A
  rule sel(false, _, B) => B
  rule sel(_, A, A) => A [simplification]
  syntax KItem ::= go(Int) [symbol(go)]
  rule <k> go(I) => go(sel(I >Int 0, I -Int 1, 0)) ... </k> requires I >Int 0
  configuration <k> $PGM:KItem </k>
endmodule
