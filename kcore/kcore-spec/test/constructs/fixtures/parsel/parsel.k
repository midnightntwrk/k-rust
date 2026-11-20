// A sort-parametric function applied in a rule (as K's regression fixture kompile/parametric):
// kompile writes its equations at the sort K (`sel{K}`) and the rule's application at Int (`sel{Int}`).
module PARSEL-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
endmodule

module PARSEL
  imports PARSEL-SYNTAX
  imports BOOL
  imports INT
  syntax {S} S ::= sel(Bool, S, S) [function, symbol(sel)]
  rule sel(true, A, _) => A
  rule sel(false, _, B) => B
  syntax KItem ::= go(Int) [symbol(go)]
  rule <k> go(I) => go(sel(I >Int 0, I -Int 1, 0)) ... </k> requires I >Int 0
  configuration <k> $PGM:KItem </k>
endmodule
