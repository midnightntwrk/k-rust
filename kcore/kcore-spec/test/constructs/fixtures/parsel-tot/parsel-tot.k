// A sort-parametric function declared total, applied in a rule at Int with its equation at K:
// kompile states the totality of every instance by one axiom quantified over the sort variable.
module PARSEL-TOT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
endmodule

module PARSEL-TOT
  imports PARSEL-TOT-SYNTAX
  imports BOOL
  imports INT
  syntax {S} S ::= idp(S) [function, total, symbol(idp)]
  rule idp(X) => X
  syntax KItem ::= go(Int) [symbol(go)]
  rule <k> go(I) => go(idp(I -Int 1)) ... </k> requires I >Int 0
  configuration <k> $PGM:KItem </k>
endmodule
