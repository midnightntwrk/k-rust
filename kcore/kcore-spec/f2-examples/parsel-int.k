// As parsel.k, with the equations' variables at Int: kompile writes them at `sel{Int}`, the instance
// the rule applies.
module PARSEL-INT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
endmodule

module PARSEL-INT
  imports PARSEL-INT-SYNTAX
  imports BOOL
  imports INT
  syntax {S} S ::= sel(Bool, S, S) [function, symbol(sel)]
  rule sel(true, A:Int, _:Int) => A
  rule sel(false, _:Int, B:Int) => B
  syntax KItem ::= go(Int) [symbol(go)]
  rule <k> go(I) => go(sel(I >Int 0, I -Int 1, 0)) ... </k> requires I >Int 0
  configuration <k> $PGM:KItem </k>
endmodule
