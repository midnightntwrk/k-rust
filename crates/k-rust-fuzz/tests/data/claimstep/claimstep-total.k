// Mutant of claimstep.k: the guard of `go` is dropped and the division goes through `td`,
// declared `total` although its equation reduces `td(0)` to the undefined `10 /Int 0`. On
// `go(0)` the step applies (a total right-hand side carries no definedness obligation) and its
// successor's normalization finds `\bottom`: an undefined step whose leaf carries the
// contradicted `total` claim. The definition is inconsistent there, so the step is no evidence.

module CLAIMSTEP-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module CLAIMSTEP
  imports CLAIMSTEP-SYNTAX
  imports INT
  imports BOOL

  syntax Int ::= td(Int)  [function, total, symbol(td)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [tdeq]: td(I) => 10 /Int I
  rule [go]:   <k> go(N) => .K ... </k> <out> _ => td(N) </out>
endmodule
