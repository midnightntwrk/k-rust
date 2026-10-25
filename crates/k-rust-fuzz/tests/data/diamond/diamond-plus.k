// The other side of the diamond pair: `go(N)` ends at `d(N +Int 1)` in one step, reading nothing.

module DIAMOND-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module DIAMOND
  imports DIAMOND-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  syntax KItem ::= b(Int) | c(Int) | d(Int)

  configuration <k> $PGM:Pgm </k>

  rule [go]: <k> go(N) => d(N +Int 1) ... </k>
endmodule
