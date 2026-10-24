// KINK-OVERLOAD-VALUE review S1: a program emits one `tick` event per item, with its item as the
// payload. `tick-anywhere.k` makes the rule `c(1) => d` apply anywhere.
module TICK-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Foo ::= c(Int) [klabel(c), symbol] | "d" [klabel(d), symbol]
  syntax Pgm ::= tick(Foo, Pgm) [klabel(tick), symbol] | "done" [klabel(done), symbol]
endmodule
module TICK
  imports TICK-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>
  rule <k> tick(_, P) => P </k>
  rule c(1) => d [anywhere]
endmodule
