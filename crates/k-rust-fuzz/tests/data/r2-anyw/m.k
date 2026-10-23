// The mutant of r2-anyw/b.k: it adds rule c(1) => d [anywhere].

module AW-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Foo ::= c(Int) | "d"
  syntax Pgm ::= go(Int)
endmodule
module AW
  imports AW-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => c(1) </s>
  rule c(1) => d [anywhere]
endmodule
