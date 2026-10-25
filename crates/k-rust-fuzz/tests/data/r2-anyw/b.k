// FZ-DATAEND review R2-B2, without overloads (pre-existing: main kills it): this baseline ends at
// c(1), a free constructor term; m.k adds the anywhere rule c(1) => d, so its end d is c(1) in the
// mutant's theory.

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

endmodule
