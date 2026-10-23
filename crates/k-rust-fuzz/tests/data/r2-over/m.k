// The mutant of r2-over/b.k: it stores 2.

module KP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp ::= Int
  syntax Foo ::= f(K)   [overload(f)]
  syntax Foo ::= f(Exp) [overload(f)]
  syntax Pgm ::= go(Int)
endmodule
module KP
  imports KP-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => 2 </s>
endmodule
