// The mutant of `kp.k` (FZ-DATAEND review B1): it adds `Exp ::= Bar`, so `f(bar ~> .K)` lowers
// to `f(bar)` at `Exp`.

module KP-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp ::= Int | Bar
  syntax Bar ::= "bar"
  syntax Foo ::= f(K)   [overload(f)]
  syntax Foo ::= f(Exp) [overload(f)]
  syntax Pgm ::= go(Int)
endmodule
module KP
  imports KP-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => f(bar ~> .K) </s>
endmodule
