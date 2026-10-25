// FZ-DATAEND review R2-S1: an unused overload placed across K (f(K)/f(Exp)) breaks only its own
// family. This baseline stores 1 and m.k stores 2: the ends hold kseq and dotk, which the family
// does not relate, so the case is a kill.

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
  rule <k> go(_) => .K </k> <s> _ => 1 </s>
endmodule
