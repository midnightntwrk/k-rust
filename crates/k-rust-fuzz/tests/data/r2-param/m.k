// The mutant of r2-param/b.k: it adds the parametric subsort Nm ::= MInt{8}.

requires "domains.md"
module PM-SYNTAX
  imports DOMAINS-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Nm  ::= "x"
  syntax Exp ::= Nm | MInt{8}
  syntax Exp ::= f(Exp) [overload(f)]
  syntax Nm  ::= f(Nm)  [overload(f)]
  syntax Nm ::= MInt{8}
  syntax Pgm ::= go(Int)
endmodule
module PM
  imports PM-SYNTAX
  imports DOMAINS
  imports MINT
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => f(2p8) </s>
endmodule
