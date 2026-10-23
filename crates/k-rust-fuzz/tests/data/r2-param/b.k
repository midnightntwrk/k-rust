// FZ-DATAEND review R2-B1: an overload family f(Exp)/f(Nm) with Exp ::= Nm | MInt{8}. This
// baseline stores f(2p8), the normal form f_Exp(inj{MInt{8},Exp}(2p8)); m.k adds Nm ::= MInt{8},
// where the same term lowers to inj(f_Nm(inj{MInt{8},Nm}(2p8))): one value of the mutant.
// Parametric sorts need Z3 sort inference, so the portable build does not compile this pair.

requires "domains.md"
module PM-SYNTAX
  imports DOMAINS-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Nm  ::= "x"
  syntax Exp ::= Nm | MInt{8}
  syntax Exp ::= f(Exp) [overload(f)]
  syntax Nm  ::= f(Nm)  [overload(f)]

  syntax Pgm ::= go(Int)
endmodule
module PM
  imports PM-SYNTAX
  imports DOMAINS
  imports MINT
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => f(2p8) </s>
endmodule
