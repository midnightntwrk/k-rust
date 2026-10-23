// FZ-DATAEND review R2-B2 (pre-existing: main kills it): the family f(Exp)/f(Nm) with Bot < Nm
// < Exp. This baseline ends at f_Nm(inj{Bot,Nm}(b)), f_Nm being its least member and so a free
// constructor; m.k adds the member f(Bot), and its axiom f_Nm(inj{Bot,Nm}(X)) = inj(f_Bot(X))
// makes the two ends one value of the mutant.

module AM-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Bot ::= "b"
  syntax Nm  ::= Bot | "x"
  syntax Exp ::= Nm | Int
  syntax Exp ::= f(Exp) [overload(f)]
  syntax Nm  ::= f(Nm)  [overload(f)]

  syntax Pgm ::= go(Int)
endmodule
module AM
  imports AM-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => f(b) </s>
endmodule
