// The mutant of r2-addmember/b.k: it adds the overload member Bot ::= f(Bot).

module AM-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Bot ::= "b"
  syntax Nm  ::= Bot | "x"
  syntax Exp ::= Nm | Int
  syntax Exp ::= f(Exp) [overload(f)]
  syntax Nm  ::= f(Nm)  [overload(f)]
  syntax Bot ::= f(Bot) [overload(f)]
  syntax Pgm ::= go(Int)
endmodule
module AM
  imports AM-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => f(b) </s>
endmodule
