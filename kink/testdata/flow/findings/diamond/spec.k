module DIA-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Bot  ::= "b"
  syntax Id2  ::= Bot | "x"
  syntax Val  ::= Bot | Int
  syntax Exp  ::= Id2 | Val
  syntax Bots ::= List{Bot,","}
  syntax Ids  ::= List{Id2,","} [overload(Exps)]
  syntax Vals ::= List{Val,","} [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Ids  ::= Bots
  syntax Vals ::= Bots
  syntax Exps ::= Ids | Vals
  syntax Pgm  ::= go(Int)
endmodule
module DIA
  imports DIA-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> go(_) => .K </k> <s> _ => .Ids </s>
endmodule
