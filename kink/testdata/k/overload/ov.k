module OV-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp  ::= Int | Id
  syntax Ids  ::= List{Id,","}  [overload(Exps)]
  syntax Exps ::= List{Exp,","} [overload(Exps)]
  syntax Exps ::= Ids
  syntax Pgm  ::= "h" "(" Exps ")"
endmodule
module OV
  imports OV-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k> <s> .K </s>
  rule <k> h(Es) => .K </k> <s> _ => Es </s>
endmodule
