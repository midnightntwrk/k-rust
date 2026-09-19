module SIMPLE-PRINT-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Exp ::= Int | String | "choose"
  syntax Exps ::= List{Exp, ","} [overload(Exps), strict]
  syntax Val
  syntax Vals ::= List{Val, ","} [overload(Exps)]
  syntax Stmt ::= "print" "(" Exps ")" ";" [strict]
endmodule

module SIMPLE-PRINT
  imports SIMPLE-PRINT-SYNTAX
  imports DOMAINS

  syntax Val ::= Int | String
  syntax Exp ::= Val
  syntax Exps ::= Vals
  syntax KResult ::= Val | Vals

  configuration <k> $PGM:Stmt </k> <output stream="stdout"> .List </output>

  rule choose => 1
  rule choose => 2
  rule <k> print(V:Val, Es:Vals => Es); ...</k>
       <output>... .List => ListItem(V) </output>
  rule print(.Vals); => .K
endmodule
