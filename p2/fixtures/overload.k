module P2-OVERLOAD
  imports ID

  syntax LVal ::= "L" "(" ")" [symbol(lval)]
  syntax Exp ::= "E" "(" ")" [symbol(exp)] | LVal
  syntax Exp ::= Exp "." Id   [symbol(expDot), overload(dot)]
  syntax LVal ::= LVal "." Id [symbol(lvalDot), overload(dot)]
  syntax KItem ::= "done" [symbol(done)]

  configuration <k> $PGM:Exp </k>

  rule _:LVal => done [label(infer-lval)]
endmodule
