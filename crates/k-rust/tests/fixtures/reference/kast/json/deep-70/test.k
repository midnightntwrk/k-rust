module TEST-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp ::= Int | String | Id | Bool
               | Exp "+" Exp [left]
               | "(" Exp ")" [bracket]
               | "f" "(" Exps ")"
               | "g" "(" Exp ")"
               | "#h" "(" Exp ")"
  syntax Exps ::= List{Exp, ","}
  syntax Stmt ::= Exp ";"
  syntax Pgm ::= Stmt | Pgm Pgm [left]
endmodule
module TEST
  imports TEST-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>
endmodule
