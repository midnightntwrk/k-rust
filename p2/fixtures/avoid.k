module P2-AVOID
  syntax Exp ::= "true" [symbol(true)] | "false" [symbol(false)]
  syntax Stmt ::= "if" "(" Exp ")" Stmt             [symbol(ifThen)]
                | "if" "(" Exp ")" Stmt "else" Stmt [symbol(ifThenElse), avoid]
                | "{" "}"                            [symbol(block)]

  configuration <k> $PGM:Stmt </k>
endmodule
