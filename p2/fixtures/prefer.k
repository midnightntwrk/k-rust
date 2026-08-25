module P2-PREFER
  syntax Exp ::= "true" [symbol(true)] | "false" [symbol(false)]
  syntax Stmt ::= "if" "(" Exp ")" Stmt             [symbol(ifThen), prefer]
                | "if" "(" Exp ")" Stmt "else" Stmt [symbol(ifThenElse)]
                | "{" "}"                            [symbol(block)]

  configuration <k> $PGM:Stmt </k>
endmodule
