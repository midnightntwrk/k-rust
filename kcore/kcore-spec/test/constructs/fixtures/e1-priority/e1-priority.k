module E1-PRIORITY
  imports INT
  syntax Exp ::= Int
               | Exp "*" Exp                [symbol(mul), group(mulg)]
               | Exp "+" Exp                [symbol(plus), group(plusg)]
               | Exp "^" Exp                [symbol(pow)]
               | Exp "==" Exp               [symbol(eq)]
  syntax priority mulg > plusg
  syntax left mul plus
  syntax right pow
  syntax non-assoc eq
endmodule
