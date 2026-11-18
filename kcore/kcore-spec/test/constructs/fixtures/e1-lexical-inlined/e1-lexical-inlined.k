module E1-LEXICAL-INLINED
  imports INT
  syntax Name ::= r"[a-z][a-z0-9]*"         [token]
  syntax Num = Int
  syntax Num ::= twice(Num)                 [function, symbol(twice)]
  rule twice(N) => N *Int 2
endmodule
