module E1-LEXICAL
  imports INT
  syntax lexical Lower = r"[a-z]"
  syntax Name ::= r"{Lower}[a-z0-9]*"       [token]
  syntax Num = Int
  syntax Num ::= twice(Num)                 [function, symbol(twice)]
  rule twice(N) => N *Int 2
endmodule
