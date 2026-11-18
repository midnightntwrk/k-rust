module E1-LEXICAL-SYNONYM
  imports INT
  syntax lexical Lower = r"[a-z]"
  syntax Name ::= r"{Lower}[a-z0-9]*"       [token]
  syntax Int ::= twice(Int)                 [function, symbol(twice)]
  rule twice(N) => N *Int 2
endmodule
