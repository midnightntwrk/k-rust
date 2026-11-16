module E2-TOKEN
  syntax Name [token]
  syntax Word ::= r"[a-z]+"                          [token, prec(2)]
  syntax Exp ::= n(Name) [symbol(n)] | w(Word) [symbol(w)]
endmodule
