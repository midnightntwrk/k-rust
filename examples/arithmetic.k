module ARITHMETIC
  syntax Int ::= r"[0-9]+" [token]
  syntax Exp ::= Int
  syntax Exp ::= left: Exp "+" Exp [symbol(plus)]
endmodule
