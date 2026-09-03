module BRACKET-SYMBOL
  imports INT
  syntax Exp ::= Int | "(" Exp ")" [bracket, symbol(paren)] | Exp "+" Exp [symbol(plus)]
endmodule
