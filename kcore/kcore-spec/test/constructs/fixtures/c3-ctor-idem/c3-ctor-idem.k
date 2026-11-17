module C3-CTOR-IDEM
  syntax Exp ::= ".E" [symbol(.E)] | "x" [symbol(x)] | Exp "+" Exp [idem, symbol(plus)]
endmodule
