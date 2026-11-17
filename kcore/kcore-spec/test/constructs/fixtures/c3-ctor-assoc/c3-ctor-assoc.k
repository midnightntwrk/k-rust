module C3-CTOR-ASSOC
  syntax Exp ::= ".E" [symbol(.E)] | "x" [symbol(x)] | Exp "+" Exp [assoc, symbol(plus)]
endmodule
