module E2-UNIT-CTOR
  syntax Exp ::= ".E" [symbol(.E)] | "x" [symbol(x)] | Exp "+" Exp [assoc, unit(.E), symbol(plus)]
endmodule
