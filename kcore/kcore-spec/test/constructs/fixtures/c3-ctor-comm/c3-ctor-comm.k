module C3-CTOR-COMM
  syntax Exp ::= ".E" [symbol(.E)] | "x" [symbol(x)] | Exp "+" Exp [comm, symbol(plus)]
endmodule
