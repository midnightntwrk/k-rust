module E2-OPEN-CTOR-ARG
  syntax Exp ::= "x" [symbol(x)] | s(Exp) [symbol(s)] | Exp "&" Exp [comm, symbol(and)]
endmodule
