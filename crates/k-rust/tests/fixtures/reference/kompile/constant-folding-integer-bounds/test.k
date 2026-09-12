module MAIN
  syntax Int [hook(INT.Int)]
  syntax Int ::= r"[\\+\\-]?[0-9]+" [token]
  syntax Int ::= "result" [function, symbol(result)]
  syntax Int ::= Int ">>Int" Int [function, hook(INT.shr), symbol(shrInt)]
  rule result => 0 >>Int 2147483648
endmodule
