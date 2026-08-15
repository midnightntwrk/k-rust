module Z3-INFERENCE
  syntax Int ::= r"[0-9]+" [token]
  syntax Box ::= "box(" Int ")" [symbol(box)]
  syntax {S} S ::= "same(" S ")" [symbol(same)]
endmodule
