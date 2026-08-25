// Negative oracle: the unexpected `+` token must be reported here.
module KRS-M2-INDUCED-RULE-ERROR
  syntax Bool ::= r"true" [token]
  syntax KItem
  syntax KResult
  syntax M2Obj ::= "foo" [symbol(foo)]
                 | "bar" [symbol(bar)]
  syntax KItem ::= KResult
  syntax KResult ::= M2Obj

  configuration <k> foo </k>

  rule foo => bar + foo
endmodule
