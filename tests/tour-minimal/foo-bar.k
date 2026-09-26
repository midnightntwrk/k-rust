// Hand-written reference semantics. This file is an input oracle, never
// generated from or updated to match a KRS adapter artifact.
module KRS-FOO-BAR
  // Portable k-rust uses this truth token without loading the full prelude.
  syntax Bool ::= r"true" [token]
  syntax KItem
  syntax KResult
  syntax ObjectTerm ::= "foo" [symbol(foo)]
                 | "bar" [symbol(bar)]
  syntax KItem ::= KResult
  syntax KResult ::= ObjectTerm

  configuration <k> foo </k>

  rule foo => bar
endmodule
