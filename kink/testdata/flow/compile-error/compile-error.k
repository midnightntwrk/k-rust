// Flow fixture (F-02): loads, but does not compile (a hooked constant with no
// arguments, as testdata/corpus/admission-v1/compile-error.k); `kink-flow check`
// refuses the spec at stage `compile`.
module FLOW-COMPILE-ERROR
  imports BOOL
  configuration <k> $PGM:K </k>
  syntax Bool ::= "bad" [hook(BOOL.not), symbol(bad)]
  rule true => false
endmodule
