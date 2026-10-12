module CS12-COMPILE-ERROR
  imports BOOL
  configuration <k> $PGM:K </k>
  syntax Bool ::= "bad" [hook(BOOL.not), symbol(bad)]
  rule true => false
endmodule
