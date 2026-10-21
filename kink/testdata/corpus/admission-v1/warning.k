module CS12-WARNING
  imports BOOL
  configuration <k> $PGM:K </k>
  syntax Bool ::= opaque(Bool) [function, hook(KINKTEST.unimplemented), symbol(opaque)]
  rule true => false
endmodule
