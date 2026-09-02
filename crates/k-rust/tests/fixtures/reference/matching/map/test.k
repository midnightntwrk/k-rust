module TEST
  imports MAP
  imports SET
  imports INT
  syntax Pgm ::= "go" [symbol(go)] | "done" [symbol(done)] | "gos" [symbol(gos)] | "dones" [symbol(dones)]
  configuration <k> $PGM:Pgm </k> <m> .Map </m> <s> .Set </s>
  rule <k> go => done </k> <m> (_K |-> _V) REST => REST </m> [label(mapsel)]
  rule <k> gos => dones </k> <s> SetItem(1) => .Set </s> [label(setclosed)]
endmodule
