// VI-T12 probe: MInt literal spelling (rule-literal to rule-literal).
module T12MINT-SYNTAX
  imports INT-SYNTAX
  imports MINT-SYNTAX
  syntax MInt{8}
  syntax Prog ::= done(Int) [symbol(done)]
  syntax Prog ::= m1s(Int) [symbol(m1s)] | m1c(MInt{8}) [symbol(m1c)]
endmodule
module T12MINT
  imports T12MINT-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports MINT
  configuration <k> .K </k>
  rule [m1s]: m1s(_) => m1c(1p8)
  rule [m1p]: m1c(1p8) => done(7)
  rule [m1o]: m1c(_) => done(0) [owise]
endmodule
