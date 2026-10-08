// A made-up hook has no backend implementation or kompile folding arm.
module T13INERT-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)] | chk(Int) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T13INERT
  imports T13INERT-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>
  syntax Int ::= inert(Int) [function, hook(INT.kinktestUnimplemented), symbol(inert)]
  rule [start]: start(I) => chk(inert(I))
  rule [hit]: chk(0) => done(1)
  rule [ow]: chk(_) => done(0) [owise]
endmodule
