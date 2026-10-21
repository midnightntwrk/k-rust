// A user declaration copies domains.md's INT.add hook and signature.
module T13NATURAL-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)] | chk(Int) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T13NATURAL
  imports T13NATURAL-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>
  syntax Int ::= addNatural(Int, Int) [function, total, hook(INT.add), symbol(addNatural)]
  rule [start]: start(I) => chk(addNatural(I, I))
  rule [hit]: chk(0) => done(1)
  rule [ow]: chk(_) => done(0) [owise]
endmodule
