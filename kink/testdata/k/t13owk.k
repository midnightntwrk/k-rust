// VI-T13 V4: INT.add places an Int in its declared Bool result position.
module T13OWK-SYNTAX
  imports INT-SYNTAX
  imports BASIC-K
  syntax Prog ::= start(Int) [symbol(start)] | chk(KItem) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T13OWK
  imports T13OWK-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>
  syntax Bool ::= addB(Int, Int) [function, total, hook(INT.add), symbol(addB)]
  rule [start]: start(I) => chk(addB(I, I))
  rule [t]: chk(true) => done(1)
  rule [f]: chk(false) => done(1)
  rule [range]: chk(X:KItem) => done(7) requires X ==K X [priority(60)]
  rule [rangeow]: chk(_) => done(0) [owise]
endmodule
