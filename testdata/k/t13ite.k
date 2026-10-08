// VI-T13 V3': ite places an Int in its declared Bool result position.
module T13ITE-SYNTAX
  imports INT-SYNTAX
  imports BASIC-K
  syntax Prog ::= start(Int) [symbol(start)] | chk(KItem) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T13ITE
  imports T13ITE-SYNTAX
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>
  syntax Bool ::= i2b(Bool, Int, Int) [function, total, hook(KEQUAL.ite), symbol(i2b)]
  rule [start]: start(I) => chk(i2b(true, I, I))
  rule [t]: chk(true) => done(1)
  rule [f]: chk(false) => done(1)
  rule [range]: chk(X:KItem) => done(7) requires X ==K X [priority(60)]
  rule [rangeow]: chk(_) => done(0) [owise]
endmodule
