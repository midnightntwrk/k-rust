// VI-T13 B1: an unhooked Foo constructor carries a List element role.
module T13ROLE-SYNTAX
  imports INT-SYNTAX
  imports BASIC-K
  syntax Foo ::= mkFoo(Int) [symbol(mkFoo)]
  syntax Prog ::= start(Int) [symbol(start)] | chk(KItem) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T13ROLE
  imports T13ROLE-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>
  syntax LI [hook(LIST.List)]
  syntax LI ::= LI LI [function, total, left, assoc, symbol(_LI_), element(mkFoo), unit(.LI)]
  syntax LI ::= ".LI" [function, total, symbol(.LI)]
  rule [start]: start(I) => chk(mkFoo(I))
  rule [hit]: chk(F:Foo) => done(1)
  rule [range]: chk(X:KItem) => done(7) requires X ==K X [priority(60)]
  rule [rangeow]: chk(_) => done(0) [owise]
endmodule
