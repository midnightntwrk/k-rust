// CS-15 spike: VI-T13 B1, an unhooked Foo constructor carries a List element role, kept in the
// final configuration.
module B1COLL-SYNTAX
  imports INT-SYNTAX
  imports BASIC-K
  syntax Foo ::= mkFoo(Int) [symbol(mkFoo)]
  syntax Prog ::= start(Int) [symbol(start)] | keep(KItem) [symbol(keep)]
  syntax LI [hook(LIST.List)]
  syntax LI ::= LI LI [function, total, left, assoc, symbol(_LI_), element(mkFoo), unit(.LI)]
  syntax LI ::= ".LI" [function, total, symbol(.LI)]
endmodule
module B1COLL
  imports B1COLL-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [start]: start(I) => keep(mkFoo(I))
endmodule
