// KWasm ListInt:get shape: LIST.get narrows KItem to a user element sort.
module T13TYPEDLIST-SYNTAX
  imports INT-SYNTAX
  imports BASIC-K
  syntax Elt ::= elt(Int) [symbol(elt)]
  syntax Prog ::= start(Int) [symbol(start)] | chk(Elt) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T13TYPEDLIST
  imports T13TYPEDLIST-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> .K </k>
  syntax LE [hook(LIST.List)]
  syntax LE ::= LE LE [function, total, left, assoc, hook(LIST.concat), symbol(_LE_), element(LEItem), unit(.LE)]
  syntax LE ::= ".LE" [function, total, hook(LIST.unit), symbol(.LE)]
  syntax LE ::= LEItem(Elt) [function, total, hook(LIST.element), symbol(LEItem)]
  syntax Elt ::= getLE(LE, Int) [function, hook(LIST.get), symbol(getLE)]
  rule [start]: start(I) => chk(getLE(LEItem(elt(I)), 0))
  rule [hit]: chk(elt(I)) => done(I)
  rule [ow]: chk(_) => done(0) [owise]
endmodule
