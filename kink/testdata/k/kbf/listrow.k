// fz26 KINK-BASELINE-FINDINGS review S1/N4 (after k-rust-fuzz's list-row fixture, INT8 follow-ups
// review B1): `ListItem(1) => ListItem(2)` rewrites a term headed by a collection, a precondition
// row (`IndexedAt(List)`) that the check decides, so no end is data and its name is refused.
module LISTROW-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)
endmodule
module LISTROW
  imports LISTROW-SYNTAX
  imports LIST
  rule ListItem(1) => ListItem(2)
  configuration <k> $PGM:Pgm </k> <s> .List </s>
  rule <k> go(_) => .K </k> <s> _ => ListItem(1) </s>
endmodule
