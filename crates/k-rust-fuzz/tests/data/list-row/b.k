// INT8 follow-ups review B1: `ListItem(1) => ListItem(2)` rewrites a term headed by a collection
// (a precondition row, `IndexedAt(List)`), so `ListItem(1)` is not a normal form and no end of
// this definition is data. This side stores ListItem(1).
module LR-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)
endmodule
module LR
  imports LR-SYNTAX
  imports LIST
  rule ListItem(1) => ListItem(2)
  configuration <k> $PGM:Pgm </k> <s> .List </s>
  rule <k> go(_) => .K </k> <s> _ => ListItem(1) </s>
endmodule
