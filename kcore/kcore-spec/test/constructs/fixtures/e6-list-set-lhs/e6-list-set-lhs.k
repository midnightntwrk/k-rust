// List:set (hook LIST.update) on a rule's left side, in a list cell: the rule of K's regression
// test list-set, with a symbol attribute on l.
module E6-LIST-SET-LHS
  imports LIST
  imports INT
  configuration <k> $PGM:K </k> <list> ListItem(0) ListItem(1) ListItem(2) </list>
  syntax KItem ::= l(Int, Int) [symbol(l)]
  rule <k> l(I, J) => .K ... </k>
       <list> _ [ I <- J ] </list>
endmodule
