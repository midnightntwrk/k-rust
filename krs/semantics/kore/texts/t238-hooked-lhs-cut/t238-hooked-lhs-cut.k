// List:set (hook LIST.update) in a rule's left side: with a list argument held by nothing else, and with every argument bound in the k cell.
module T238-HOOKED-LHS-CUT
  imports LIST
  imports INT
  configuration <k> $PGM:K </k> <list> ListItem(0) ListItem(1) ListItem(2) </list>
  syntax KItem ::= l(Int, Int) [symbol(l)] | m(List, Int, Int) [symbol(m)]
  rule <k> l(I, J) => .K ... </k> <list> _ [ I <- J ] </list>
  rule <k> m(L, I, J) => .K ... </k> <list> L [ I <- J ] </list>
endmodule
