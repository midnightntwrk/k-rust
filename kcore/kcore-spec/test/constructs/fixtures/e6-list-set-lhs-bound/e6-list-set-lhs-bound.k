// List:set (hook LIST.update) in a rule's left side, every argument bound by a constructor position
// of the left side: the list L, the index I and the value J are m's arguments in the k cell.
module E6-LIST-SET-LHS-BOUND
  imports LIST
  imports INT
  configuration <k> $PGM:K </k> <list> ListItem(0) ListItem(1) ListItem(2) </list>
  syntax KItem ::= m(List, Int, Int) [symbol(m)]
  rule <k> m(L, I, J) => .K ... </k> <list> L [ I <- J ] </list>
endmodule
