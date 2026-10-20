// Rules whose right-hand sides read a value the definition leaves open: the listing order of a
// map's keys (MAP.keys_list) and of a set's elements (SET.set2list). With two distinct keys or
// elements the order is implementation-chosen and the leaf carries an
// `implementation-chosen-value` mark; with equal arguments there is one key or element, whose
// listing is determined, and the leaf is unmarked.

module CHOSEN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= listKeys(Int, Int)  [symbol(listKeys)]
               | listSet(Int, Int)   [symbol(listSet)]
endmodule

module CHOSEN
  imports CHOSEN-SYNTAX
  imports INT
  imports MAP
  imports SET
  imports LIST
  imports COLLECTIONS

  configuration <k> $PGM:Pgm </k>
                <out> .List </out>

  rule [list-keys]: <k> listKeys(A, B) => .K ... </k>
                    <out> _ => keys_list((A |-> 0) [ B <- 1 ]) </out>
  rule [list-set]:  <k> listSet(A, B) => .K ... </k>
                    <out> _ => Set2List(List2Set(ListItem(A) ListItem(B))) </out>
endmodule
