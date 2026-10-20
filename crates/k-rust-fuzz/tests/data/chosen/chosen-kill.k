// Mutant of chosen.k whose `list-keys` appends the first argument to the listing:
// `listKeys(A, B)` ends with keys_list(...) followed by A, which the baseline never reaches.
// For A =/= B both sides read an implementation-chosen order and carry its mark, so condition 3
// of the differential target (ARCHITECTURE.md 4.3) refuses the kill; for A == B neither side
// reads an open value, and the mutant's end [A, A] is a kill.

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
                    <out> _ => keys_list((A |-> 0) [ B <- 1 ]) ListItem(A) </out>
  rule [list-set]:  <k> listSet(A, B) => .K ... </k>
                    <out> _ => Set2List(List2Set(ListItem(A) ListItem(B))) </out>
endmodule
