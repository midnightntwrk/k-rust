// Re-pin R0b (decision 1): imports MAP, but no sentence of its own lists a map's keys; only a
// test's initial state can.
module KEYSFREE-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax Prog ::= start(Int) [symbol(start)]
                | keys(List) [symbol(keys)]
endmodule
module KEYSFREE
  imports KEYSFREE-SYNTAX
  imports INT
  imports MAP
  imports LIST
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start(I) => keys(ListItem(I)) </k>
endmodule
