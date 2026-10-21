// Re-pin R0c-fix-1 deliverable 3 (R0c review 1 minor, the reviewer's probe): a stdout stream cell, into
// which kompile copies the prelude's stream rules (#write, Float2String) with their prelude source.
module OUTS-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= emit(Int) [symbol(emit)]
endmodule
module OUTS
  imports OUTS-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:Prog </k> <out stream="stdout"> .List </out>
  rule [emit]: <k> emit(I) => .K ... </k> <out> ... .List => ListItem(I) </out>
endmodule
