// F-ROLLBACK mutant: the same K rules, div's cells written in the other order.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <r> 7 </r> <s> 7 </s> </T>
  rule [div]: <k> mk(_) => .K ... </k> <s> _ => !_B:Int </s> <r> _ => 10 /Int !_A:Int </r>
  rule [plain]: <k> mk(_) => .K ... </k>
endmodule
