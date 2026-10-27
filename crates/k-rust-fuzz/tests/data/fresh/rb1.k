// F-ROLLBACK baseline: a two-name rule undefined where !A is 0, beside a plain sibling.
module FRESH-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= mk(Int)
endmodule
module FRESH
  imports FRESH-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <r> 7 </r> <s> 7 </s> </T>
  rule [div]: <k> mk(_) => .K ... </k> <r> _ => 10 /Int !_A:Int </r> <s> _ => !_B:Int </s>
  rule [plain]: <k> mk(_) => .K ... </k>
endmodule
