// KINK-CENSUS-RUNLIST (fz26 P7-SIMPLE-KINK, review R2-S1): console operations in rewrite rules,
// without the bytes pair. #write and #getc are on the run list, so the definition is not excluded
// by the census; a run that applies one is excluded by its unsupportedHooks list.
module IOPW-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "w" | "g" | "n"
endmodule

module IOPW
  imports IOPW-SYNTAX
  imports K-IO
  imports INT
  imports STRING
  configuration <k> $PGM:Pgm </k> <r> .K </r>
  rule <k> w => .K ... </k> <r> _ => #write(1, "x") </r>
  rule <k> g => .K ... </k> <r> _ => #getc(0) </r>
  rule <k> n => .K ... </k> <r> _ => 1 </r>
endmodule
