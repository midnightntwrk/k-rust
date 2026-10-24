// KINK-CENSUS-RUNLIST (fz26 P7-SIMPLE-KINK, review R2-S1): iopw.k with rule b, which applies the
// String2Bytes/Bytes2String pair. k-rust evaluates the pair with no record, so it stays in the
// census and excludes the whole definition, every program alike.
module IOP-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "w" | "g" | "b" | "n"
endmodule

module IOP
  imports IOP-SYNTAX
  imports K-IO
  imports INT
  imports STRING
  imports BYTES
  configuration <k> $PGM:Pgm </k> <r> .K </r>
  rule <k> w => .K ... </k> <r> _ => #write(1, "x") </r>
  rule <k> g => .K ... </k> <r> _ => #getc(0) </r>
  rule <k> b => .K ... </k> <r> _ => Bytes2String(String2Bytes("ab")) </r>
  rule <k> n => .K ... </k> <r> _ => 1 </r>
endmodule
