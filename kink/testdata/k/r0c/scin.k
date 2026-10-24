// KINK-SC-DEFINED (fz26 P7-SIMPLE-KINK design): a stdin stream cell, into which kompile copies the
// prelude's stdin rules; three of them have a requires over findChar, whose equation the
// short-circuit scan flagged before KINK-SC-DEFINED (stock SIMPLE's short-circuit-reading row).
module SCIN-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= "rd" [symbol(rd)]
endmodule
module SCIN
  imports SCIN-SYNTAX
  imports INT
  imports LIST
  configuration <k> $PGM:Prog </k> <in stream="stdin"> .List </in>
  rule [rd]: <k> rd => .K </k>
endmodule
