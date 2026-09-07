module SD-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= count(Int)
endmodule
module SD
  imports SD-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> count(N) => count(N -Int 1) ... </k> requires N >Int 0
endmodule
