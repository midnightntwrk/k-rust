requires "a/rules.k"
requires "b/rules.k"
module MAIN
  imports A-RULES
  imports B-RULES
  configuration <k> $PGM:Pgm </k>
endmodule
