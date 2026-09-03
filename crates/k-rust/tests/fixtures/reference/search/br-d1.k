// reference: krun a.pgm --search-all --output kore -> a zz c b d (Kore order; port prints a b c d zz by arbiter row 12)
module BR-SYNTAX
  syntax Pgm ::= "a" | "b" | "c" | "d" | "zz"
endmodule
module BR
  imports BR-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule [ab]: <k> a => b </k>
  rule [ac]: <k> a => c </k>
  rule [azz]: <k> a => zz </k>
  rule [bd]: <k> b => d </k>
endmodule
