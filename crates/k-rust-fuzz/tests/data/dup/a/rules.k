module A-RULES
  imports INT
  syntax Pgm ::= run(Int) | left(Int) | right(Int)
  // a's rule on line 5
  rule run(I) => left(I) requires I <Int 10
  rule run(I) => right(I) requires I >=Int 10
endmodule
