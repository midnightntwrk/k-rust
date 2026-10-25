module B-RULES
  imports A-RULES

  // line 5 of b is this comment; b's rules start on line 7

  syntax Pgm ::= done(Int)
  rule left(I) => done(I)
  rule right(I) => done(I)
endmodule
