// A sort below another by two subsort paths (E < A < T, E < B < T), with no subsort E < T stated:
// kompile writes T's no-junk axiom with the injection of E once.
module SUBSORT-DIAMOND-SYNTAX
  syntax E ::= "e" [symbol(e)]
  syntax A ::= E | "a" [symbol(a)]
  syntax B ::= E | "b" [symbol(b)]
  syntax T ::= A | B
endmodule

module SUBSORT-DIAMOND
  imports SUBSORT-DIAMOND-SYNTAX
  configuration <k> $PGM:T </k>
endmodule
