module SEG-SYNTAX
  syntax T ::= "a" | c(T) | p(T, T)
endmodule
module SEG
  imports SEG-SYNTAX
  configuration <k> $PGM:T </k>
endmodule
