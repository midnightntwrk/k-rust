module DN-SYNTAX
  syntax S ::= S S [symbol(cat)]
             | "c" "a" "c" "a" [symbol(caca)]
             | "d" [symbol(d)]
             | S "d" [symbol(sd)]
endmodule
module DN
  imports DN-SYNTAX
  configuration <k> $PGM:S </k>
endmodule
