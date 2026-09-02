// reference: k/result/bin/kast --definition k-rx --module RX-SYNTAX --sort Pgm --expression ddd
module RX-SYNTAX
  syntax Foo ::= r"\\d+" [token]
  syntax Pgm ::= Foo [symbol(pgm)]
endmodule

module RX
  imports RX-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
