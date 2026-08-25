module P2-LIST
  syntax Atom ::= "n" [symbol(n)]
  syntax Atoms ::= List{Atom, ","} [symbol(atoms), terminator-symbol(.atoms)]
  syntax Pgm ::= "[" Atoms "]" [symbol(bracket)]

  configuration <k> $PGM:Pgm </k>
endmodule
