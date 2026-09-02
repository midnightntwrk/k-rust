module NELIST-SYNTAX
  imports ID-SYNTAX
  syntax Ids ::= NeList{Id, ","}
  syntax Pgm ::= Ids
endmodule

module NELIST
  imports NELIST-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
