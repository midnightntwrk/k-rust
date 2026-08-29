module FRESH-CONSTANTS
  imports INT

  syntax Input ::= Int | "fresh"
  configuration <k> $PGM:Input </k>
  rule <k> fresh => !I:Int </k>
endmodule
