module TEST
  imports INT
  syntax Bytes ::= ".Bytes" [symbol(.Bytes)]
  syntax WordStack ::= ".WordStack" [symbol(.WordStack)]
  syntax Bytes ::= Bytes "[" Int ":=" Bytes "]" [symbol(mapWriteRange)]
  syntax WordStack ::= WordStack "[" Int ":=" Int "]" [symbol(setWordStack)]
  rule _ [ START := _ ] => .Bytes
endmodule
