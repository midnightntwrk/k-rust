module TEST
  imports INT
  syntax Bytes ::= ".Bytes" [symbol(.Bytes)]
  syntax WordStack ::= ".WordStack" [symbol(.WordStack)]
  syntax Bytes ::= Bytes "[" Int ":=" Bytes "]" [function, total, symbol(mapWriteRange)]
  syntax WordStack ::= WordStack "[" Int ":=" Int "]" [function, total, symbol(setWordStack)]
  rule _ [ START := _ ] => .Bytes requires START <Int 0
endmodule
