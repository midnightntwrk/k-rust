requires "domains.md"

module PARAMS-SYNTAX
  imports INT-SYNTAX
  imports BYTES-SYNTAX
  syntax Stmt ::= "hash" Bytes | "roundtrip" Int
endmodule

module PARAMS
  imports PARAMS-SYNTAX
  imports INT
  imports BYTES
  imports BOOL
  imports STRING
  configuration <T> <k> $PGM:Stmt </k> <out> 0 </out> </T>

  // `Bytes2Hex` (a hook the hook library does not implement) and a function without equations
  // are parameters of the generated library (fields of its `Hooks` class)
  syntax Int ::= oracle(Int) [function]

  rule <k> hash B => .K </k> <out> _ => lengthString(Bytes2Hex(B)) +Int oracle(lengthBytes(B)) </out>
  rule <k> roundtrip I => .K </k> <out> _ => Bytes2Int(Int2Bytes(4, I, BE), BE, Signed) </out>
endmodule
