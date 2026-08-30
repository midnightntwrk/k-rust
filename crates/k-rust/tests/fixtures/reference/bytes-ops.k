module BYTES-OPS
  imports BYTES
  imports INT

  syntax Input ::= "bytesOps" | BytesResult
  syntax BytesResult ::= "bytesResult" "(" Bytes "," Bytes "," Bytes "," Bytes "," Int "," Int ")"

  configuration <k> $PGM:Input </k>

  rule <k> bytesOps => bytesResult(
    b"ab" +Bytes b"cd",
    substrBytes(b"abcdef", 1, 4),
    padLeftBytes(b"x", 3, 48),
    padRightBytes(Int2Bytes(2, 258, BE), 3, 0),
    Bytes2Int(b"\x01\x02", BE, Unsigned),
    Bytes2Int(b"\x01\x02", LE, Unsigned))
  </k>
endmodule
