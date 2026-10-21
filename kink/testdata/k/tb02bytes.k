// TB-02 review F3: every byte sequence denotes a Bytes value.
module TB02BYTES-SYNTAX
  imports INT-SYNTAX
  imports BYTES-SYNTAX
  syntax Prog ::= bytesPoint(Bytes) [symbol(bytesPoint)]
                | done(Int) [symbol(done)]
endmodule
module TB02BYTES
  imports TB02BYTES-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports BYTES
  configuration <k> .K </k>
  rule [point]: bytesPoint(b"\x80") => done(7)
  rule [pointow]: bytesPoint(_) => done(0) [owise]
  syntax Bool ::= byteGuard(Bytes) [function, symbol(byteGuard)]
  rule [guard]: byteGuard(B) => lengthBytes(B) ==Int 1 andBool B[0] ==Int 128
endmodule
