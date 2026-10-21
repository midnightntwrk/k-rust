// TB-02 review 4 F1: k-rust's STRING.token2string copies the bytes of any domain value,
// so a function with that hook over Bytes turns the byte 80 into an invalid String. The
// range guard is the one of tb02string.k; K Strings never satisfy it.
module TB02BYTESTOKEN-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  syntax Prog ::= stringRange(String) [symbol(stringRange)]
                | start(Int) [symbol(start)]
                | done(Int) [symbol(done)]
endmodule
module TB02BYTESTOKEN
  imports TB02BYTESTOKEN-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports BYTES
  configuration <k> .K </k>
  syntax String ::= b2s(Bytes) [function, total, hook(STRING.token2string), symbol(b2s)]
  syntax Bytes ::= mkb(Int) [function, total, symbol(mkb)]
  rule mkb(I) => Int2Bytes(1, I, BE)
  rule start(I) => stringRange(b2s(mkb(I)))
  rule [range]: stringRange(S) => done(7)
    requires lengthString(S) ==Int 1 andBool "\u007f" <String S andBool S <String "\u0080"
  rule [rangeow]: stringRange(_) => done(0) [owise]
endmodule
