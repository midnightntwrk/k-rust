// TB-02 review 4 F1, the converse direction: k-rust's STRING.string2token writes a String's
// UTF-8 bytes into any result sort. K reads a Bytes token one code point per byte, so a
// one-code-point String below U+0100 is a one-byte token and the width guard never holds.
module TB02STRINGTOKEN-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  syntax Prog ::= bytesWidth(String) [symbol(bytesWidth)]
                | done(Int) [symbol(done)]
endmodule
module TB02STRINGTOKEN
  imports TB02STRINGTOKEN-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports BYTES
  configuration <k> .K </k>
  syntax Bytes ::= s2b(String) [function, total, hook(STRING.string2token), symbol(s2b)]
  rule [width]: bytesWidth(S) => done(7)
    requires lengthString(S) ==Int 1 andBool ordChar(S) <Int 256
      andBool lengthBytes(s2b(S)) ==Int 2
  rule [widthow]: bytesWidth(_) => done(0) [owise]
endmodule
