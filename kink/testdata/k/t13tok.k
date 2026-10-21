// VI-T13 V1: ite feeds Bytes through an unhooked Tok to token2string.
module T13TOK-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  syntax Tok [token]
  syntax Prog ::= start(Int) [symbol(start)] | stringRange(String) [symbol(stringRange)] | done(Int) [symbol(done)]
endmodule
module T13TOK
  imports T13TOK-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports BYTES
  configuration <k> .K </k>
  syntax String ::= tok2s(Tok) [function, total, hook(STRING.token2string), symbol(tok2s)]
  syntax Tok ::= b2t(Bool, Bytes, Bytes) [function, total, hook(KEQUAL.ite), symbol(b2t)]
  rule [start]: start(I) => stringRange(tok2s(b2t(true, Int2Bytes(1, I, BE), Int2Bytes(1, I, BE))))
  rule [range]: stringRange(S) => done(7)
    requires lengthString(S) ==Int 1 andBool "\u007f" <String S andBool S <String "\u0080"
  rule [rangeow]: stringRange(_) => done(0) [owise]
endmodule
