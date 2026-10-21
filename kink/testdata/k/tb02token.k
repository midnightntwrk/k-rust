// TB-02 review 3 F1: STRING.token2string copies a token's bytes into a String, so an
// invalid-UTF-8 token reaches the String guards of tb02string.k without a String value.
module TB02TOKEN-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports ID-SYNTAX
  syntax Tok [token]
  syntax Prog ::= stringRange(String) [symbol(stringRange)]
                | stringPoint(String) [symbol(stringPoint)]
                | done(Int) [symbol(done)]
endmodule
module TB02TOKEN
  imports TB02TOKEN-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports ID
  configuration <k> .K </k>
  // A user token sort reaches the same hook as K's standard Id.
  syntax String ::= tok2s(Tok) [function, total, hook(STRING.token2string), symbol(tok2s)]
  rule [range]: stringRange(S) => done(7)
    requires lengthString(S) ==Int 1 andBool "\u007f" <String S andBool S <String "\u0080"
  rule [rangeow]: stringRange(_) => done(0) [owise]
  rule [point]: stringPoint("\u0080") => done(7)
  rule [pointow]: stringPoint(_) => done(0) [owise]
  // Used as the point mutant's equivalent condition; its equation remains unchanged.
  syntax Bool ::= pointGuard(String) [function, total, symbol(pointGuard)]
  rule [guard]: pointGuard(S) => lengthString(S) ==Int 1 andBool "\u007f" <String S andBool S <String "\u0081"
endmodule
