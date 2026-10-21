// TB-02 review F1: no Unicode scalar lies strictly between U+007F and U+0080.
module TB02STRING-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= stringRange(String) [symbol(stringRange)]
                | stringPoint(String) [symbol(stringPoint)]
                | done(Int) [symbol(done)]
endmodule
module TB02STRING
  imports TB02STRING-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  configuration <k> .K </k>
  rule [range]: stringRange(S) => done(7)
    requires lengthString(S) ==Int 1 andBool "\u007f" <String S andBool S <String "\u0080"
  rule [rangeow]: stringRange(_) => done(0) [owise]
  rule [point]: stringPoint("\u0080") => done(7)
  rule [pointow]: stringPoint(_) => done(0) [owise]
  // Used as the point mutant's equivalent condition; its equation remains unchanged.
  syntax Bool ::= pointGuard(String) [function, total, symbol(pointGuard)]
  rule [guard]: pointGuard(S) => lengthString(S) ==Int 1 andBool "\u007f" <String S andBool S <String "\u0081"
endmodule
