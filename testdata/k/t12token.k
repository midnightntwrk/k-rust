// T1: the Float token constructor is declared but never applied by an axiom.
module T12TOKEN-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= chk(Int, Float) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T12TOKEN
  imports T12TOKEN-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  imports STRING
  imports K-EQUAL
  configuration <k> .K </k>
  syntax Float ::= parseF(String) [function, symbol(parseF), hook(STRING.string2token)]
  rule [tp]: chk(I, F) => done(7)
    requires precisionFloat(F) ==Int 53 andBool exponentBitsFloat(F) ==Int 11
      andBool F ==K Int2Float(I, 53, 11)
  rule [to]: chk(_, _) => done(0) [owise]
endmodule
