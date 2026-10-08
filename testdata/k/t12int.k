// TB-03 review 1 F2: test-written noncanonical text in a renamed INT.Int-hooked sort.
module T12INT-SYNTAX
  imports INT-SYNTAX
  syntax MyInt [hook(INT.Int)]
  syntax MyInt ::= r"m[0-9]+" [token]
  syntax Prog ::= chk(MyInt, MyInt) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module T12INT
  imports T12INT-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> .K </k>
  rule [p]: chk(X, X) => done(7)
  rule [o]: chk(_, _) => done(0) [owise]
endmodule
