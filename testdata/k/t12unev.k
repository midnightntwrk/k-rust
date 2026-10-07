// Weak R-UNEV controls: no byte comparator may separate symbolic FLOAT calls.
module T12UNEV-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  syntax Prog ::= u1s(Int) [symbol(u1s)] | u1c(Float) [symbol(u1c)] | u3s(Int) [symbol(u3s)]
                | u3c(Float, Float) [symbol(u3c)] | done(Int) [symbol(done)]
endmodule
module T12UNEV
  imports T12UNEV-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  imports K-EQUAL
  configuration <k> .K </k>
  rule [u1start]: u1s(_) => u1c(?F)
  rule [u1]: u1c(F) => done(7) requires F *Float 1.0 ==K F *Float 1.0
  rule [u1ow]: u1c(_) => done(0) [owise]
  rule [u3]: u3s(_) => u3c(?F *Float 3.0, ?F *Float 3.00)
  rule [u3point]: u3c(F, F) => done(7)
  rule [u3ow]: u3c(_, _) => done(0) [owise]
endmodule
