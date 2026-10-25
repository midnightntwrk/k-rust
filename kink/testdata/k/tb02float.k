module TB02FLOAT-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  syntax Prog ::= floatCheck(Float) [symbol(floatCheck)]
                | done(Int) [symbol(done)]
                | start(Int) [symbol(start)]
endmodule
module TB02FLOAT
  imports TB02FLOAT-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  configuration <k> .K </k>
  rule [point]: floatCheck(1.0) => done(7)
  rule [start]: start(I) => floatCheck(Int2Float(I, 53, 11))
  rule [pointow]: floatCheck(_) => done(0) [owise]
endmodule
