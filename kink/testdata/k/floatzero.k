// R3-ADMIT-FLOAT: Float literals are compared by value. `start(I)` reaches `chk` with the
// binary64 value of I; `point` matches the binary64 zero. A respelling of `0.0` that names the
// same element (`0.00e5`, `0e+00p53x11`) is the baseline's rule; one that names another element
// (`-0.0`, the other signed zero; `0.0f`, the binary32 zero) is not.
module FLOATZERO-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)] | chk(Float) [symbol(chk)] | done(Int) [symbol(done)]
endmodule
module FLOATZERO
  imports FLOATZERO-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports FLOAT
  configuration <k> .K </k>
  rule [start]: start(I) => chk(Int2Float(I, 53, 11))
  rule [point]: chk(0.0) => done(7)
  rule [pointow]: chk(_) => done(0) [owise]
endmodule
