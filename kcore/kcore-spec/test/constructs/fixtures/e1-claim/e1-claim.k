module E1-CLAIM
  imports INT
  syntax Exp ::= Int | inc(Int)             [symbol(inc)]
  rule <k> inc(I) => I +Int 1 ... </k>
  claim <k> inc(1) => 2 ... </k>
endmodule
