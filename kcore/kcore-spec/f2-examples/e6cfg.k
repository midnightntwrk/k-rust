module E6-CONFIGURATION
  imports K-IO
  imports K-REFLECTION
  syntax Exp ::= "go" [symbol(go)] | wrap(K) [symbol(wrap)]
  rule <k> go => wrap(#configuration) ... </k>
endmodule
