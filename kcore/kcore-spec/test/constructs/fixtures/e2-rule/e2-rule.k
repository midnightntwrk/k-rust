module E2-RULE
  imports INT
  syntax KResult ::= Int
  syntax Exp ::= Int | a(Int) [symbol(a)] | b(Int) [symbol(b)] | c(Int) [symbol(c)]
  rule [r-label]: <k> a(X) => b(X) ... </k>
  rule <k> a(X) => c(X) ... </k> [priority(10)]
  rule <k> a(X) => c(X +Int 1) ... </k> [priority(50)]
  rule <k> a(X) => c(X +Int 2) ... </k> [priority(60)]
  rule <k> b(X) => c(X) ... </k> [owise]
  rule <k> b(0) => c(0) ... </k>
  rule <k> c(X) => b(X) ... </k> [preserves-definedness, label(r2)]
  rule <k> c(1) => b(1) ... </k> [cool]
  rule <k> c(2) => b(2) ... </k> [heat]
endmodule
