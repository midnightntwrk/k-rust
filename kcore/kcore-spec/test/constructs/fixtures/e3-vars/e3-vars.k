module E3-VARS
  imports INT
  imports BOOL
  syntax Exp ::= a(Int) [symbol(a)] | b() [symbol(b)] | c(Int, Int) [symbol(c)] | d(Int) [symbol(d)]
  configuration <k> $PGM:Exp </k> <n> $N:Int </n>
  rule <k> a(X) => d(X) ... </k>
  rule <k> b() => d(!N:Int) ... </k>
  rule <k> c(_, _Y) => d(?Z:Int) ... </k>
endmodule
