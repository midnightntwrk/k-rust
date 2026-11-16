module E3-USERLIST
  imports INT
  syntax Ints ::= List{Int, ","} [symbol(ints)]
  syntax Exp ::= f(Ints) [symbol(f)] | g(Int) [symbol(g)]
  rule <k> g(X) => f(X) ... </k>
  rule <k> f(X, Y) => g(X +Int Y) ... </k>
  rule <k> f(.Ints) => g(0) ... </k>
endmodule
