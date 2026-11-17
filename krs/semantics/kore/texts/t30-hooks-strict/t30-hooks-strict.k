module T30-HOOKS-STRICT
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= a(Int) | b(Int) | c(Int) | r(Bool) | i(Int)
  rule <k> a(X) => r(false andThenBool (1 /Int X ==Int 0)) ... </k>
  rule <k> b(X) => r(false andBool (1 /Int X ==Int 0)) ... </k>
  rule <k> c(X) => i(#if true #then 1 #else 1 /Int X #fi) ... </k>
endmodule
