module T107-GENERATED-NAMES
  imports INT
  syntax Exp ::= a(Int) | b(Int)
  rule <k> a(X) => b(X +Int 1) ... </k> requires X >Int 0
  rule <k> b(_) => a(0) ... </k>
endmodule
