module T111-USER-GENERATED-COUNTER
  imports INT
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)]
  rule <k> a() => b(!X:Int) ... </k>
  rule <k> b(_) => b(C) ... </k> <generatedCounter> C </generatedCounter>
endmodule
