// A sort with no constructor, under a binder and as a variable in the left sides of two rules.
module T192-SORT-NO-CONSTRUCTOR
  syntax Empty
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d() [symbol(d)] | e(Empty) [symbol(e)]
  rule <k> c(#Exists Y:Empty. a()) => b() ... </k>
  rule <k> e(_:Empty) #Or d() => b() ... </k>
endmodule
