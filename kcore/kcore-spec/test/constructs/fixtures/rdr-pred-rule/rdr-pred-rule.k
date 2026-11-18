// A rule of the text for the sort predicate kompile generates (isFoo), at a pattern the generated
// equations also decide.
module RDR-PRED-RULE
  imports BOOL
  syntax Foo ::= "a" [symbol(a)] | pair(Foo, Foo) [symbol(pair)]
  rule isFoo(pair(_, _)) => true
endmodule
