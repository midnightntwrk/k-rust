// Each hooked function of K-REFLECTION that the library reads as a parameter symbol (no registry
// hook), applied once in a rule's right side to variables (literal arguments would be folded
// by kompile); fixture.toml params records `kcore sem-fields`'s parameter lines.
module E6-PARAM-KREFLECTION
  imports K-REFLECTION
  imports K-IO
  imports INT
  imports LIST
  imports STRING
  syntax KItem ::= go(Int, K, K) [symbol(go)]
  rule <k> go(1, _, _) => #argv() ... </k>
  rule <k> go(2, _, _) => #configuration ... </k>
  rule <k> go(3, X1:String, _) => #fresh(X1) ... </k>
  rule <k> go(4, X1:String, _) => #getenv(X1) ... </k>
  rule <k> go(5, _, _) => #kompiledDirectory() ... </k>
  rule <k> go(6, X1:K, _) => #sort(X1) ... </k>
  rule <k> go(7, X1:K, _) => getsymbol(X1) ... </k>
endmodule
