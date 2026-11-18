// The two sort-parametric hooked functions of SUBSTITUTION (substitution.md), each applied once in a
// rule's right side, at sort K: the declarations are not read (sort-parametric, of a builtin file's
// names of its own), and an application of an instance of a hooked sort-parametric symbol is refused.
requires "substitution.md"
module E6-PARAM-SUBST-POLY
  imports SUBSTITUTION
  imports INT
  imports MAP
  syntax KItem ::= go(Int, K, KItem, KItem, Map) [symbol(go)]
  rule <k> go(1, X:K, A:KItem, B:KItem, _) => X[A / B] ... </k>
  rule <k> go(2, X:K, _, _, M:Map) => X[M] ... </k>
endmodule
