// The two sort-parametric hooked functions of UNIFICATION (unification.k), each applied once in a
// rule's right side, at sort K: the declarations are not read (sort-parametric, of a builtin file's
// names of its own), and an application of an instance of a hooked sort-parametric symbol is refused.
requires "unification.k"
module E6-PARAM-UNIFICATION-POLY
  imports UNIFICATION
  imports INT
  imports SET
  syntax KItem ::= go(Int, K, K, Set) [symbol(go)]
  rule <k> go(1, X1:K, X2:K, _) => #freezeKVariables(X1, X2) ... </k>
  rule <k> go(2, X1:K, _, S:Set) => #renameMetaKVariables(X1, S) ... </k>
endmodule
