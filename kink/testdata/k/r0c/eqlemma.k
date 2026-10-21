// Re-pin R0c-fix-4 (R0c-fix-3 review minor 6): `{ A #Equals B }` outside a rule's or an
// application-headed equation's requires: in the requires of a lemma rooted at a predicate
// (#Ceil), in an equation's ensures and in a rewrite rule's ensures. Each is read as an
// equals-condition, which excludes the definition.
module EQLEMMA-SYNTAX
  imports INT-SYNTAX
  imports ML-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | val(Int) [symbol(val)]
  syntax Int ::= f(Int) [function, symbol(f)]
               | g(Int) [function, symbol(g)]
endmodule
module EQLEMMA
  imports EQLEMMA-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [f]: f(I) => 10 /Int I
  rule [fceil]: #Ceil(f(I)) => #Top requires { I #Equals 1 } [simplification]
  rule [g]: g(I) => I ensures { I #Equals I }
  rule [go]: <k> go(I) => val(g(I)) </k> ensures { I #Equals I }
endmodule
