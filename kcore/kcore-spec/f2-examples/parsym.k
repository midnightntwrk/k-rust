// A sort-parametric function declared and applied only in a lemma (as the corpus fixture
// parametric-semantic-cast): `symbol pair{S}(S, S) : S` in KORE. KCore applies no sort-parametric
// symbol but `ite`, so the declaration is part of the reading only through an application: it is
// not read (`unread parametricUnused`), and the lemma is inert. `parsym-app.k` applies it in a
// rule, which is refused (`parametricSymbol`).
module PARSYM-SYNTAX
  syntax A ::= "a" [symbol(a)]
  syntax B ::= "b" [symbol(b)]
  syntax C ::= A | B
  syntax {S} S ::= pair(S, S) [symbol(pair), function]
  syntax Cmd ::= go() [symbol(go)] | done() [symbol(done)]
endmodule

module PARSYM
  imports PARSYM-SYNTAX
  configuration <k> $PGM:Cmd </k>
  rule pair(a, b):C => pair(a, b):C [simplification]
  rule [go]: <k> go() => done() </k>
endmodule
