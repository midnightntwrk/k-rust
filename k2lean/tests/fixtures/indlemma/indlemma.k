// An author's lemmas about recursive functions, which hold by induction (EQ-21): a statement
// language whose loop body is a statement list inside a statement (the sorts are mutual, and a
// strict part of a list is reached through another sort), the concatenation `app`, and a
// step measure `mu`. Each simplification is stated and proved by induction on the variable the
// function recurses on (`k2l_eqn_ind`). A lemma about a function that calls another reads that
// other's lemma (EQ-23): `cw`'s bound is `mu`'s plus 2, without a case split on `mu`'s value, and
// `lw`'s, by induction, needs `cw`'s at each loop.
requires "domains.md"

module INDLEMMA-SYNTAX
  imports INT-SYNTAX
  syntax Stmt ::= "add" "(" Int ")"
                | "loop" "(" Int "," Code ")"
  syntax Stmts ::= List{Stmt, ";"}
  syntax Code ::= "{" Stmts "}"
endmodule

module INDLEMMA
  imports INDLEMMA-SYNTAX
  imports INT
  imports BOOL

  syntax Stmts ::= app(Stmts, Stmts) [function, total]
  rule app(.Stmts, T) => T
  rule app(S ; R, T) => S ; app(R, T)

  configuration <k> $PGM:Stmts </k> <reg> 0 </reg>

  rule <k> add(I) ; C => C </k> <reg> R => R +Int I </reg>
  rule <k> loop(M, { B }) ; C => app(B, loop(M -Int 1, { B }) ; C) </k> requires M >Int 0
  rule <k> loop(M, _) ; C => C </k> requires M <=Int 0

  // the steps left to run
  syntax Int ::= mu(Stmts) [function, total]
  rule mu(.Stmts) => 0
  rule mu(add(_) ; C) => 1 +Int mu(C)
  rule mu(loop(M, { B }) ; C) => 1 +Int maxInt(M, 0) *Int (mu(B) +Int 1) +Int mu(C)

  // the lemmas, each by induction: on the list `app` recurses on, with arithmetic (a product's
  // sign), and without
  rule mu(C) >=Int 0 => true [simplification]
  rule mu(app(A, B)) => mu(A) +Int mu(B) [simplification]
  rule app(A, .Stmts) => A [simplification]
  rule app(app(A, B), C) => app(A, app(B, C)) [simplification]

  // a weight that calls `mu` (not recursive), and one that calls the weight (recursive): each
  // lemma holds by the lemma before it about the function it calls
  syntax Int ::= cw(Stmts) [function, total]
  rule cw(B) => 2 +Int mu(B)
  syntax Int ::= lw(Stmts) [function, total]
  rule lw(.Stmts) => 0
  rule lw(add(_) ; C) => lw(C)
  rule lw(loop(_, { B }) ; C) => cw(B) +Int lw(C)
  rule cw(_B) >=Int 2 => true [simplification]
  rule lw(_C) >=Int 0 => true [simplification]
endmodule
