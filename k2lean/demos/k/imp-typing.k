// A static type system for kimp's IMP, as a separate K definition over the same syntax
// (demos/ImpTypes proves kimp type-sound for it). Types are `int` and `bool`; a typing environment maps
// identifiers to types. `typeOf` is partial: it is undefined (no equation applies) exactly
// on ill-typed expressions. `wt` is total.

requires "imp.k"

module IMP-TYPING-SYNTAX
  imports IMP-SYNTAX
endmodule

module IMP-TYPING
  imports IMP-TYPING-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL

  syntax Type ::= "int" | "bool"

  syntax Type ::= typeOf(Expr, Map) [function]
  rule typeOf(_:Int, _) => int
  rule typeOf(_:Bool, _) => bool
  rule typeOf(X:Id, X |-> T:Type _:Map) => T

  rule typeOf(- E, G) => int requires typeOf(E, G) ==K int
  rule typeOf(! E, G) => bool requires typeOf(E, G) ==K bool
  rule typeOf(E1 + E2, G) => int requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 - E2, G) => int requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 * E2, G) => int requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 / E2, G) => int requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 >= E2, G) => bool requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 > E2, G) => bool requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 <= E2, G) => bool requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 < E2, G) => bool requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOf(E1 == E2, G) => bool requires typeOf(E1, G) ==K typeOf(E2, G)
  rule typeOf(E1 != E2, G) => bool requires typeOf(E1, G) ==K typeOf(E2, G)
  rule typeOf(E1 && E2, G) => bool requires typeOf(E1, G) ==K bool andBool typeOf(E2, G) ==K bool
  rule typeOf(E1 || E2, G) => bool requires typeOf(E1, G) ==K bool andBool typeOf(E2, G) ==K bool

  syntax Bool ::= wt(Stmt, Map) [function, total]
  rule wt({}, _) => true
  rule wt({ S }, G) => wt(S, G)
  rule wt(X:Id = E ;, G) => true requires typeOf(X, G) ==K typeOf(E, G)
  rule wt(S1:Stmt S2:Stmt, G) => wt(S1, G) andBool wt(S2, G)
  rule wt(if (C) S1 else S2, G) => wt(S1, G) andBool wt(S2, G) requires typeOf(C, G) ==K bool
  rule wt(if (C) S, G) => wt(S, G) requires typeOf(C, G) ==K bool
  rule wt(while (C) S, G) => wt(S, G) requires typeOf(C, G) ==K bool
  rule wt(_, _) => false [owise]

  // a configuration only so that the definition compiles as a main module
  configuration <k> $PGM:Stmt </k>
endmodule
