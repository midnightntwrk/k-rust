// A static type system for kimp's expression language EXPR (expr.k: arithmetic and Boolean
// expressions, whose programs end with a value on <k>), as a separate K definition over the same
// syntax (demos/ExprTypes proves EXPR type-sound for it). Types are `int` and `bool`; `typeOf` is
// partial: it is undefined (no equation applies) exactly on ill-typed expressions. The typing
// environment is unused (EXPR has no variables); it is there because `k2lean soundness` types a
// term in an environment. A program is accepted when it has a type.

requires "expr.k"

module EXPR-TYPING-SYNTAX
  imports EXPR-SYNTAX
endmodule

module EXPR-TYPING
  imports EXPR-TYPING-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL

  syntax Type ::= "int" | "bool"

  syntax Type ::= typeOf(Expr, Map) [function]
  rule typeOf(_:Int, _) => int
  rule typeOf(_:Bool, _) => bool

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

  // a configuration only so that the definition compiles as a main module
  configuration <k> $PGM:Expr </k>
endmodule
