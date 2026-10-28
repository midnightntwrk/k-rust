// A static type system for IMP++ (K's tutorial, `pl-tutorial/1_k/4_imp++/lesson_7/imp.k`), as a
// separate K definition over the same syntax: the second semantics of `k2lean soundness` (example
// material, `demos/ImpPlusTypes`). Types are `int`, `bool` and `string`. `typeOf` and `typeOfB` are
// partial: undefined (no equation applies) exactly on ill-typed expressions; `wt` and `wts` accept
// statements; `wtEnv` types the environment item that a block leaves on `<k>` (`Ss ~> Rho`).
//
// This checker accepts the programs without variables, `read()` or division (SND-6's first slice):
// typing a variable needs the typing environment to follow declarations and block scopes along
// `<k>`, and `read()` and division stop a thread at a well-typed head (empty input, a zero divisor),
// both outside the theorem's outcomes so far. The environment `G` is not read.

requires "imp.k"

module IMPPLUS-TYPING-SYNTAX
  imports IMP-SYNTAX
  imports DOMAINS-SYNTAX
  // the strictness attributes of IMP-SYNTAX need it; the checker's own equations do not read it
  syntax KResult ::= Int | Bool | String
endmodule

module IMPPLUS-TYPING
  imports IMPPLUS-TYPING-SYNTAX
  imports DOMAINS

  syntax Type ::= "int" | "bool" | "string"

  syntax Type ::= typeOf(AExp, Map) [function]
  rule typeOf(_:Int, _) => int
  rule typeOf(_:String, _) => string
  rule typeOf(- _, _) => int
  rule typeOf(E1 + E2, G) => typeOf(E1, G)
    requires typeOf(E1, G) ==K typeOf(E2, G) andBool typeOf(E1, G) =/=K bool
  rule typeOf(spawn B, G) => int requires wt(B, G)

  syntax Type ::= typeOfB(BExp, Map) [function]
  rule typeOfB(_:Bool, _) => bool
  rule typeOfB(E1 <= E2, G) => bool requires typeOf(E1, G) ==K int andBool typeOf(E2, G) ==K int
  rule typeOfB(! B, G) => bool requires typeOfB(B, G) ==K bool
  rule typeOfB(B1 && B2, G) => bool requires typeOfB(B1, G) ==K bool andBool typeOfB(B2, G) ==K bool

  syntax Bool ::= wt(Stmt, Map) [function, total]
  rule wt({ Ss }, G) => wts(Ss, G)
  // IMP++ discards an integer (`rule _:Int; => .K`), and nothing else
  rule wt(E ;, G) => true requires typeOf(E, G) ==K int
  rule wt(if (B) S1 else S2, G) => wt(S1, G) andBool wt(S2, G) requires typeOfB(B, G) ==K bool
  rule wt(while (B) S, G) => wt(S, G) requires typeOfB(B, G) ==K bool
  rule wt(print(AEs) ;, G) => printable(AEs, G)
  rule wt(halt ;, _) => true
  rule wt(join E ;, G) => true requires typeOf(E, G) ==K int
  rule wt(_, _) => false [owise]

  syntax Bool ::= wts(Stmts, Map) [function, total]
  rule wts(.Stmts, _) => true
  rule wts(S Ss, G) => wt(S, G) andBool wts(Ss, G)

  // `print` evaluates its arguments one at a time and prints integers and strings
  syntax Bool ::= printable(AExps, Map) [function, total]
  rule printable(.AExps, _) => true
  rule printable(E, AEs, G) => printable(AEs, G)
    requires typeOf(E, G) ==K int orBool typeOf(E, G) ==K string
  rule printable(_, _) => false [owise]

  // the environment a block saves on `<k>`, restored when the block ends
  syntax Bool ::= wtEnv(Map, Map) [function, total]
  rule wtEnv(_, _) => true

  // a configuration only so that the definition compiles as a main module
  configuration <k> $PGM:Stmts </k>
endmodule
