// The security checker of the fixture contract (k2lean/docs/design.md, section 3.7), a separate K
// definition over its syntax, in the style of Compact's witness-data analysis with a fixed
// labelling of the local variables: levels `lo` and `hi`; `lev` is the level of an expression
// (`witness()` is `hi`; `read(X)` and `disclose(E)` are `lo`); `quiet` holds for an expression
// that performs no operation an observer sees (no `read`, no `disclose`; it takes the labelling
// only so that the checker's functions have one shape); `sec` accepts a statement
// at a low program counter: the ledger, `emit` and the low variables receive only low values, a
// high expression is evaluated only where nothing it does is seen (`quiet`), and a branch on a
// high condition is confined (`conf`: it assigns only high variables, and performs no observable
// operation).
requires "../contract/contract.k"

module CONTRACTSEC-SYNTAX
  imports CONTRACT-SYNTAX
endmodule

module CONTRACTSEC
  imports CONTRACTSEC-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports K-EQUAL

  syntax Level ::= "lo" | "hi"

  syntax Level ::= join(Level, Level) [function, total]
  rule join(lo, L) => L
  rule join(hi, _) => hi

  syntax Bool ::= quiet(Expr, Map) [function, total]
  rule quiet(_:Int, _) => true
  rule quiet(_:Bool, _) => true
  rule quiet(_:Id, _) => true
  rule quiet(witness(), _) => true
  rule quiet(E1 + E2, G) => quiet(E1, G) andBool quiet(E2, G)
  rule quiet(E1 < E2, G) => quiet(E1, G) andBool quiet(E2, G)
  rule quiet(_, _) => false [owise]

  syntax Level ::= lev(Expr, Map) [function]
  rule lev(_:Int, _) => lo
  rule lev(_:Bool, _) => lo
  rule lev(X:Id, X |-> L:Level _:Map) => L
  rule lev(witness(), _) => hi
  rule lev(read(_), _) => lo
  rule lev(disclose(E), G) => lo requires lev(E, G) ==K lo orBool quiet(E, G)
  rule lev(E1 + E2, G) => join(lev(E1, G), lev(E2, G))
  rule lev(E1 < E2, G) => join(lev(E1, G), lev(E2, G))

  syntax Bool ::= conf(Stmt, Map) [function, total]
  rule conf({}, _) => true
  rule conf({ S }, G) => conf(S, G)
  rule conf(X:Id = E ;, G) => lev(X, G) ==K hi andBool quiet(E, G)
  rule conf(S1:Stmt S2:Stmt, G) => conf(S1, G) andBool conf(S2, G)
  rule conf(if (C) S1 else S2, G) => quiet(C, G) andBool conf(S1, G) andBool conf(S2, G)
  rule conf(repeat(_) S, G) => conf(S, G)
  rule conf(_, _) => false [owise]

  syntax Bool ::= sec(Stmt, Map) [function, total]
  rule sec({}, _) => true
  rule sec({ S }, G) => sec(S, G)
  rule sec(X:Id = E ;, G) => true requires lev(E, G) ==K lo orBool (lev(X, G) ==K hi andBool quiet(E, G))
  rule sec(write(_, E) ;, G) => true requires lev(E, G) ==K lo
  rule sec(emit(E) ;, G) => true requires lev(E, G) ==K lo
  rule sec(S1:Stmt S2:Stmt, G) => sec(S1, G) andBool sec(S2, G)
  rule sec(if (C) S1 else S2, G) => sec(S1, G) andBool sec(S2, G) requires lev(C, G) ==K lo
  rule sec(if (C) S1 else S2, G) => quiet(C, G) andBool conf(S1, G) andBool conf(S2, G) requires lev(C, G) ==K hi
  rule sec(repeat(_) S, G) => sec(S, G)
  rule sec(_, _) => false [owise]

  // a configuration only so that the definition compiles as a main module
  configuration <k> $PGM:Stmt </k>
endmodule
