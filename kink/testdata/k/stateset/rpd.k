// KINK-PD-SYMBOLIC-INSTANCE (D40), a known gap of kink's exclusion, from the KINK-PATHSET-FALLBACK
// review's probe: `g1` carries `preserves-definedness`, but its result `p(X, h(X))` is undefined
// at X = 0, where `h` divides by zero. k-rust records a contradicted `preserves-definedness`
// claim only where the declared rule's own successor normalization shows its result `\bottom`.
// - RPD-LATER, on the symbolic `a(X)`: that normalization is symbolic and finds nothing; the
//   `\bottom` shows one step later, when `pz` narrows X to 0, as a `Trivial` leaf naming `pz`. So
//   the run reaches an instance where g1's claim is false, yet it carries no record and no leaf
//   names a `preserves-definedness` rule: it is not excluded, in either modality.
// - RPD-GROUND, on the ground `a(0)`: g1's own step finds the `\bottom`, and the record excludes
//   the run in both modalities.
module RPD-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= a(Int) [symbol(a)]
                | c(Int, Int) [symbol(c)]
                | p(Int, Int) [symbol(p)]
  syntax Int ::= h(Int) [function, symbol(h)]
endmodule

module RPD-LATER
  imports RPD-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [h0]: h(0) => 1 /Int 0
  rule [g1]: <k> a(X) => p(X, h(X)) </k> [preserves-definedness]
  rule [pz]: <k> p(X, Y) => c(X, Y) </k> requires X ==Int 0
endmodule

module RPD-GROUND
  imports RPD-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [h0]: h(0) => 1 /Int 0
  rule [g1]: <k> a(X) => p(X, h(X)) </k> [preserves-definedness]
endmodule
