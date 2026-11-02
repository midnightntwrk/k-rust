// A fixture of `k2lean gen --invariant` (k2lean/docs/invariants.md): invariants that read cells
// through K's `Bool` equality connectives. `<a>`, `<b>` and `<c>` are flags that `set(X)` writes
// together (`mirror`: `<a>` and `<b>` agree and `<c>` is their negation, by `==Bool`, `=/=Bool`
// and `xorBool`); `<zero>` caches whether `<n>` is zero, which `put(I)` writes with the call
// `isZero(I)` (`cached`: `Z ==Bool isZero(N)`, a call on the right-hand side).
module FLAGS-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Cmd ::= "set" "(" Bool ")" | "put" "(" Int ")"
  syntax Pgm ::= Cmd ";" Pgm | "done"
endmodule

module FLAGS
  imports FLAGS-SYNTAX
  imports INT
  imports BOOL
  configuration <T>
      <k> $PGM:Pgm </k>
      <a> true </a> <b> true </b> <c> false </c>
      <n> 0 </n> <zero> true </zero>
    </T>

  rule <k> C:Cmd ; P => C ~> P ... </k> [label(seq)]
  rule <k> done => .K ... </k> [label(done)]
  rule <k> set(X) => .K ... </k> <a> _ => X </a> <b> _ => X </b> <c> _ => notBool X </c> [label(set)]
  rule <k> put(I) => .K ... </k> <n> _ => I </n> <zero> _ => isZero(I) </zero> [label(put)]

  syntax Bool ::= isZero(Int) [function, total]
  rule isZero(I) => I ==Int 0

  syntax Bool ::= mirror(TCell) [function, total]
                | cached(TCell) [function, total]
  rule mirror(<T> <k> _ </k> <a> A </a> <b> B </b> <c> C </c> <n> _ </n> <zero> _ </zero> </T>)
    => (A ==Bool B) andBool (A =/=Bool C) andBool (B xorBool C)
  rule cached(<T> <k> _ </k> <a> _ </a> <b> _ </b> <c> _ </c> <n> N </n> <zero> Z </zero> </T>)
    => Z ==Bool isZero(N)
endmodule
