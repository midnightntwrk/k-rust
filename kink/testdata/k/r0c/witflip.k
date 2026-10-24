// fz26 KINK-WITNESS: the pass the full check adopts flips between baseline and mutant (design
// P7-EMPTYJOIN review B2's `m`). `E` has no production; `s`'s pair joins only through the witness
// `ib(inj{E,B}(X)) => inj X` (as in `witness.k`), and `m`'s two equations, both at `m(X:E)`, join
// through it too (`ib(inj X)` and `inj X`), so the second pass is adopted. Editing `mid`'s
// right-hand side to `g(X)`, a declared partial function with no equation, makes `m`'s pair join
// only in the first pass (both sides stuck) and not in the second (`inj X` against `g(X)`), so
// the mutant's full check keeps its first pass, where `s`'s pair is not joined.
module WITFLIP-SYNTAX
  imports INT-SYNTAX
  syntax E
  syntax A ::= E | a(Int) [symbol(a)]
  syntax B ::= E | b(Int) [symbol(b)]
  syntax S ::= A | B
  syntax S ::= s(S) [function, symbol(s)]
  syntax A ::= da(A) [function, symbol(da)]
             | hd(Int) [symbol(hd)]
  syntax B ::= ib(B) [function, symbol(ib)]
             | m(E) [function, symbol(m)]
             | g(E) [function, symbol(g)]
  syntax Prog ::= go(Int) [symbol(go)] | val(S) [symbol(val)]
endmodule
module WITFLIP
  imports WITFLIP-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [sa]: s(X:A) => da(X)
  rule [sb]: s(X:B) => ib(X)
  rule [daa]: da(a(_)) => a(0)
  rule [daowise]: da(X) => X [owise]
  rule [ibb]: ib(b(_)) => b(0)
  rule [mib]: m(X:E) => ib(X)
  rule [mid]: m(X:E) => X
  rule [hd]: hd(K) => a(K) [anywhere]
  rule [go]: <k> go(I) => val(s(hd(I))) </k>
endmodule
