// fz26 KINK-WITNESS: a witness equation's source edited. `E` has no production, so its carrier in
// `M+` is one fresh constant. `s`'s two equations overlap at that constant, where `da`'s `owise`
// gives it back and `ib`, a declared partial function with no equation for it, is stuck: the full
// check joins the pair through the witness `ib(inj{E,B}(X)) => inj X`, proposed by `s`'s pair
// (relevant through the equation head `hd`). `s2`'s pair joins alike through a witness at `ic`.
// `t`'s pair joins only through `ib`'s witness and reaches neither `da` nor `s`. Deleting
// `daowise` takes `ib`'s witness away while `ic`'s keeps the witness pass adopted, so only the
// witness diff (`ib`, reached by `t`) puts `t`'s pair under the check.
module WITNESS-SYNTAX
  imports INT-SYNTAX
  syntax E
  syntax A ::= E | a(Int) [symbol(a)]
  syntax B ::= E | b(Int) [symbol(b)]
  syntax C ::= E | c(Int) [symbol(c)]
  syntax S ::= A | B | C
  syntax S ::= s(S) [function, symbol(s)]
             | s2(S) [function, symbol(s2)]
  syntax A ::= da(A) [function, symbol(da)]
             | dc(A) [function, symbol(dc)]
             | hd(Int) [symbol(hd)]
  syntax B ::= ib(B) [function, symbol(ib)]
             | t(B) [function, symbol(t)]
  syntax C ::= ic(C) [function, symbol(ic)]
  syntax Prog ::= go(Int) [symbol(go)] | val(S) [symbol(val)]
endmodule
module WITNESS
  imports WITNESS-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [sa]: s(X:A) => da(X)
  rule [sb]: s(X:B) => ib(X)
  rule [daa]: da(a(_)) => a(0)
  rule [daowise]: da(X) => X [owise]
  rule [ibb]: ib(b(_)) => b(0)
  rule [s2a]: s2(X:A) => dc(X)
  rule [s2c]: s2(X:C) => ic(X)
  rule [dca]: dc(a(_)) => a(1)
  rule [dcowise]: dc(X) => X [owise]
  rule [icc]: ic(c(_)) => c(0)
  rule [tb]: t(X:B) => ib(X)
  rule [te]: t(X:E) => X
  rule [hd]: hd(K) => a(K) [anywhere]
  rule [go]: <k> go(I) => val(s(hd(I))) </k>
endmodule
