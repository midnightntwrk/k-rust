// Kill-soundness audit fixture (KS-07). `write` states its guard as a range that holds for
// exactly one address, so `A ==Int 1` is an equivalent rephrasing (AS2). `loadZero` has a
// higher priority than the observed `load`, whose pre-state on a symbolic address is the
// remainder of `loadZero`'s guard (AS6). `load` carries `preserves-definedness` over the
// total function `norm`, so a patch of `norm` withdraws that claim from `load` (AS7).
module GUARDEDEQ-SYNTAX
  imports INT-SYNTAX
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
  syntax Prog ::= "halt" [symbol(halt)] | "fault" [symbol(fault)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module GUARDEDEQ
  imports GUARDEDEQ-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  syntax Int ::= norm(Int) [function, total, symbol(norm)]
  rule [norm]: norm(X) => X

  rule [write]:      seq(write(addr(A), V), P) => P requires A >=Int 1 andBool A <=Int 1
  rule [writeOther]: seq(write(addr(A), _), _) => fault requires A <Int 1 orBool A >Int 1
  rule [loadZero]:   seq(load(addr(A), _), P) => P requires A ==Int 0 [priority(40)]
  rule [load]:       seq(load(addr(A), V), P) => P requires norm(A) ==Int A [preserves-definedness]
endmodule
