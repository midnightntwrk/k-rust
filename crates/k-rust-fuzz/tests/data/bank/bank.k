// The ledger-shaped stall benchmark (FZ-14 round 2): one rule applies every transaction of a
// `List` hole, `$TXS`, under guards relative to the state, as a bank applies transfers. It is
// the case the lock (`lock/lock.k`) leaves out: there, each key fires its own rule, so coverage
// sees every key the corpus gets right; here, one more applied transaction reaches no rule an
// earlier case did not, and its constants depend on the running balance, not on the definition.
//
// - `$TXS` is a list of `tx(N, A)`: a transaction with nonce `N` and amount `A` (a deposit when
//   positive, a withdrawal when negative).
// - `pay` applies the next transaction when its nonce is the account's nonce and it neither
//   overdraws the balance nor more than doubles it: `-B <= A <= B`. The balance starts at 100,
//   a constant of the configuration, not of any rule.
// - `double` (tried first, `priority(40)`) applies a transaction that exactly doubles the
//   balance, from the third transaction on: its amount must equal the running balance.
// - `rich` ends a list whose every transaction applied, when at least five did and the balance
//   reached 2000: since no step more than doubles, the five amounts must each be near the
//   running balance (100, 200, 400, 800, 1600 reach 3200).
// - `broke` is unreachable (a negative control): `pay` never lets the balance go negative.
//
// `close` (`owise`) ends every other walk, so every list ends naturally with an empty `<k>`, and
// the rules of one state are disjoint, so every list has one path.
// `research/stall-benchmark.md` in the fz26 notes gives the measurements.

module BANK-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "run"  [symbol(run)]
endmodule

module BANK
  imports BANK-SYNTAX
  imports INT
  imports BOOL
  imports LIST

  syntax Tx ::= tx(Int, Int)  [symbol(tx)]
  syntax KItem ::= "apply"    [symbol(apply)]

  configuration <k> $PGM:Pgm </k>
                <txs> $TXS:List </txs>
                <nonce> 0 </nonce>
                <balance> 100 </balance>

  rule [begin]: <k> run => apply ... </k>

  rule [double]: <k> apply ... </k> <txs> (ListItem(tx(N, A)) => .List) ... </txs>
                 <nonce> M => M +Int 1 </nonce> <balance> B => B +Int A </balance>
    requires N ==Int M andBool M >=Int 2 andBool A ==Int B
    [priority(40)]
  rule [pay]: <k> apply ... </k> <txs> (ListItem(tx(N, A)) => .List) ... </txs>
              <nonce> M => M +Int 1 </nonce> <balance> B => B +Int A </balance>
    requires N ==Int M andBool 0 -Int B <=Int A andBool A <=Int B

  rule [rich]: <k> apply => .K ... </k> <txs> .List </txs> <nonce> M </nonce>
               <balance> B </balance>
    requires M >=Int 5 andBool B >=Int 2000
  rule [broke]: <k> apply => .K ... </k> <balance> B </balance> requires B <Int 0

  rule [close]: <k> apply => .K ... </k> [owise]
endmodule
