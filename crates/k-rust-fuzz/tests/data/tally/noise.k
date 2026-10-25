// The tally with noise (FZ-17 fix round, from the FZ-17 review's probe): `tally.k`, plus work
// at the end of the walk proportional to the keys left after the loop. `stop` stores
// `cnt(size(KS))` in `<j>`, and the equation `cnt-step` applies once per remaining key, so an
// invalid key appended to a list puts `cnt-step` in a new count bucket without bringing the
// depth cells any closer. The cells and the program are the tally's (`tally/harness.rs`).

module NOISE-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "count"  [symbol(count)]
endmodule

module NOISE
  imports NOISE-SYNTAX
  imports INT
  imports BOOL
  imports LIST

  syntax KItem ::= "next"  [symbol(next)]
  syntax Int ::= cnt(Int)  [function, total, symbol(cnt)]
  rule [cnt-step]: cnt(N) => 1 +Int cnt(N -Int 1) requires N >Int 0
  rule [cnt-zero]: cnt(_) => 0 [owise]

  configuration <k> $PGM:Pgm </k>
                <keys> $KEYS:List </keys>
                <n> 0 </n>
                <j> 0 </j>

  rule [begin]: <k> count => next ... </k>

  rule [eat]: <k> next ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
              <n> N => N +Int 1 </n>
    requires X >Int 1000 andBool X <Int 1100

  rule [stop]: <k> next => .K ... </k> <keys> KS </keys> <j> _ => cnt(size(KS)) </j> [owise]
endmodule
