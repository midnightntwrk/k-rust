// The tally with a drain (FZ-17 fix round, from the FZ-17 review's probe): `tally.k`, plus a
// rewrite rule `drain` that consumes each key left after the loop, so an invalid key appended
// to a list puts `drain` in a new count bucket without bringing the depth cells any closer.
// The cells and the program are the tally's (`tally/harness.rs`).

module DRAIN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "count"  [symbol(count)]
endmodule

module DRAIN
  imports DRAIN-SYNTAX
  imports INT
  imports BOOL
  imports LIST

  syntax KItem ::= "next"   [symbol(next)]
                 | "drain"  [symbol(drain)]

  configuration <k> $PGM:Pgm </k>
                <keys> $KEYS:List </keys>
                <n> 0 </n>

  rule [begin]: <k> count => next ... </k>

  rule [eat]: <k> next ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
              <n> N => N +Int 1 </n>
    requires X >Int 1000 andBool X <Int 1100

  rule [stop]: <k> next => drain ... </k> [owise]
  rule [drain]: <k> drain ... </k> <keys> (ListItem(_) => .List) ... </keys>
  rule [drained]: <k> drain => .K ... </k> <keys> .List </keys>
endmodule
