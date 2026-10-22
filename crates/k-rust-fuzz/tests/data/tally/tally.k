// The loop-shaped stall benchmark (FZ-17): one rule, `eat`, applies every key of a `List` hole,
// `$KEYS`, that lies in a window whose bounds the definition states, and counts the keys it
// applied in a cell. It isolates what the bank (`bank/bank.k`) mixes with state-relative exact
// amounts: one more applied key reaches no rule an earlier case did not, so a set of covered
// rules gives the corpus no gradient, while the applied count of `eat` grows by one.
//
// - `eat` applies the next key when `1000 < X < 1100` and increments `<n>`.
// - `stop` (`owise`) ends every walk when `eat` does not apply, so every list ends naturally.
//
// The cells are pattern targets on the final configuration, `<n> N </n>` with `N >= d`
// (`tally/harness.rs`): no rule marks a depth, so no depth is a new rule.

module TALLY-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "count"  [symbol(count)]
endmodule

module TALLY
  imports TALLY-SYNTAX
  imports INT
  imports BOOL
  imports LIST

  syntax KItem ::= "next"  [symbol(next)]

  configuration <k> $PGM:Pgm </k>
                <keys> $KEYS:List </keys>
                <n> 0 </n>

  rule [begin]: <k> count => next ... </k>

  rule [eat]: <k> next ... </k> <keys> (ListItem(X:Int) => .List) ... </keys>
              <n> N => N +Int 1 </n>
    requires X >Int 1000 andBool X <Int 1100

  rule [stop]: <k> next => .K ... </k> [owise]
endmodule
