// The condition shapes of `condition_records.rs` (FZ-G7): K Boolean connectives over operands that
// may be undefined (`/Int` by zero), a partial Boolean function without an equation for its
// argument, and a conjunction. Adapted from the FZ-G7 review's probe definition.
module CONDITIONS-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= neg(Int, Int)       [symbol(neg)]
               | two(Int, Int)       [symbol(two)]
               | strictneg(Int, Int) [symbol(strictneg)]
               | lazy(Int, Int)      [symbol(lazy)]
endmodule

module CONDITIONS
  imports CONDITIONS-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= done(Int)
  syntax Bool ::= pb(Int) [function, symbol(pb)]
  rule pb(0) => true

  configuration <T> <k> $PGM:Pgm </k> </T>

  rule [negdiv]: <k> neg(X, Y) => done(X) ... </k> requires notBool (X /Int Y >Int 3)
  rule [twoc]: <k> two(X, Y) => done(X) ... </k> requires X >Int 0 andBool Y <Int 10
  rule [pbneg]: <k> strictneg(X, _Y) => done(X) ... </k> requires notBool pb(X)
  rule [lazyr]: <k> lazy(X, Y) => done(X) ... </k> requires Y =/=Int 0 andThenBool X /Int Y >Int 1
endmodule
