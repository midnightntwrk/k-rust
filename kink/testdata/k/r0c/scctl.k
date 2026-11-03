// CF-01's controls that stay excluded: a notBool, orBool or orElseBool shape whose skippable
// operand is X /Int Y with Y a program input, in the Bool term of a rule's condition, of an
// equation's condition, and of that condition as the owise equation beside it reaches it (the
// test also drops each first equation, so that only the owise guard holds it). In each C the
// skippable operand stands below an operator other than the conjunctions at C's top, where the
// readings can differ as true versus \bottom (notBool (false andThenBool u), true orBool u, true
// orElseBool u), and X /Int Y owes Y =/=Int 0, which no other operand evaluates.
module SCCTL-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= go(Int, Int) [symbol(go)] | res(Int) [symbol(res)]
                | rnb(Int, Int) [symbol(rnb)] | rob(Int, Int) [symbol(rob)]
                | roe(Int, Int) [symbol(roe)]
  syntax Int ::= nb(Int, Int) [function, symbol(nb)]
               | ob(Int, Int) [function, symbol(ob)]
               | oe(Int, Int) [function, symbol(oe)]
endmodule
module SCCTL
  imports SCCTL-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [nb1]: nb(X, Y) => 1 requires notBool (X >=Int 0 andThenBool X /Int Y ==Int 0)
  rule [nb2]: nb(_, _) => 0 [owise]
  rule [ob1]: ob(X, Y) => 1 requires X >=Int 0 orBool X /Int Y ==Int 0
  rule [ob2]: ob(_, _) => 0 [owise]
  rule [oe1]: oe(X, Y) => 1 requires X >=Int 0 orElseBool X /Int Y ==Int 0
  rule [oe2]: oe(_, _) => 0 [owise]
  rule [go]: <k> go(X, Y) => res(nb(X, Y) +Int ob(X, Y) +Int oe(X, Y)) </k>
  rule [rnb]: <k> rnb(X, Y) => res(1) </k> requires notBool (X >=Int 0 andThenBool X /Int Y ==Int 0)
  rule [rob]: <k> rob(X, Y) => res(1) </k> requires X >=Int 0 orBool X /Int Y ==Int 0
  rule [roe]: <k> roe(X, Y) => res(1) </k> requires X >=Int 0 orElseBool X /Int Y ==Int 0
endmodule
