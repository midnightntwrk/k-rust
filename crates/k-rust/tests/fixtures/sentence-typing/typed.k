module TYPED-SYNTAX
  imports SORT-BOOL
  imports INT-SYNTAX
  syntax Nat ::= "z" [symbol(z)]
               | s(Nat) [symbol(s)]
  syntax Counter ::= counter(Nat, Nat) [symbol(counter)]
  syntax Control ::= choose(Bool) [symbol(choose)]
                   | selected(Bool) [symbol(selected)]
  syntax Small ::= "one" [symbol(one)]
  syntax Exp ::= Int | Nat | Small
  syntax Exp ::= neg(Exp) [symbol(negExp), overload(neg)]
  syntax Small ::= neg(Small) [symbol(negSmall), overload(neg)]
  syntax Exp ::= plus(Exp, Exp) [symbol(plus)]
  syntax {S} S ::= id(S) [symbol(id)]
endmodule


module TYPED
  imports TYPED-SYNTAX
  imports BASIC-K
  configuration <k> .K </k> <count> z </count>

  rule [increment]: counter(N, s(L)) => counter(s(N), L)
  rule [branch]: choose(B) => selected(B) requires B
  rule [overload]: neg(S:Small) => neg(neg(S))
  rule [cell]: <k> plus(E, z) => E ... </k> <count> C => s(C) </count>
  rule [anonymous]: plus(_:Int, _:Nat) => z
endmodule
