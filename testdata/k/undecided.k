// Evidence the no-Z3 profile cannot decide. `open(z)` has no equation, so an
// `ensures open(z)` is carried as a path condition; recursive `grow` is a
// simplification equation that exhausts a small budget; and `isZero` refutes
// the substitution of `support::deferred_vacuous_state` only after `step`.
// `carry` and `slow` never apply in the baseline; their mutants replace `requires false`.
module UNDECIDED-SYNTAX
  imports SORT-BOOL
  syntax Nat ::= "z" [symbol(z)]
               | s(Nat) [symbol(s)]
  syntax S ::= "carry" [symbol(carry)]
             | "carryAlways" [symbol(carryAlways)]
             | "carried" [symbol(carried)]
             | "draining" [symbol(draining)]
             | drained(Nat) [symbol(drained)]
             | "vacuous" [symbol(vacuous)]
             | "reached" [symbol(reached)]
  syntax Bool ::= open(Nat) [function, total, symbol(open)]
                | isZero(Nat) [function, total, symbol(isZero)]
  syntax Nat ::= grow(Nat) [function, total, symbol(grow)]
endmodule

module UNDECIDED
  imports UNDECIDED-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule isZero(z) => true
  rule isZero(s(_)) => false
  rule grow(N) => grow(grow(N)) [simplification]

  rule [carry]: carry => carried requires false ensures open(z)
  rule [carryAlways]: carryAlways => carried ensures open(z)
  rule [slow]: draining => drained(grow(z)) requires false
  rule [step]: vacuous => reached
endmodule
