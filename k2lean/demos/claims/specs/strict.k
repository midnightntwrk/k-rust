// A strict operator in a definition whose `Step` is not a function: `+` is strict in both
// arguments, so either one heats first (two successors), and its cooling rules match the item
// after the hole. Example material of `k2lean claims` (demos/claims/specs/strict-spec.k): where a
// claim leaves the rest of `<k>` symbolic, those matchers read the rest before the hole and do not
// reduce, and `kc_auto` steps by the cases of `Step` itself (design.md §3.8).

module STRICT-SYNTAX
  imports INT-SYNTAX
  syntax KResult ::= Int
  syntax Exp ::= Int
               | Exp "+" Exp [strict, symbol(plus)]
endmodule

module STRICT
  imports STRICT-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  rule I1:Int + I2:Int => I1 +Int I2
endmodule
