// A function equation that blocks a lower one with a match left undecided
// (`offered_mutation.rs`): matching `0` against `gx(5)` is undecided, so `feC` blocks `feLo` in
// `fe(gx(5))` and is in `offered` only; lowered below `feLo`, it lets `feLo` apply.
module LOWER-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= ge(Int) [symbol(ge)] | val(Int) [symbol(val)]
endmodule

module LOWER
  imports LOWER-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Int ::= fe(Int) [function, symbol(fe)]
               | gx(Int) [function, total, no-evaluators, symbol(gx)]
  rule [feC]:  fe(0) => 1 [priority(50)]
  rule [feLo]: fe(_) => 0 [priority(60)]
  rule [ge]:   <k> ge(X) => val(fe(gx(X))) </k>
endmodule
