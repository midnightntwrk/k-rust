// The probe of a function clause of priority above `[owise]`'s 200: `hi-top`, of priority 250,
// decides only where `hi-z` (50) and `hi-ow` (200) both fail, and `hi-ow` applies at every
// argument, so `hi-top` never decides: `hi(0)` is 1 and `hi(5)` is 2.
module FPRIO-REFUSED-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "t1" [symbol(t1)]
endmodule

module FPRIO-REFUSED
  imports FPRIO-REFUSED-SYNTAX
  imports INT
  configuration <k> $PGM:Cmd </k>

  syntax Int ::= hi(Int) [function, symbol(hi)]
  rule [hi-z]: hi(0) => 1
  rule [hi-top]: hi(_) => 3 [priority(250)]
  rule [hi-ow]: hi(_) => 2 [owise]

  syntax KItem ::= res(Int) [symbol(res)]
  rule [t1]: <k> t1 => res(hi(5)) </k>
endmodule
