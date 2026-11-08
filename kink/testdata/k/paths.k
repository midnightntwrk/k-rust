// Paths a run splits into, for kink-campaign's observation slot over several paths (`Observe`,
// tests/observation.rs). From `pick`, `one` sets `<n>` to 1 and `two` sets it to 2, and `settle`
// then sets it to 0 at `done`: the two paths reach one configuration at one depth, having observed
// different values of `<n>`. From `fan`, `low` sets `<n>` to 1, `high` to 2 and `odd` to
// `part(3)`, an application of a partial function that no equation reduces, so its value is not
// known; `finish` then ends each path at `done`. The mutations the tests make: two's 2 becomes 1
// (the behaviour 2 is dropped); low's 1 becomes 7 (a behaviour no explored baseline path has).
module PATHS-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "pick" [symbol(pick)]
               | "mid" [symbol(mid)]
               | "fan" [symbol(fan)]
               | "go" [symbol(go)]
               | "done" [symbol(done)]
endmodule
module PATHS
  imports PATHS-SYNTAX
  imports INT
  syntax Int ::= part(Int) [function, symbol(part)]
  rule part(0) => 0
  configuration <k> $PGM:Cmd </k> <n> 0 </n>
  rule [one]: <k> pick => mid </k> <n> _ => 1 </n>
  rule [two]: <k> pick => mid </k> <n> _ => 2 </n>
  rule [settle]: <k> mid => done </k> <n> _ => 0 </n>
  rule [low]: <k> fan => go </k> <n> _ => 1 </n>
  rule [high]: <k> fan => go </k> <n> _ => 2 </n>
  rule [odd]: <k> fan => go </k> <n> _ => part(3) </n>
  rule [finish]: <k> go => done </k>
endmodule
