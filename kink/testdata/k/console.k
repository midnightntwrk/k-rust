// A free-running console, for kink-campaign's observation slot (`Observe`, tests/observation.rs).
// `tick` advances the count `<n>` and the phase `<phase>`, a bookkeeping cell; every third step is
// `emit`, which resets the phase and appends `show(N)` to the `<out>` log. No run of `run` ends on
// its own, so a run is compared over the prefix its depth bound explores. `show` is declared total
// but has a value only below 5, so `show(6)`, the third item a run of `run` appends, stays in the
// log as a residue, an item that is no value. `halt`, `stall`, `jump`, `fall` and `rewrite` are
// guarded so that no run of `run` from a count of 0 takes them; a test that starts elsewhere
// reaches them: from 1000001 `halt` ends the run at once; from -50 `fall` beside `tick` makes a
// sibling path that ends at once; from -22 `rewrite` replaces the log's first item after the first
// emit, so the log does not only grow by appending. The mutations the tests make: tick's count
// step 1 becomes 2, 0 or 3 (with 3 the first item is the residue `show(6)`); emit's phase reset 0
// becomes 1 (every second step emits, and the second item is 3); halt's bound becomes 2 (the run
// ends before its fourth tick), 999999 or 1000001; stall's bound becomes 2 (the count stops and the
// phase runs on unobserved); jump's -1 becomes 1 (the second tick has a sibling); tick is deleted;
// an `anywhere` rule heading `done` is inserted. `f` is partial, defined below 10 by its `#Ceil`
// lemma, and no run of `run` reads `f` or `h`; a test that starts with `f(h(0))` in `<phase>` and
// `h(0)` in `<out>` runs as from a count of 0 with the log's first item 1, until h's step 1 becomes
// 20: the initial configuration then holds `f(20)`, which has no instance, and the run is vacuous.
module CONSOLE-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "run" [symbol(run)]
               | "done" [symbol(done)]
endmodule
module CONSOLE
  imports CONSOLE-SYNTAX
  imports INT
  imports BOOL
  imports LIST
  imports ML-SYNTAX
  configuration <k> $PGM:Cmd </k> <n> 0 </n> <phase> 0 </phase> <out> .List </out>
  syntax Int ::= show(Int) [function, total, symbol(show)]
  rule [show]: show(N) => N requires N <Int 5
  syntax Int ::= f(Int) [function, symbol(f)]
               | h(Int) [function, symbol(h)]
  rule [f]: f(X) => X -Int 1 requires X <Int 10
  rule [fceil]: #Ceil(f(X)) => {(X <Int 10) #Equals true} [simplification]
  rule [h]: h(X) => X +Int 1
  rule [tick]: <k> run </k> <n> N => N +Int 1 </n> <phase> P => P +Int 1 </phase> requires P <Int 2
  rule [emit]: <k> run </k> <n> N </n> <phase> 2 => 0 </phase> <out> L => L ListItem(show(N)) </out>
  rule [halt]: <k> run => done </k> <n> N </n> requires N >Int 1000000 [priority(10)]
  rule [stall]: <k> run </k> <n> N </n> <phase> P => P +Int 10 </phase> requires N >Int 1000000 [priority(20)]
  rule [jump]: <k> run </k> <n> N => N +Int 100 </n> requires N ==Int -1
  rule [fall]: <k> run => done </k> <n> N </n> requires N ==Int -50
  rule [rewrite]: <k> run </k> <n> N => N +Int 1 </n> <out> ListItem(_) L => ListItem(0) L </out> requires N ==Int -20 [priority(10)]
endmodule
