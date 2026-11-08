// A nondeterministic console, for kink-campaign's observation slot over several paths
// (`Observe`, tests/observation.rs). From a count of 0, `run` takes one of three steps to `go`,
// each appending one item to the `<out>` log: `left` appends 1, `right` appends 2 and `again`
// appends 1 as `left` does, so the run has three paths, two of which reach one state with one
// history, and its log's prefix set is {1, 2}; `finish` then ends each path at `done`. `extra`
// appends 3 and is guarded so that no run from 0 takes it; from 7 `seven` appends 1 and `loop`
// steps `run` to itself, so a run from 7 has a path at every depth that has appended nothing
// when the depth bound cuts it. The mutations the tests make: extra's -1 becomes 0 (a third
// behaviour, 3) or 7 (a behaviour beside the unexplored one); right's 0 becomes 5 (the
// behaviour 2 is dropped); left is deleted (the paths 1 and 2 are explored in another order).
module CHOICE-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "run" [symbol(run)]
               | "go" [symbol(go)]
               | "done" [symbol(done)]
endmodule
module CHOICE
  imports CHOICE-SYNTAX
  imports INT
  imports BOOL
  imports LIST
  configuration <k> $PGM:Cmd </k> <n> 0 </n> <out> .List </out>
  rule [left]: <k> run => go </k> <n> N </n> <out> L => L ListItem(1) </out> requires N ==Int 0
  rule [right]: <k> run => go </k> <n> N </n> <out> L => L ListItem(2) </out> requires N ==Int 0
  rule [again]: <k> run => go </k> <n> N </n> <out> L => L ListItem(1) </out> requires N ==Int 0
  rule [extra]: <k> run => go </k> <n> N </n> <out> L => L ListItem(3) </out> requires N ==Int -1
  rule [seven]: <k> run => go </k> <n> N </n> <out> L => L ListItem(1) </out> requires N ==Int 7
  rule [loop]: <k> run => run </k> <n> N </n> requires N ==Int 7
  rule [finish]: <k> go => done </k>
endmodule
