// A fixture of `k2lean confluence --equiv` (k2lean/docs/design.md, section 3.6): the fixture race
// with each unit of work logged. A worker's step appends its id to `<log>`, so two schedules end
// with the same `<acc>` but their logs in different orders: the configurations differ, and are
// equal up to the order of the log's items (`--equiv log=perm`). `<last>` holds the id of the last
// worker to step, which no rule reads (`--equiv last=any`).
requires "domains.md"

module RACELOG-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "spawn" "(" Int ")" ";" Pgm | "done"
endmodule

module RACELOG
  imports RACELOG-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL
  configuration <T>
      <k> $PGM:Pgm </k>
      <workers> <worker multiplicity="*" type="Map"> <wid> 0 </wid> <todo> 0 </todo> </worker> </workers>
      <acc> 0 </acc>
      <log> .List </log>
      <last> -1 </last>
      <next> 0 </next>
    </T>

  rule <worker> <wid> W </wid> <todo> C => C -Int 1 </todo> </worker>
       <acc> A => A +Int C </acc>
       <log> ... (.List => ListItem(W)) </log>
       <last> _ => W </last>
    requires C >Int 0 [label(work)]
  rule <k> spawn ( N ) ; P => P ... </k>
       <workers> (.Bag => <worker> <wid> I </wid> <todo> N </todo> </worker>) ... </workers>
       <next> I => I +Int 1 </next> [label(spawn)]
  rule <k> done => .K ... </k> [label(stop)]

  // `gen --step-property accUp@acc --step-property-trans`: the accumulated work never decreases
  // (`work` adds a worker's `C` under `C >Int 0`, matching the worker in the `<workers>` cell map)
  syntax Bool ::= accUp(Int, Int) [function, total]
  rule accUp(A1, A2) => A1 <=Int A2
endmodule
