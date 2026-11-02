// A fixture of `k2lean confluence --equiv` without threads (k2lean/docs/design.md, section 3.6):
// a map of jobs, each a number with whether it has run, run one at a time in any order. A job's
// step marks it run, adds it to `<total>` and appends it to `<done>`, so two runs end with one
// `<total>` but `<done>` in two orders: equal up to the order of its items (`--equiv done=perm`).
// A binding whose value is `true` from the start, or whose key is not an `Int`, never runs: the
// fixture claims no progress, only that the runs that end agree.
requires "domains.md"

module JOBS-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports MAP
endmodule

module JOBS
  imports JOBS-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL
  configuration <T>
      <jobs> $PGM:Map </jobs>
      <total> 0 </total>
      <done> .List </done>
    </T>

  rule <jobs> ... J:Int |-> (false => true) ... </jobs>
       <total> T => T +Int J </total>
       <done> ... (.List => ListItem(J)) </done> [label(run)]
endmodule
