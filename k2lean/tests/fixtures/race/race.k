// The fixture of `k2lean confluence` (k2lean/docs/design.md, section 3.6): workers in a cell map
// each add their count to a shared accumulator, one unit of work at a time, in any interleaving;
// `spawn(N)` adds a worker with a fresh id and count N. Every schedule ends with the same `<acc>`
// (addition commutes), and in fact in the same configuration.
requires "domains.md"

module RACE-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "spawn" "(" Int ")" ";" Pgm | "done"
endmodule

module RACE
  imports RACE-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <T>
      <k> $PGM:Pgm </k>
      <workers> <worker multiplicity="*" type="Map"> <wid> 0 </wid> <todo> 0 </todo> </worker> </workers>
      <acc> 0 </acc>
      <next> 0 </next>
    </T>

  rule <worker> <wid> _ </wid> <todo> C => C -Int 1 </todo> </worker>
       <acc> A => A +Int C </acc>
    requires C >Int 0 [label(work)]
  rule <k> spawn ( N ) ; P => P ... </k>
       <workers> (.Bag => <worker> <wid> I </wid> <todo> N </todo> </worker>) ... </workers>
       <next> I => I +Int 1 </next> [label(spawn)]
  rule <k> done => .K ... </k> [label(stop)]
endmodule
