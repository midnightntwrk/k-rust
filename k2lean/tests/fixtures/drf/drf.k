// A fixture of `k2lean confluence` with a false slot (k2lean/docs/design.md, section 3.6): the
// fixture race with each worker writing its count to the shared accumulator once, instead of
// adding to it. Two workers with different counts race on `<acc>`: the last write wins, so two
// schedules end with different `<acc>`, and the slot of two `put` steps is refuted.
requires "domains.md"

module DRF-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "spawn" "(" Int ")" ";" Pgm | "done"
endmodule

module DRF
  imports DRF-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <T>
      <k> $PGM:Pgm </k>
      <workers> <worker multiplicity="*" type="Map"> <wid> 0 </wid> <todo> 0 </todo> </worker> </workers>
      <acc> 0 </acc>
      <next> 0 </next>
    </T>

  rule <worker> <wid> _ </wid> <todo> C => 0 </todo> </worker>
       <acc> _ => C </acc>
    requires C >Int 0 [label(put)]
  rule <k> spawn ( N ) ; P => P ... </k>
       <workers> (.Bag => <worker> <wid> I </wid> <todo> N </todo> </worker>) ... </workers>
       <next> I => I +Int 1 </next> [label(spawn)]
  rule <k> done => .K ... </k> [label(stop)]
endmodule
