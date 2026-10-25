// Mutant of vanish.k: only `plain`, which ends with 10. Its end 10 is outside the baseline's
// reported leaves {0}, yet the baseline reaches 10 in the model that lists key B first, so a
// kill is not established: the baseline is incomplete (`run_facts_off_leaves`, D16).

module VANISH-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= pick(Int, Int)  [symbol(pick)]
endmodule

module VANISH
  imports VANISH-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports K-EQUAL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [plain]: <k> pick(_, _) => .K ... </k> <out> _ => 10 </out>
endmodule
