// Several cells: rules that read and rewrite cells besides <k> in one step, a requires over a cell
// the rule rewrites, a cell a rule matches without rewriting it, the cells a rule does not mention
// kept, and the initial values the configuration declares for the cells besides <k>.
module CASE-SYNTAX
  imports INT-SYNTAX
  syntax S ::= go(Int) | step(Int) | done(Int)
endmodule
module CASE
  imports CASE-SYNTAX
  imports INT
  imports BOOL
  configuration <t> <k> $PGM:S </k> <acc> 0 </acc> <cnt> 1 </cnt> </t>
  rule <k> go(N) => step(N) </k> <acc> A => A +Int 10 </acc>
  rule <k> step(N) => step(N -Int 1) </k> <acc> A => A +Int N </acc> <cnt> C => C *Int 2 </cnt>
    requires N >Int 0 andBool A <Int 100
  rule <k> step(0) => done(C) </k> <cnt> C </cnt>
endmodule
