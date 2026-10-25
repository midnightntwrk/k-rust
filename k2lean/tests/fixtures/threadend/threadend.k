// Threads in a cell map: a step of one thread, and the end of a thread whose `<k>` is empty, which
// removes it and is matched at the key `<id> _ </id>` rather than at a variable
// (crates/k2lean/tests/cli.rs: `confluence --report-only` separates the two at one binding).
requires "domains.md"

module THREADEND-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "work"
endmodule

module THREADEND
  imports THREADEND-SYNTAX
  imports INT
  configuration <T>
      <threads> <thread multiplicity="*" type="Map" initial=""> <id> 0 </id> <k> $PGM:Pgm </k> <cnt> 0 </cnt> </thread> </threads>
      <ended> 0 </ended>
    </T>

  rule <k> work => .K ... </k> <cnt> C => C +Int 1 </cnt> [label(step)]
  rule <threads> (<thread> <id> _ </id> <k> .K </k> ... </thread> => .Bag) ... </threads>
       <ended> N => N +Int 1 </ended> [label(end)]
endmodule
