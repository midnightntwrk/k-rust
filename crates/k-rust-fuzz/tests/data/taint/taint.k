// Leaves that end with an empty <k> but are not clean (ARCHITECTURE.md 5.2).
//
// - `get(K)` writes `find(1 |-> 10, K)`. `find` is a partial function whose only equation needs
//   `K in_keys(M)`, so for a missing key no equation applies. `get(2)` has two leaves: a `stuck`
//   one with an empty <k>, no constraint and no diagnostic that holds the unevaluated
//   application, whose internalized term is not `ceil_free`; and the undefined step (`trivial`,
//   rule `get`) under `#Not(#Ceil(find(...)))`.
// - `look(K)` writes the hooked lookup `(1 |-> 10) [ K ]`, which is undefined for a missing key:
//   the step is an undefined step (`trivial`), not a leaf holding the lookup.
// - `guard(I)` takes `guard-ok` when `td(I) >Int 0`. `td` is declared `total`, but `td(0)`
//   reduces to `10 /Int 0`, so for I = 0 this run refutes the condition through a contradicted
//   claim, and `guard-else` ends the program: the leaf carries a `contradicted-claim` record
//   observed by the run (`observedIn: run`).

module TAINT-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= get(Int)    [symbol(getPgm)]
               | look(Int)   [symbol(look)]
               | guard(Int)  [symbol(guard)]
endmodule

module TAINT
  imports TAINT-SYNTAX
  imports INT
  imports BOOL
  imports MAP

  syntax KItem ::= find(Map, KItem)  [function, symbol(find)]
  syntax Int   ::= td(Int)           [function, total, symbol(td)]

  configuration <k> $PGM:Pgm </k>
                <out> .K </out>

  rule [find]:       find(M, K) => M [ K ] requires K in_keys(M)
  rule [tdeq]:       td(I) => 10 /Int I

  rule [get]:        <k> get(K) => .K ... </k> <out> _ => find(1 |-> 10, K) </out>
  rule [look]:       <k> look(K) => .K ... </k> <out> _ => (1 |-> 10) [ K ] </out>
  rule [guard-ok]:   <k> guard(I) => .K ... </k> <out> _ => 1 </out> requires td(I) >Int 0
  rule [guard-else]: <k> guard(_) => .K ... </k> <out> _ => 0 </out> [owise]
endmodule
