// A definition whose load observes a contradicted claim. `td` is declared `total`, but its
// equation reduces `td(0)` to `10 /Int 0`, which is undefined. The two `anywhere` equations of
// `g` overlap, and the load's critical-pair check simplifies the first one's condition through
// `td(0)`: the load records the contradicted `total` claim (`observedIn: load`). No program
// evaluates `td` or `g`, so every run lists that record and no leaf carries it.

module LOADCLAIM-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module LOADCLAIM
  imports LOADCLAIM-SYNTAX
  imports INT
  imports BOOL

  syntax Int ::= td(Int)  [function, total, symbol(td)]
  syntax Foo ::= g(Int) | "a" | "b"

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [tdeq]:     td(I) => 10 /Int (I +Int 0)
  rule [ga]:       g(_X) => a requires td(0) ==Int 1 [anywhere]
  rule [gb]:       g(_X) => b [anywhere]
  rule [go-big]:   <k> go(N) => .K ... </k> <out> _ => 1 </out> requires N >Int 100
  rule [go-small]: <k> go(N) => .K ... </k> <out> _ => 0 </out> requires N <=Int 100
endmodule
