// Data sorts declared in the semantic module whose values may or may not contain program
// syntax or computations, for the transitive hole-sort rule (ARCHITECTURE 2.4 as amended by
// D17): `Pair` holds only integers and is data; `Job` wraps a `Stmt`, `Nested` reaches one
// through `Job`, and `Sack` holds a `List` without declared element sorts (so `KItem`s).
// `Box` is built by a parametric constructor, whose argument may be of any sort; `Ledger` has a
// helper function over a `Map`, which builds no `Ledger` value; `Both` holds an `Id` and a
// `Stmt`, two refusals at once.

module WRAPS-SYNTAX
  imports INT-SYNTAX

  syntax Exp  ::= Int
                | Exp "+" Exp       [symbol(plus), left]
  syntax Stmt ::= "print" Exp ";"   [symbol(print)]
  syntax Pgm  ::= Stmt
endmodule

module WRAPS
  imports WRAPS-SYNTAX
  imports INT
  imports LIST
  imports MAP
  imports ID

  syntax Pair   ::= pair(Int, Int)  [symbol(pair)]
  syntax Job    ::= exec(Stmt)      [symbol(exec)]
                  | "idle"          [symbol(idle)]
  syntax Nested ::= nest(Pair)      [symbol(nest)]
                  | wrap(Job)       [symbol(wrap)]
  syntax Sack   ::= sack(List)      [symbol(sack)]
  syntax {S} Box ::= box(S)         [symbol(box)]
  syntax Ledger ::= ledger(Int)     [symbol(ledger)]
                  | touch(Ledger, Map) [function, symbol(touch)]
  syntax Both   ::= both(Id, Stmt)  [symbol(both)]

  rule touch(L, _) => L

  configuration <k> $PGM:Pgm </k>
                <job> idle </job>

  rule [run]: <k> _:Stmt => .K ... </k>
endmodule
