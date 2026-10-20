// Data sorts declared in the semantic module whose values may or may not contain program
// syntax or computations, for the transitive hole-sort rule (ARCHITECTURE 2.4 as amended by
// D17): `Pair` holds only integers and is data; `Job` wraps a `Stmt`, `Nested` reaches one
// through `Job`, and `Bag` holds a `List` without declared element sorts (so `KItem`s).

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

  syntax Pair   ::= pair(Int, Int)  [symbol(pair)]
  syntax Job    ::= exec(Stmt)      [symbol(exec)]
                  | "idle"          [symbol(idle)]
  syntax Nested ::= nest(Pair)      [symbol(nest)]
                  | wrap(Job)       [symbol(wrap)]
  syntax Bag    ::= bag(List)       [symbol(bag)]

  configuration <k> $PGM:Pgm </k>
                <job> idle </job>

  rule [run]: <k> _:Stmt => .K ... </k>
endmodule
