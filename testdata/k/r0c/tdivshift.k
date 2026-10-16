// Re-pin R0c-fix-2: mutants that keep a baseline claim their edit does not reach, and contradict
// it. `td` is declared total and `pd` preserves-definedness, but both divide by their argument
// plus one, so at -1 the claims are false. `tdiv` and `go` shift the argument by one first, so the
// baseline never reaches -1 from tdiv(-1) or go(-1); a mutant of `tdiv` or `go` (rewrite rules,
// which redefine no symbol) that drops the shift does, and keeps both claims.
module TDIVSHIFT-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | pd(Int) [symbol(pd)]
                | go(Int) [symbol(go)]
                | val(Int) [symbol(val)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module TDIVSHIFT
  imports TDIVSHIFT-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 1)
  rule [tdiv]: <k> tdiv(I) => val(td(I +Int 1)) </k>
  rule [pd]: <k> pd(I) => val(10 /Int (I +Int 1)) </k> [preserves-definedness]
  rule [go]: <k> go(I) => pd(I +Int 1) </k>
endmodule
