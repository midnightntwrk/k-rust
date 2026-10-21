// Hooked collection sorts with typed elements that programs are written in (FZ-02 review 2,
// N-a): `Stmts` holds statements and `Ints` integers, and `Pgm` reaches both. A value of such a
// sort is built from its unit, element and concatenation productions, so it holds exactly what
// its element production takes: a hole may declare only element sorts that production accepts.

module ELEMENTS-SYNTAX
  imports INT-SYNTAX

  syntax Stmt ::= "print" Int ";"  [symbol(print)]

  syntax Stmts [hook(LIST.List)]
  syntax Stmts ::= Stmts Stmts     [left, function, total, hook(LIST.concat), symbol(_Stmts_), assoc, unit(.Stmts), element(stmt)]
  syntax Stmts ::= ".Stmts"        [function, total, hook(LIST.unit), symbol(.Stmts)]
  syntax Stmts ::= stmt(Stmt)      [function, total, hook(LIST.element), symbol(stmt)]

  syntax Ints [hook(LIST.List)]
  syntax Ints ::= Ints Ints        [left, function, total, hook(LIST.concat), symbol(_Ints_), assoc, unit(.Ints), element(int)]
  syntax Ints ::= ".Ints"          [function, total, hook(LIST.unit), symbol(.Ints)]
  syntax Ints ::= int(Int)         [function, total, hook(LIST.element), symbol(int)]

  syntax Pgm ::= "run" Stmts       [symbol(run)]
               | "sum" Ints        [symbol(sum)]
endmodule

module ELEMENTS
  imports ELEMENTS-SYNTAX
  imports INT

  configuration <k> $PGM:Pgm </k>

  rule <k> run _ => .K </k>
  rule <k> sum _ => .K </k>
endmodule
