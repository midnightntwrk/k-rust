// Configuration variables beside the program (FZ-02 review 2, N-b and the note under S2; HARD-A
// review S2). Which module parses a binding, and where its sort's grammar lives, decide whether
// its values are program syntax:
// - `$LIB` is read with the syntax module (its cell's `parser` attribute);
// - `$LIB2` has no attribute, so the main module reads it, but `Lib2` and `Body` are declared in
//   the syntax module, the grammar programs are written in;
// - `$EXT` is read with a second grammar module, `SYNTAXVARS-EXT`, that its cell names.
// None of `Lib`, `Lib2`, `Body`, `Ext` and `Arg` is reached from `Pgm`. `$C` binds a `Circle`
// and `$SHAPE` a `Shape`, its supersort, both declared in the main module: a hole on `$C` takes
// circles only.

module SYNTAXVARS-SYNTAX
  imports INT-SYNTAX

  syntax Pgm  ::= "go" Int         [symbol(go)]
  syntax Lib  ::= "lib" Int        [symbol(lib)]
  syntax Lib2 ::= "lib2" Body      [symbol(lib2)]
  syntax Body ::= "ret" Int        [symbol(ret)]
                | "loop" Body      [symbol(loop)]
endmodule

module SYNTAXVARS-EXT
  imports INT-SYNTAX

  syntax Ext ::= "ext" Arg         [symbol(ext)]
  syntax Arg ::= "arg" Int         [symbol(arg)]
endmodule

module SYNTAXVARS
  imports SYNTAXVARS-SYNTAX
  imports SYNTAXVARS-EXT
  imports INT

  syntax Shape  ::= Circle | Square
  syntax Circle ::= circle(Int)    [symbol(circle)]
  syntax Square ::= square(Int)    [symbol(square)]

  configuration <k> $PGM:Pgm </k>
                <lib parser="LIB, SYNTAXVARS-SYNTAX"> $LIB:Lib </lib>
                <lib2> $LIB2:Lib2 </lib2>
                <ext parser="EXT, SYNTAXVARS-EXT"> $EXT:Ext </ext>
                <c> $C:Circle </c>
                <shape> $SHAPE:Shape </shape>

  rule <k> go _ => .K </k>
endmodule
