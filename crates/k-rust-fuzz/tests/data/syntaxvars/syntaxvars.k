// Configuration variables beside the program (FZ-02 review 2, N-b and the note under S2).
// `$LIB` is read with the syntax module, as the program is (its cell's `parser` attribute), so
// `Lib` is a sort programs are written in although `Pgm` does not reach it. `$C` binds a
// `Circle` and `$SHAPE` a `Shape`, its supersort: a hole on `$C` takes circles only.

module SYNTAXVARS-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "go" Int          [symbol(go)]
  syntax Lib ::= "lib" Int         [symbol(lib)]
endmodule

module SYNTAXVARS
  imports SYNTAXVARS-SYNTAX
  imports INT

  syntax Shape  ::= Circle | Square
  syntax Circle ::= circle(Int)    [symbol(circle)]
  syntax Square ::= square(Int)    [symbol(square)]

  configuration <k> $PGM:Pgm </k>
                <lib parser="LIB, SYNTAXVARS-SYNTAX"> $LIB:Lib </lib>
                <c> $C:Circle </c>
                <shape> $SHAPE:Shape </shape>

  rule <k> go _ => .K </k>
endmodule
