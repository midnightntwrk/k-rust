// A definition that declares the stream variables `$STDIN` and `$IO` beside `$PGM` and one
// other configuration variable, `$LIMIT`. A campaign case binds the streams as
// `krun --io off < /dev/null` does (`$STDIN` is one newline, `$IO` is `off`); FZ-02's assembly
// test compares its configuration with the one that krun builds for `go.pgm` with
// `-cLIMIT=3`.

module STREAMS-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= "go" Int  [symbol(go)]
endmodule

module STREAMS
  imports STREAMS-SYNTAX
  imports INT
  imports STRING

  configuration <k> $PGM:Pgm </k>
                <limit> $LIMIT:Int </limit>
                <in> $STDIN:String </in>
                <io> $IO:String </io>

  rule [go]: <k> go _:Int => .K ... </k>
endmodule
