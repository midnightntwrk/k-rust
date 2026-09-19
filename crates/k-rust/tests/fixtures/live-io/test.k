module LIVE-IO-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Pgm ::= "multi"
               | "ordered"
               | "input"
               | "bytes"
               | "rollback"
               | "branch"
               | "branch-empty"
               | "left-done"
               | "right-done"
               | "stderr-only"
               | "empty-stdout"
               | "after-first"
               | "after-error"
               | got(Int)
endmodule

module LIVE-IO
  imports LIVE-IO-SYNTAX
  imports K-IO

  configuration <k> $PGM:Pgm </k>

  syntax K ::= dead(K) [function]
  rule dead(X) => X ensures false [simplification]

  rule <k> multi => #write(1, "first") ~> after-first ...</k>
  rule <k> after-first => #write(1, " second") ~> .K </k>

  rule <k> ordered => #write(1, "out-1") ~> after-error ...</k>
  rule <k> after-error => #write(2, "err-1") ~> #write(1, "out-2") ~> #putc(2, 33) ~> .K </k>

  rule <k> input => got({#getc(0)}:>Int) ...</k>
  rule <k> got(65) => #write(1, "accepted") ~> .K </k>

  rule <k> bytes => #write(1, {#read(0, 4)}:>String) ~> .K </k>

  rule <k> stderr-only => #write(2, "stderr only") ~> .K </k>
  rule <k> empty-stdout => #write(1, "") ~> #write(2, "after empty stdout") ~> .K </k>

  rule <k> rollback => dead(#write(1, "leaked")) </k>
  rule <k> rollback => #write(1, "retained") ~> .K </k>

  rule <k> branch => #write(1, "left") ~> .K </k>
  rule <k> branch => #write(1, "right") ~> .K </k>
  rule <k> branch-empty => left-done </k>
  rule <k> branch-empty => right-done </k>
endmodule
