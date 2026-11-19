// The parametric premise's check (kink-patch tests/premise.rs, PJ-34 U34f): a definition that
// imports the prelude modules whose equations an inserted constructor would otherwise leave
// unsupported (K-EQUAL's `=/=K` and `#if`, LIST's `pushList`, SET's `|Set`, STRING's `findChar`),
// with one user sort for the test to insert a fresh constructor at.
module PREMISE
  imports BASIC-K
  imports INT
  imports BOOL
  imports STRING
  imports LIST
  imports SET
  imports K-EQUAL
  syntax Val ::= "z" [symbol(z)]
  configuration <k> .K </k>
endmodule
