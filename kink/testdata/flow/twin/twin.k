// Flow fixture (F-14): two identical rules in one module. They share a sentence
// fingerprint, so a mutation's position-free identity must tell them apart by
// their occurrence among equal fingerprints (flow README 7.5.4).
module TWIN-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "inc" "(" Exp ")" [strict, symbol(inc)]
endmodule

module TWIN
  imports TWIN-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  rule inc(I:Int) => I +Int 1
  rule inc(I:Int) => I +Int 1
endmodule
