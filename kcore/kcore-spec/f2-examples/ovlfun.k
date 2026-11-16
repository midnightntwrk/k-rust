// An overload of a function by a constructor: `cap` at Gas, a constructor (kompile: `anywhere`),
// overloads `cap` at N, a function. The overload axiom `capGas(inj{N,Gas}(K)) = inj{N,Gas}(capN(K))`
// states that a constructor agrees with a function on N.
module OVLFUN-SYNTAX
  imports INT-SYNTAX
  syntax N ::= "z" [symbol(z)]
  syntax Gas ::= N
  syntax Gas ::= "inf" [symbol(inf)]
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax N ::= cap(N) [function, total, symbol(capN), overload(cap)]
  syntax Pgm ::= run(Gas) [symbol(run)]
  syntax Pgm ::= done(Gas) [symbol(done)]
endmodule

module OVLFUN
  imports OVLFUN-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule cap(z) => z
  rule <k> run(G:Gas) => done(cap(G)) </k>
endmodule
