module E5-OVL-FUN-LHS-SYNTAX
  imports INT-SYNTAX
  syntax N ::= "z" [symbol(z)]
  syntax Gas ::= N
  syntax Gas ::= "inf" [symbol(inf)]
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax N ::= cap(N) [function, total, symbol(capN), overload(cap)]
  syntax Pgm ::= run(Gas) [symbol(run)]
  syntax Pgm ::= done(Gas) [symbol(done)]
endmodule

module E5-OVL-FUN-LHS
  imports E5-OVL-FUN-LHS-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule cap(z) => z
  rule <k> run(cap(G:Gas)) => done(G) </k>
endmodule
