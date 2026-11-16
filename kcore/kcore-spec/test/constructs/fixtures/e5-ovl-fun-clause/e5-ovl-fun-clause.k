module E5-OVL-FUN-CLAUSE-SYNTAX
  syntax N ::= "z" [symbol(z)]
  syntax Gas ::= N
  syntax Gas ::= "inf" [symbol(inf)]
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax N ::= cap(N) [function, total, symbol(capN), overload(cap)]
  syntax Gas ::= uncap(Gas) [function, symbol(uncap)]
endmodule
module E5-OVL-FUN-CLAUSE
  imports E5-OVL-FUN-CLAUSE-SYNTAX
  rule cap(z) => z
  rule uncap(cap(G:Gas)) => G
endmodule
