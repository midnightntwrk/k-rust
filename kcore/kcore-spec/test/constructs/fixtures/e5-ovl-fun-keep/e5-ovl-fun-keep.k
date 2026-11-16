module E5-OVL-FUN-KEEP
  syntax N ::= "z" [symbol(z)]
  syntax Gas ::= N | "inf" [symbol(inf)]
  syntax Gas ::= cap(Gas) [symbol(capGas), overload(cap)]
  syntax Gas ::= cap(N)   [function, total, symbol(capN), overload(cap)]
  rule cap(z) => inf
endmodule
