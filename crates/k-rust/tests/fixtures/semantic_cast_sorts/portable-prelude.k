module SORT-BOOL
  syntax Bool [hook(BOOL.Bool)]
  syntax Bool ::= "true" [token] | "false" [token]
endmodule

module INT-SYNTAX
  syntax Int [hook(INT.Int)]
  syntax Int ::= r"[\\+\\-]?[0-9]+" [prefer, token, prec(2)]
endmodule

module STRING-SYNTAX
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [token]
endmodule
