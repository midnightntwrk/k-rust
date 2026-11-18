// Equations of the text's own for two symbols of the INT module, one of them a simplification.
module T237-HOOK-EQ-OWED
  imports INT
  imports BOOL
  rule X +Int 0 => X
  rule X *Int 1 => X [simplification]
endmodule
