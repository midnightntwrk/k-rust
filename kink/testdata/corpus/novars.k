// A definition that declares no configuration variable: its case binds nothing.
module NOVARS
  imports BOOL
  configuration <k> true </k>
  rule true => false
endmodule
