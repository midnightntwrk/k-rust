requires "void.k"
module VOID-SPEC
  imports VOID
  claim [vacuous]: <k> hold(_V:Void) => done </k>
  claim [control]: <k> stay(_X:Int) => done </k>
endmodule
