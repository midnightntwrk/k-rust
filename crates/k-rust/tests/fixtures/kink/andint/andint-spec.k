requires "andint.k"
module ANDINT-SPEC
  imports ANDINT
  claim [vacuous]: <k> stay(X:Int) => done </k> requires X &Int 1 ==Int 2
  claim [control]: <k> stay(X:Int) => done </k> requires X +Int 1 ==Int 2
  claim [empty]: <k> stay(X:Int) => done </k> requires X +Int 1 ==Int 2 andBool X ==Int 5
endmodule
