requires "split.k"
module TRIVIAL-SPEC
  imports SPLIT
  claim [ct1]: <k> t1 => t3 </k> [one-path]
  claim [ct2]: <k> t1 => t3 </k>
endmodule
