requires "split.k"
module SPLIT-LEMMAS
  imports SPLIT
  claim [pass]: <k> a => c </k>
  claim [fail1]: <k> c => d </k>
  claim [fail2]: <k> good => d </k>
endmodule
module IMPORTED-SPEC
  imports SPLIT-LEMMAS
endmodule
