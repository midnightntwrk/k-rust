// K claims over demos/claims/specs/strict.k: both arguments of each `+` heat first in some run,
// and every interleaving ends in the sum.
requires "strict.k"

module STRICT-SPEC
  imports STRICT

  // the whole of `<k>`: every successor list reduces
  claim [nested]: <k> (1 + 2) + (3 + 4) => 10 </k>

  // with a symbolic rest of `<k>`: the cooling rules' matchers read it, and do not reduce
  claim [nested-frame]: <k> (1 + 2) + (3 + 4) => 10 ... </k>
endmodule
