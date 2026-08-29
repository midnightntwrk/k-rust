requires "mini-proof.k"

module MINI-SPEC
  imports MINI-PROOF

  claim <k> start => done </k> [label(claim-proven)]
  claim <k> start => stuck </k> [label(claim-refuted)]
endmodule
