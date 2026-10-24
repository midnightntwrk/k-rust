// The cell-map lift of `k2lean gen --invariant NAME@CELL`: `<cnt>` is inside the cell map of
// `<worker>`s, so `cntOk@cnt` means "for every worker, cntOk of its <cnt>" (crates/k2lean/tests/cli.rs).
// `isCount` has an `owise` equation, which joins the invariant's unfolding set.
requires "domains.md"

module CELLMAP-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= "go"
endmodule

module CELLMAP
  imports CELLMAP-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <T>
      <k> $PGM:Pgm </k>
      <workers> <worker multiplicity="*" type="Map"> <wid> 0 </wid> <cnt> 0 </cnt> </worker> </workers>
      <next> 1 </next>
    </T>

  syntax Bool ::= cntOk(Int) [function, total]
                | isCount(KItem) [function, total]
  rule cntOk(I) => isCount(I)
  rule isCount(I:Int) => I >=Int 0
  rule isCount(_) => false [owise]

  rule <worker> <wid> _ </wid> <cnt> C => C +Int 1 </cnt> </worker> [label(tick)]
  rule <k> go => .K ... </k>
       <workers> (.Bag => <worker> <wid> N </wid> <cnt> 0 </cnt> </worker>) ... </workers>
       <next> N => N +Int 1 </next> [label(spawn)]
endmodule
