module P3-PROBE-SYNTAX
  imports STRING

  syntax PCells ::= "pCellNil" [symbol(pCellNil)]
                  | pCellCons ( String , PCells )
  syntax PCellEdge ::= pCellEdge ( String , String )
  syntax PCellEdges ::= "pCellEdgeNil" [symbol(pCellEdgeNil)]
                      | pCellEdgeCons ( PCellEdge , PCellEdges )

  syntax PContextDecl ::= pSeqstrict2 ( String )
                        | pExplicitContext ( String )
  syntax PContextDecls ::= "pContextNil" [symbol(pContextNil)]
                         | pContextCons ( PContextDecl , PContextDecls )

  syntax PRuleDecl ::= pRuleDecl ( String , String , PCells , String , String )
                     | pConfigCall ( String , String )
  syntax PRuleDecls ::= "pRuleDeclNil" [symbol(pRuleDeclNil)]
                      | pRuleDeclCons ( PRuleDecl , PRuleDecls )

  syntax P3Input ::= p3Definition ( PCellEdges , PContextDecls , PRuleDecls )

  syntax PFact ::= pContextRule ( String , String , PCells )
                 | pConcretizedRule ( String , String , PCells , String , String )
                 | pFunctionInjection ( String , String )
  syntax PFacts ::= "pFactNil" [symbol(pFactNil)]
                  | pFactCons ( PFact , PFacts )
  syntax P3Projection ::= p3Projection ( PCellEdges , PFacts )
  syntax P3Program ::= P3Input | P3Projection
endmodule

module P3-PROBE
  imports P3-PROBE-SYNTAX
  imports STRING
  imports BOOL

  syntax P3Phase ::= "p3Idle" [symbol(p3Idle)]
                   | "p3Contexts" [symbol(p3Contexts)]
                   | "p3Rules" [symbol(p3Rules)]
                   | "p3Build" [symbol(p3Build)]
                   | "p3Halted" [symbol(p3Halted)]

  configuration
    <p3>
      <k> $PGM:P3Program </k>
      <p3Phase> p3Idle </p3Phase>
      <cellEdges> pCellEdgeNil </cellEdges>
      <pendingContexts> pContextNil </pendingContexts>
      <pendingRuleDecls> pRuleDeclNil </pendingRuleDecls>
      <facts> pFactNil </facts>
      <p3Result> .K </p3Result>
    </p3>

  rule <k> p3Definition(EDGES, CONTEXTS, RULES) => .K ... </k>
       <p3Phase> p3Idle => p3Contexts </p3Phase>
       <cellEdges> _ => EDGES </cellEdges>
       <pendingContexts> _ => CONTEXTS </pendingContexts>
       <pendingRuleDecls> _ => RULES </pendingRuleDecls>

  rule <k> RESULT:P3Projection => .K ... </k>
       <p3Phase> p3Idle => p3Halted </p3Phase>
       <p3Result> .K => RESULT </p3Result>

  rule <p3Phase> p3Contexts </p3Phase>
       <pendingContexts> pContextCons(pSeqstrict2(BASE), REST) => REST </pendingContexts>
       <cellEdges> EDGES </cellEdges>
       <facts> FACTS => #seqstrictFacts(BASE, #complete(pCellCons("k", pCellNil), EDGES), FACTS) </facts>

  rule <p3Phase> p3Contexts </p3Phase>
       <pendingContexts> pContextCons(pExplicitContext(BASE), REST) => REST </pendingContexts>
       <cellEdges> EDGES </cellEdges>
       <facts> FACTS => #explicitFacts(BASE, #complete(pCellCons("k", pCellNil), EDGES), FACTS) </facts>

  rule <p3Phase> p3Contexts => p3Rules </p3Phase>
       <pendingContexts> pContextNil </pendingContexts>

  rule <p3Phase> p3Rules </p3Phase>
       <pendingRuleDecls>
         pRuleDeclCons(pRuleDecl(LABEL, MODE, CELLS, REQUIRES, ENSURES), REST) => REST
       </pendingRuleDecls>
       <cellEdges> EDGES </cellEdges>
       <facts> FACTS => pFactCons(
         pConcretizedRule(LABEL, MODE, #complete(CELLS, EDGES), REQUIRES, ENSURES), FACTS
       ) </facts>

  rule <p3Phase> p3Rules </p3Phase>
       <pendingRuleDecls>
         pRuleDeclCons(pConfigCall(LABEL, FUNCTION), REST) => REST
       </pendingRuleDecls>
       <facts> FACTS => pFactCons(pFunctionInjection(LABEL, FUNCTION), FACTS) </facts>

  rule <p3Phase> p3Rules => p3Build </p3Phase>
       <pendingRuleDecls> pRuleDeclNil </pendingRuleDecls>

  rule <p3Phase> p3Build => p3Halted </p3Phase>
       <cellEdges> EDGES </cellEdges>
       <facts> FACTS </facts>
       <p3Result> .K => p3Projection(EDGES, FACTS) </p3Result>

  syntax PCells ::= #appendUnique ( PCells , PCells ) [function]
  rule #appendUnique(pCellNil, RIGHT) => RIGHT
  rule #appendUnique(pCellCons(CELL, REST), RIGHT)
    => #appendUnique(REST, RIGHT)
    requires #contains(CELL, RIGHT)
  rule #appendUnique(pCellCons(CELL, REST), RIGHT)
    => pCellCons(CELL, #appendUnique(REST, RIGHT))
    requires notBool(#contains(CELL, RIGHT))

  syntax Bool ::= #contains ( String , PCells ) [function]
  rule #contains(_, pCellNil) => false
  rule #contains(CELL, pCellCons(CELL, _)) => true
  rule #contains(CELL, pCellCons(OTHER, REST)) => #contains(CELL, REST)
    requires CELL =/=String OTHER

  syntax PCells ::= #parents ( String , PCellEdges ) [function]
  rule #parents(_, pCellEdgeNil) => pCellNil
  rule #parents(CELL, pCellEdgeCons(pCellEdge(CELL, PARENT), REST))
    => pCellCons(PARENT, #parents(PARENT, REST))
  rule #parents(CELL, pCellEdgeCons(pCellEdge(OTHER, _), REST)) => #parents(CELL, REST)
    requires CELL =/=String OTHER

  syntax PCells ::= #complete ( PCells , PCellEdges ) [function]
  rule #complete(pCellNil, _) => pCellNil
  rule #complete(pCellCons(CELL, REST), EDGES)
    => #appendUnique(pCellCons(CELL, #parents(CELL, EDGES)), #complete(REST, EDGES))

  syntax PFacts ::= #seqstrictFacts ( String , PCells , PFacts ) [function]
  rule #seqstrictFacts(BASE, CELLS, FACTS)
    => pFactCons(pContextRule((BASE +String "1-heat"), "heat", CELLS),
       pFactCons(pContextRule((BASE +String "1-cool"), "cool", CELLS),
       pFactCons(pContextRule((BASE +String "2-heat"), "heat", CELLS),
       pFactCons(pContextRule((BASE +String "2-cool"), "cool", CELLS), FACTS))))

  syntax PFacts ::= #explicitFacts ( String , PCells , PFacts ) [function]
  rule #explicitFacts(BASE, CELLS, FACTS)
    => pFactCons(pContextRule((BASE +String "-heat"), "heat", CELLS),
       pFactCons(pContextRule((BASE +String "-cool"), "cool", CELLS), FACTS))
endmodule
