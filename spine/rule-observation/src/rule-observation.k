module KINK-RULE-OBSERVATION-SYNTAX
  imports STRING
  imports INT
  imports BOOL

  syntax CMeta ::= cMeta ( String , String , String )
  syntax CTerms ::= "cTermNil" [symbol(cTermNil)]
                  | cTermCons ( CTerm , CTerms )
  syntax CTerm ::= cApply ( String , CTerms , CMeta )
                 | cToken ( String , String , CMeta )
                 | cVariable ( String , CMeta )
                 | cRewrite ( CTerm , CTerm , CMeta )
                 | cSequence ( CTerms , CMeta )
                 | cAs ( CTerm , CTerm , CMeta )
                 | cInjectedLabel ( String , CMeta )

  syntax ORule ::= oRule (
    String , String , String , String , String , String , String , String ,
    String , String , String , CTerm
  )
  syntax ORules ::= "oRuleNil" [symbol(oRuleNil)]
                  | oRuleCons ( ORule , ORules )
  syntax OModule ::= oModule ( String , ORules )
  syntax OModules ::= "oModuleNil" [symbol(oModuleNil)]
                    | oModuleCons ( OModule , OModules )
  syntax OGeneratedCell ::= oGeneratedCell (
    String , String , String , String , String , String , String
  )
  syntax OGeneratedCells ::= "oGeneratedCellNil" [symbol(oGeneratedCellNil)]
                           | oGeneratedCellCons ( OGeneratedCell , OGeneratedCells )
  syntax ODefinition ::= oDefinition ( String , String , OModules , OGeneratedCells )

  syntax CPathStep ::= cApplicationArgument ( Int )
  syntax CPath ::= "cPathNil" [symbol(cPathNil)]
                 | cPathCons ( CPathStep , CPath )
  syntax OOperation ::= oAppendGeneratedCellUpdate (
    CPath , String , String , String
  )
  syntax OObservationResult ::= oObservationResult (
    String , String , String , Int , String , String , String , String ,
    String , String , String , OOperation
  )
  syntax OObservationFailure ::= oObservationFailure ( String , String , Int )
  syntax OObservationOutcome ::= OObservationResult | OObservationFailure

  syntax OProgram ::= proposeRuleObservation ( String , ODefinition )
endmodule

module KINK-RULE-OBSERVATION
  imports KINK-RULE-OBSERVATION-SYNTAX

  configuration <k> $PGM:OProgram </k>

  rule <k> proposeRuleObservation(
             MODE,
             oDefinition("KRuleObservation-v1", DEFINITION, MODULES, CELLS)
           )
        => #oEmit(
             MODE,
             DEFINITION,
             #oModeCandidates(MODE, #oSelectModules(MODULES, CELLS)),
             #oConflictCountModules(MODULES, CELLS)
           )
        ... </k>

  syntax OCandidate ::= oCandidate (
    String , String , String , String , String , String , String , CPath ,
    String , String , String
  )
  syntax OCandidates ::= "oCandidateNil" [symbol(oCandidateNil)]
                       | oCandidateCons ( OCandidate , OCandidates )

  syntax OCandidates ::= #oModeCandidates ( String , OCandidates ) [function]
  rule #oModeCandidates("zero-target", _) => oCandidateNil
  rule #oModeCandidates(
         "duplicate-target",
         oCandidateCons(ITEM, oCandidateNil)
       ) => oCandidateCons(ITEM, oCandidateCons(ITEM, oCandidateNil))
  rule #oModeCandidates(MODE, ITEMS) => ITEMS
    requires MODE =/=String "zero-target"
     andBool MODE =/=String "duplicate-target"

  syntax OObservationOutcome ::= #oEmit (
    String , String , OCandidates , Int
  ) [function]
  rule #oEmit(_, _, _, CONFLICTS)
    => oObservationFailure(
         "KRuleObservation-v1",
         "conflicting-existing-state",
         CONFLICTS
       )
    requires CONFLICTS >Int 0
  rule #oEmit(
         MODE,
         DEFINITION,
         oCandidateCons(
           oCandidate(
             STATUS, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES, ATTRIBUTES,
             PARENT, NAME, BEFORE, AFTER
           ),
           oCandidateNil
         ),
         0
       )
    => #oEmitOne(
         MODE, DEFINITION, STATUS, LINEAGE, CONTENT, BODY, REQUIRES,
         ENSURES, ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
  rule #oEmit(_, _, ITEMS, 0)
    => oObservationFailure(
         "KRuleObservation-v1",
         "structural-target-cardinality",
         #oCandidateCount(ITEMS)
       ) [owise]

  syntax OObservationResult ::= #oEmitOne (
    String , String , String , String , String , String , String , String ,
    String , CPath , String , String , String
  ) [function]
  rule #oEmitOne(
         "stale-target-content", DEFINITION, STATUS, LINEAGE, _, BODY,
         REQUIRES, ENSURES, ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
    => #oResult(
         DEFINITION, STATUS, LINEAGE,
         "0000000000000000000000000000000000000000000000000000000000000000",
         BODY, REQUIRES, ENSURES, ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
  rule #oEmitOne(
         "unsupported-path", DEFINITION, STATUS, LINEAGE, CONTENT, BODY,
         REQUIRES, ENSURES, ATTRIBUTES, _, NAME, BEFORE, AFTER
       )
    => #oResult(
         DEFINITION, STATUS, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
         ATTRIBUTES, cPathCons(cApplicationArgument(99), cPathNil),
         NAME, BEFORE, AFTER
       )
  rule #oEmitOne(
         "unsupported-shape", DEFINITION, STATUS, LINEAGE, CONTENT, BODY,
         REQUIRES, ENSURES, ATTRIBUTES, _, NAME, BEFORE, AFTER
       )
    => #oResult(
         DEFINITION, STATUS, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
         ATTRIBUTES, cPathCons(cApplicationArgument(0), cPathNil),
         NAME, BEFORE, AFTER
       )
  rule #oEmitOne(
         "false-already-present", DEFINITION, _, LINEAGE, CONTENT, BODY,
         REQUIRES, ENSURES, ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
    => #oResult(
         DEFINITION, "already-present", LINEAGE, CONTENT, BODY, REQUIRES,
         ENSURES, ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
  rule #oEmitOne(
         MODE, DEFINITION, STATUS, LINEAGE, CONTENT, BODY, REQUIRES,
         ENSURES, ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
    => #oResult(
         DEFINITION, STATUS, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
         ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
    requires MODE =/=String "stale-target-content"
     andBool MODE =/=String "unsupported-path"
     andBool MODE =/=String "unsupported-shape"
     andBool MODE =/=String "false-already-present"

  syntax OObservationResult ::= #oResult (
    String , String , String , String , String , String , String , String ,
    CPath , String , String , String
  ) [function]
  rule #oResult(
         DEFINITION, STATUS, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
         ATTRIBUTES, PARENT, NAME, BEFORE, AFTER
       )
    => oObservationResult(
         "KRuleObservation-v1",
         "p3-observe-bump-state@1",
         DEFINITION,
         1,
         STATUS,
         LINEAGE,
         CONTENT,
         BODY,
         REQUIRES,
         ENSURES,
         ATTRIBUTES,
         oAppendGeneratedCellUpdate(PARENT, NAME, BEFORE, AFTER)
       )

  syntax OCandidates ::= #oSelectModules ( OModules , OGeneratedCells ) [function]
  rule #oSelectModules(oModuleNil, _) => oCandidateNil
  rule #oSelectModules(oModuleCons(oModule(_, RULES), REST), CELLS)
    => #oAppendCandidates(
         #oSelectRules(RULES, CELLS),
         #oSelectModules(REST, CELLS)
       )

  syntax OCandidates ::= #oSelectRules ( ORules , OGeneratedCells ) [function]
  rule #oSelectRules(oRuleNil, _) => oCandidateNil
  rule #oSelectRules(oRuleCons(RULE, REST), CELLS)
    => #oAppendCandidates(
         #oSelectRule(RULE, CELLS),
         #oSelectRules(REST, CELLS)
       )

  syntax OCandidates ::= #oSelectRule ( ORule , OGeneratedCells ) [function]
  rule #oSelectRule(
         oRule(
           _, _, _, _, _, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
           ATTRIBUTES,
           cApply(
             "#cells",
             cTermCons(KCELL, cTermCons(STATECELL, cTermNil)),
             _
           )
         ),
         CELLS
       )
    => oCandidateCons(
         oCandidate(
           "apply", LINEAGE, CONTENT, BODY, REQUIRES, ENSURES, ATTRIBUTES,
           cPathNil, "observation", "0", "1"
         ),
         oCandidateNil
       )
    requires #oIsTargetPair(KCELL, STATECELL)
     andBool #oObservationDescriptorCount(CELLS) ==Int 1
  rule #oSelectRule(
         oRule(
           _, _, _, _, _, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
           ATTRIBUTES,
           cSequence(
             cTermCons(KCELL, cTermCons(STATECELL, cTermNil)),
             _
           )
         ),
         CELLS
       )
    => oCandidateCons(
         oCandidate(
           "apply", LINEAGE, CONTENT, BODY, REQUIRES, ENSURES, ATTRIBUTES,
           cPathNil, "observation", "0", "1"
         ),
         oCandidateNil
       )
    requires #oIsTargetPair(KCELL, STATECELL)
     andBool #oObservationDescriptorCount(CELLS) ==Int 1
  rule #oSelectRule(
         oRule(
           _, _, _, _, _, LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
           ATTRIBUTES,
           cApply(
             "#cells",
             cTermCons(
               cApply(
                 "#cells",
                 cTermCons(KCELL, cTermCons(STATECELL, cTermNil)),
                 _
               ),
               cTermCons(OBSERVATION, cTermNil)
             ),
             _
           )
         ),
         CELLS
       )
    => oCandidateCons(
         oCandidate(
           "already-present", LINEAGE, CONTENT, BODY, REQUIRES, ENSURES,
           ATTRIBUTES, cPathNil, "observation", "0", "1"
         ),
         oCandidateNil
       )
    requires #oIsTargetPair(KCELL, STATECELL)
     andBool #oIsExactObservation(OBSERVATION)
     andBool #oObservationDescriptorCount(CELLS) ==Int 1
  rule #oSelectRule(_, _) => oCandidateNil [owise]

  syntax Bool ::= #oIsTargetPair ( CTerm , CTerm ) [function]
  rule #oIsTargetPair(
         cApply(
           "<k>",
           cTermCons(
             cApply("#noDots", cTermNil, _),
             cTermCons(
               cRewrite(
                 cApply("bump", cTermNil, _),
                 cToken("Int", "0", _),
                 _
               ),
               cTermCons(cApply("#dots", cTermNil, _), cTermNil)
             )
           ),
           _
         ),
         cApply(
           "<state>",
           cTermCons(
             cApply("#noDots", cTermNil, _),
             cTermCons(
               cRewrite(
                 cApply(
                   "#SemanticCastToInt",
                   cTermCons(cVariable(VARIABLE, _), cTermNil),
                   _
                 ),
                 cApply(
                   "_+Int_",
                   cTermCons(
                     cApply(
                       "#SemanticCastToInt",
                       cTermCons(cVariable(VARIABLE, _), cTermNil),
                       _
                     ),
                     cTermCons(cToken("Int", "1", _), cTermNil)
                   ),
                   _
                 ),
                 _
               ),
               cTermCons(cApply("#noDots", cTermNil, _), cTermNil)
             )
           ),
           _
         )
       ) => true
  rule #oIsTargetPair(_, _) => false [owise]

  syntax Bool ::= #oIsExactObservation ( CTerm ) [function]
  rule #oIsExactObservation(
         cApply(
           "<observation>",
           cTermCons(
             cApply("#noDots", cTermNil, _),
             cTermCons(
               cRewrite(
                 cToken("Int", "0", _),
                 cToken("Int", "1", _),
                 _
               ),
               cTermCons(cApply("#noDots", cTermNil, _), cTermNil)
             )
           ),
           _
         )
       ) => true
  rule #oIsExactObservation(_) => false [owise]

  syntax Bool ::= #oIsObservationCell ( CTerm ) [function]
  rule #oIsObservationCell(cApply("<observation>", _, _)) => true
  rule #oIsObservationCell(_) => false [owise]

  syntax Int ::= #oObservationDescriptorCount ( OGeneratedCells ) [function]
  rule #oObservationDescriptorCount(oGeneratedCellNil) => 0
  rule #oObservationDescriptorCount(
         oGeneratedCellCons(
           oGeneratedCell("observation", "<observation>", _, "Int", _, _, _),
           REST
         )
       ) => 1 +Int #oObservationDescriptorCount(REST)
  rule #oObservationDescriptorCount(oGeneratedCellCons(_, REST))
    => #oObservationDescriptorCount(REST) [owise]

  syntax Int ::= #oConflictCountModules ( OModules , OGeneratedCells ) [function]
  rule #oConflictCountModules(oModuleNil, _) => 0
  rule #oConflictCountModules(oModuleCons(oModule(_, RULES), REST), CELLS)
    => #oConflictCountRules(RULES, CELLS)
       +Int #oConflictCountModules(REST, CELLS)

  syntax Int ::= #oConflictCountRules ( ORules , OGeneratedCells ) [function]
  rule #oConflictCountRules(oRuleNil, _) => 0
  rule #oConflictCountRules(oRuleCons(RULE, REST), CELLS)
    => #oConflictRule(RULE, CELLS) +Int #oConflictCountRules(REST, CELLS)

  syntax Int ::= #oConflictRule ( ORule , OGeneratedCells ) [function]
  rule #oConflictRule(
         oRule(
           _, _, _, _, _, _, _, _, _, _, _,
           cApply(
             "#cells",
             cTermCons(
               cApply(
                 "#cells",
                 cTermCons(KCELL, cTermCons(STATECELL, cTermNil)),
                 _
               ),
               cTermCons(OBSERVATION, cTermNil)
             ),
             _
           )
         ),
         CELLS
       ) => 1
    requires #oIsTargetPair(KCELL, STATECELL)
     andBool #oIsObservationCell(OBSERVATION)
     andBool notBool #oIsExactObservation(OBSERVATION)
     andBool #oObservationDescriptorCount(CELLS) ==Int 1
  rule #oConflictRule(_, _) => 0 [owise]

  syntax OCandidates ::= #oAppendCandidates ( OCandidates , OCandidates ) [function]
  rule #oAppendCandidates(oCandidateNil, RIGHT) => RIGHT
  rule #oAppendCandidates(oCandidateCons(HEAD, TAIL), RIGHT)
    => oCandidateCons(HEAD, #oAppendCandidates(TAIL, RIGHT))

  syntax Int ::= #oCandidateCount ( OCandidates ) [function]
  rule #oCandidateCount(oCandidateNil) => 0
  rule #oCandidateCount(oCandidateCons(_, REST))
    => 1 +Int #oCandidateCount(REST)
endmodule
