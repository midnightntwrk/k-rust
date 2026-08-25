module KINK-TRACE-CONFIGURATION-AUGMENTATION-SYNTAX
  imports STRING
  imports INT
  imports BOOL

  syntax CMeta ::= cMeta ( String , String , String )
  syntax CTerms ::= "cTermNil" [symbol(cTermNil)] | cTermCons ( CTerm , CTerms )
  syntax CTerm ::= cApply ( String , CTerms , CMeta )
                 | cToken ( String , String , CMeta )
                 | cVariable ( String , CMeta )
                 | cRewrite ( CTerm , CTerm , CMeta )
                 | cSequence ( CTerms , CMeta )
                 | cAs ( CTerm , CTerm , CMeta )
                 | cInjectedLabel ( String , CMeta )
  syntax CConfiguration ::= cConfiguration (
    String , String , String , String , String , String , String , String , String , CTerm
  )
  syntax CConfigurations ::= "cConfigurationNil" [symbol(cConfigurationNil)]
                           | cConfigurationCons ( CConfiguration , CConfigurations )
  syntax CModule ::= cModule ( String , CConfigurations )
  syntax CModules ::= "cModuleNil" [symbol(cModuleNil)] | cModuleCons ( CModule , CModules )

  syntax CSort ::= cSort ( String , String )
  syntax CSorts ::= "cSortNil" [symbol(cSortNil)] | cSortCons ( CSort , CSorts )
  syntax CProduction ::= cProduction (
    String , String , CSort , CSorts , String , String , String
  )
  syntax CProductions ::= "cProductionNil" [symbol(cProductionNil)]
                        | cProductionCons ( CProduction , CProductions )
  syntax CDefinition ::= cDefinition ( String , String , CModules , CProductions , CSorts )

  syntax CPathStep ::= cApplicationArgument ( Int )
  syntax CPath ::= "cPathNil" [symbol(cPathNil)] | cPathCons ( CPathStep , CPath )
  syntax TTerms ::= "tTermNil" [symbol(tTermNil)] | tTermCons ( TTerm , TTerms )
  syntax TTerm ::= tApply ( CProduction , TTerms )
                 | tToken ( CSort , String , String )
                 | tVariable ( String , CSort )
  syntax COperation ::= cloneLeafCellWithTypedContentFromInput ( CPath , CPath , String , TTerm )
  syntax CTraceAugmentationResult ::= cTraceAugmentationResult (
    String , String , String , Int , String , String , String , String ,
    String , String , String , String , COperation
  )
  syntax CTraceAugmentationFailure ::= cTraceAugmentationFailure ( String , String , Int )
  syntax CTraceAugmentationOutcome ::= CTraceAugmentationResult | CTraceAugmentationFailure
  syntax CProgram ::= proposeTraceConfigurationAugmentation ( String , CDefinition )
endmodule

module KINK-TRACE-CONFIGURATION-AUGMENTATION
  imports KINK-TRACE-CONFIGURATION-AUGMENTATION-SYNTAX

  configuration <k> $PGM:CProgram </k>

  rule <k> proposeTraceConfigurationAugmentation(
             MODE,
             cDefinition("KTraceConfigurationAugmentation-v1", DEFINITION, MODULES, PRODUCTIONS, _)
           )
        => #withInitializers(MODE, DEFINITION, MODULES, #selectInitializers(PRODUCTIONS)) ... </k>

  syntax CCandidate ::= cCandidate (
    String , String , String , String , String , String , String , String , CPath , CPath
  )
  syntax CCandidates ::= "cCandidateNil" [symbol(cCandidateNil)]
                       | cCandidateCons ( CCandidate , CCandidates )
  syntax CCandidates ::= #modeCandidates ( String , CModules , CProduction ) [function]
  rule #modeCandidates("false-already-shape", M, I) => #selectNamedModules(M, I)
  rule #modeCandidates(MODE, M, I) => #adjustCandidateCount(MODE, #selectModules(M, I))
    requires MODE =/=String "false-already-shape"
  syntax CCandidates ::= #adjustCandidateCount ( String , CCandidates ) [function]
  rule #adjustCandidateCount("zero-target", _) => cCandidateNil
  rule #adjustCandidateCount("duplicate-target", cCandidateCons(I, cCandidateNil))
    => cCandidateCons(I, cCandidateCons(I, cCandidateNil))
  rule #adjustCandidateCount(M, I) => I
    requires M =/=String "zero-target" andBool M =/=String "duplicate-target"

  syntax CProductions ::= #selectInitializers ( CProductions ) [function]
  rule #selectInitializers(cProductionNil) => cProductionNil
  rule #selectInitializers(cProductionCons(P, R))
    => #appendProductions(#selectInitializer(P), #selectInitializers(R))
  syntax CProductions ::= #selectInitializer ( CProduction ) [function]
  rule #selectInitializer(cProduction(M, ".List", cSort("List", SF), cSortNil, PF, LF, MF))
    => cProductionCons(
         cProduction(M, ".List", cSort("List", SF), cSortNil, PF, LF, MF),
         cProductionNil)
  rule #selectInitializer(_) => cProductionNil [owise]
  syntax CProductions ::= #appendProductions ( CProductions , CProductions ) [function]
  rule #appendProductions(cProductionNil, R) => R
  rule #appendProductions(cProductionCons(I, L), R)
    => cProductionCons(I, #appendProductions(L, R))

  syntax CTraceAugmentationOutcome ::= #withInitializers (
    String , String , CModules , CProductions
  ) [function]
  rule #withInitializers(_, _, _, INITIALIZERS)
    => cTraceAugmentationFailure("KTraceConfigurationAugmentation-v1", "initializer-descriptor-cardinality", #productionCount(INITIALIZERS))
    requires #productionCount(INITIALIZERS) =/=Int 1
  rule #withInitializers(MODE, DEFINITION, MODULES,
         cProductionCons(INITIALIZER, cProductionNil))
    => #emit(MODE, DEFINITION, #modeCandidates(MODE, MODULES, INITIALIZER),
         #modeConflictCount(MODE, MODULES, INITIALIZER), INITIALIZER)

  syntax Int ::= #modeConflictCount ( String , CModules , CProduction ) [function]
  rule #modeConflictCount("false-already-shape", _, _) => 0
  rule #modeConflictCount(MODE, MODULES, INITIALIZER)
    => #conflictCountModules(MODULES, INITIALIZER)
    requires MODE =/=String "false-already-shape"

  syntax CTraceAugmentationOutcome ::= #emit (
    String , String , CCandidates , Int , CProduction
  ) [function]
  rule #emit("failure-wrong-schema", _, _, _, _)
    => cTraceAugmentationFailure("KTraceConfigurationAugmentation-v0", "structural-target-cardinality", 0)
  rule #emit("failure-unknown-reason", _, _, _, _)
    => cTraceAugmentationFailure("KTraceConfigurationAugmentation-v1", "unknown-reason", 0)
  rule #emit("failure-invalid-count", _, _, _, _)
    => cTraceAugmentationFailure("KTraceConfigurationAugmentation-v1", "structural-target-cardinality", -1)
  rule #emit(MODE, _, _, CONFLICTS, _)
    => cTraceAugmentationFailure("KTraceConfigurationAugmentation-v1", "conflicting-existing-state", CONFLICTS)
    requires CONFLICTS >Int 0
     andBool MODE =/=String "failure-wrong-schema"
     andBool MODE =/=String "failure-unknown-reason"
     andBool MODE =/=String "failure-invalid-count"
  rule #emit(MODE, DEFINITION,
         cCandidateCons(cCandidate(STATUS, LINEAGE, SOURCE, LOCATION, CONTENT, BODY,
           ENSURES, ATTRIBUTES, PARENT, TEMPLATE), cCandidateNil), 0, INITIALIZER)
    => #emitOne(MODE, DEFINITION, STATUS, LINEAGE, SOURCE, LOCATION, CONTENT, BODY,
         ENSURES, ATTRIBUTES, PARENT, TEMPLATE, INITIALIZER)
    requires MODE =/=String "failure-wrong-schema"
     andBool MODE =/=String "failure-unknown-reason"
     andBool MODE =/=String "failure-invalid-count"
  rule #emit(_, _, ITEMS, 0, _)
    => cTraceAugmentationFailure("KTraceConfigurationAugmentation-v1", "structural-target-cardinality", #candidateCount(ITEMS)) [owise]

  syntax CTraceAugmentationResult ::= #emitOne (
    String , String , String , String , String , String , String , String ,
    String , String , CPath , CPath , CProduction
  ) [function]
  rule #emitOne("stale-definition", _, S, L, SRC, LOC, C, B, E, A, P, T, I)
    => #result("0000000000000000000000000000000000000000000000000000000000000000", S, L, SRC, LOC, C, B, E, A, P, T, "trace", tApply(I, tTermNil))
  rule #emitOne("stale-target-content", D, S, L, SRC, LOC, _, B, E, A, P, T, I)
    => #result(D, S, L, SRC, LOC, "0000000000000000000000000000000000000000000000000000000000000000", B, E, A, P, T, "trace", tApply(I, tTermNil))
  rule #emitOne("stale-target-provenance", D, S, L, SRC, _, C, B, E, A, P, T, I)
    => #result(D, S, L, SRC, "Location(0,0,0,0)", C, B, E, A, P, T, "trace", tApply(I, tTermNil))
  rule #emitOne("unsupported-parent-path", D, S, L, SRC, LOC, C, B, E, A, _, T, I)
    => #result(D, S, L, SRC, LOC, C, B, E, A, cPathNil, T, "trace", tApply(I, tTermNil))
  rule #emitOne("out-of-bounds-template-path", D, S, L, SRC, LOC, C, B, E, A, P, _, I)
    => #result(D, S, L, SRC, LOC, C, B, E, A, P,
         cPathCons(cApplicationArgument(99), cPathNil), "trace", tApply(I, tTermNil))
  rule #emitOne("malformed-template", D, S, L, SRC, LOC, C, B, E, A, P, _, I)
    => #result(D, S, L, SRC, LOC, C, B, E, A, P, P, "trace", tApply(I, tTermNil))
  rule #emitOne("non-leaf-template", D, S, L, SRC, LOC, C, B, E, A, P, _, I)
    => #result(D, S, L, SRC, LOC, C, B, E, A, P, cPathNil, "trace", tApply(I, tTermNil))
  rule #emitOne("false-already-present", D, _, L, SRC, LOC, C, B, E, A, P, T, I)
    => #result(D, "already-present", L, SRC, LOC, C, B, E, A, P, T, "trace", tApply(I, tTermNil))
  rule #emitOne("unknown-constructor", D, S, L, SRC, LOC, C, B, E, A, P, T,
         cProduction(M, _, RS, AS, PF, LF, MF))
    => #result(D, S, L, SRC, LOC, C, B, E, A, P, T, "trace",
         tApply(cProduction(M, "unknownInitializer", RS, AS, PF, LF, MF), tTermNil))
  rule #emitOne("non-nullary-initializer", D, S, L, SRC, LOC, C, B, E, A, P, T, I)
    => #result(D, S, L, SRC, LOC, C, B, E, A, P, T, "trace",
         tApply(I, tTermCons(tApply(I, tTermNil), tTermNil)))
  rule #emitOne("variable-initializer", D, S, L, SRC, LOC, C, B, E, A, P, T,
         cProduction(_, _, RS, _, _, _, _))
    => #result(D, S, L, SRC, LOC, C, B, E, A, P, T, "trace", tVariable("CONFIGURATION_INITIALIZER", RS))
  rule #emitOne("sort-invalid-initializer", D, S, L, SRC, LOC, C, B, E, A, P, T,
         cProduction(M, LABEL, _, AS, PF, LF, MF))
    => #result(D, S, L, SRC, LOC, C, B, E, A, P, T, "trace",
         tApply(cProduction(M, LABEL, cSort("InvalidInitializerSort", "invalid"), AS, PF, LF, MF), tTermNil))
  rule #emitOne(MODE, D, S, L, SRC, LOC, C, B, E, A, P, T, I)
    => #result(D, S, L, SRC, LOC, C, B, E, A, P, T, "trace", tApply(I, tTermNil))
    requires MODE =/=String "stale-definition"
     andBool MODE =/=String "stale-target-content"
     andBool MODE =/=String "stale-target-provenance"
     andBool MODE =/=String "unsupported-parent-path"
     andBool MODE =/=String "out-of-bounds-template-path"
     andBool MODE =/=String "malformed-template"
     andBool MODE =/=String "non-leaf-template"
     andBool MODE =/=String "false-already-present"
     andBool MODE =/=String "unknown-constructor"
     andBool MODE =/=String "non-nullary-initializer"
     andBool MODE =/=String "variable-initializer"
     andBool MODE =/=String "sort-invalid-initializer"
     andBool MODE =/=String "failure-wrong-schema"
     andBool MODE =/=String "failure-unknown-reason"
     andBool MODE =/=String "failure-invalid-count"

  syntax CTraceAugmentationResult ::= #result (
    String , String , String , String , String , String , String , String ,
    String , CPath , CPath , String , TTerm
  ) [function]
  rule #result(D, S, L, SRC, LOC, C, B, E, A, P, T, N, I)
    => cTraceAugmentationResult(
         "KTraceConfigurationAugmentation-v1", "p3-add-empty-trace-cell@1",
         D, 1, S, L, SRC, LOC, C, B, E, A,
         cloneLeafCellWithTypedContentFromInput(P, T, N, I))

  syntax CCandidates ::= #selectModules ( CModules , CProduction ) [function]
  rule #selectModules(cModuleNil, _) => cCandidateNil
  rule #selectModules(cModuleCons(cModule(_, C), R), I)
    => #appendCandidates(#selectConfigurations(C, I), #selectModules(R, I))
  syntax CCandidates ::= #selectConfigurations ( CConfigurations , CProduction ) [function]
  rule #selectConfigurations(cConfigurationNil, _) => cCandidateNil
  rule #selectConfigurations(cConfigurationCons(C, R), I)
    => #appendCandidates(#selectConfiguration(C, I), #selectConfigurations(R, I))

  syntax CCandidates ::= #selectConfiguration ( CConfiguration , CProduction ) [function]
  rule #selectConfiguration(cConfiguration(_, _, SRC, LOC, L, C, B, E, A,
         cApply("#configCell", cTermCons(cToken("#CellName", "T", _),
           cTermCons(_, cTermCons(
             cApply("#cells", cTermCons(KCELL, cTermCons(STATECELL, cTermNil)), _),
             cTermCons(cToken("#CellName", "T", _), cTermNil)))), _)), _)
    => cCandidateCons(cCandidate("apply", L, SRC, LOC, C, B, E, A,
         cPathCons(cApplicationArgument(2), cPathNil),
         cPathCons(cApplicationArgument(2),
           cPathCons(cApplicationArgument(1), cPathNil))), cCandidateNil)
    requires #isKCell(KCELL) andBool #isStateCell(STATECELL)
  rule #selectConfiguration(cConfiguration(_, _, SRC, LOC, L, C, B, E, A,
         cApply("#configCell", cTermCons(cToken("#CellName", "T", _),
           cTermCons(_, cTermCons(
             cApply("#cells", cTermCons(
                cApply("#cells", cTermCons(KCELL, cTermCons(STATECELL, cTermNil)), _),
                cTermCons(TRACECELL, cTermNil)), _),
             cTermCons(cToken("#CellName", "T", _), cTermNil)))), _)), I)
    => cCandidateCons(cCandidate("already-present", L, SRC, LOC, C, B, E, A,
         cPathCons(cApplicationArgument(2), cPathNil),
         cPathCons(cApplicationArgument(2), cPathCons(cApplicationArgument(0),
           cPathCons(cApplicationArgument(1), cPathNil)))), cCandidateNil)
    requires #isKCell(KCELL) andBool #isStateCell(STATECELL)
     andBool #isExpectedClone(TRACECELL, STATECELL, "trace", I)
  rule #selectConfiguration(_, _) => cCandidateNil [owise]

  syntax CCandidates ::= #selectNamedModules ( CModules , CProduction ) [function]
  rule #selectNamedModules(cModuleNil, _) => cCandidateNil
  rule #selectNamedModules(cModuleCons(cModule(_, C), R), I)
    => #appendCandidates(#selectNamedConfigurations(C, I), #selectNamedModules(R, I))
  syntax CCandidates ::= #selectNamedConfigurations ( CConfigurations , CProduction ) [function]
  rule #selectNamedConfigurations(cConfigurationNil, _) => cCandidateNil
  rule #selectNamedConfigurations(cConfigurationCons(C, R), I)
    => #appendCandidates(#selectNamedConfiguration(C, I), #selectNamedConfigurations(R, I))
  syntax CCandidates ::= #selectNamedConfiguration ( CConfiguration , CProduction ) [function]
  rule #selectNamedConfiguration(cConfiguration(_, _, SRC, LOC, L, C, B, E, A,
         cApply("#configCell", cTermCons(cToken("#CellName", "T", _),
           cTermCons(_, cTermCons(
             cApply("#cells", cTermCons(
               cApply("#cells", cTermCons(KCELL, cTermCons(STATECELL, cTermNil)), _),
               cTermCons(cApply("#configCell", cTermCons(cToken(_, "trace", _), _), _),
                 cTermNil)), _),
             cTermCons(cToken("#CellName", "T", _), cTermNil)))), _)), _)
    => cCandidateCons(cCandidate("already-present", L, SRC, LOC, C, B, E, A,
         cPathCons(cApplicationArgument(2), cPathNil),
         cPathCons(cApplicationArgument(2), cPathCons(cApplicationArgument(0),
           cPathCons(cApplicationArgument(1), cPathNil)))), cCandidateNil)
    requires #isKCell(KCELL) andBool #isStateCell(STATECELL)
  rule #selectNamedConfiguration(_, _) => cCandidateNil [owise]

  syntax Bool ::= #isKCell ( CTerm ) [function]
  rule #isKCell(cApply("#configCell", cTermCons(cToken("#CellName", "k", _),
         cTermCons(_, cTermCons(_,
           cTermCons(cToken("#CellName", "k", _), cTermNil)))), _)) => true
  rule #isKCell(_) => false [owise]
  syntax Bool ::= #isStateCell ( CTerm ) [function]
  rule #isStateCell(cApply("#configCell", cTermCons(cToken("#CellName", "state", _),
         cTermCons(_, cTermCons(cToken("Int", "1", _),
           cTermCons(cToken("#CellName", "state", _), cTermNil)))), _)) => true
  rule #isStateCell(_) => false [owise]
  syntax CTerm ::= #expectedClone ( CTerm , String , CProduction ) [function]
  rule #expectedClone(
         cApply("#configCell", cTermCons(cToken(STARTSORT, _, STARTMETA),
           cTermCons(PROPERTIES, cTermCons(_,
             cTermCons(cToken(ENDSORT, _, ENDMETA), cTermNil)))), APPLICATIONMETA),
         NAME,
         cProduction(_, LABEL, cSort(RESULTSORT, _), cSortNil, _, NODEPRODUCTION, NODEMETA))
    => cApply("#configCell", cTermCons(cToken(STARTSORT, NAME, STARTMETA),
         cTermCons(PROPERTIES,
           cTermCons(cApply(LABEL, cTermNil,
             cMeta(RESULTSORT, NODEPRODUCTION, NODEMETA)),
             cTermCons(cToken(ENDSORT, NAME, ENDMETA), cTermNil)))), APPLICATIONMETA)

  syntax Bool ::= #isExpectedClone ( CTerm , CTerm , String , CProduction ) [function]
  rule #isExpectedClone(ACTUAL, TEMPLATE, NAME, INITIALIZER)
    => #sameTerm(ACTUAL, #expectedClone(TEMPLATE, NAME, INITIALIZER))
  syntax Bool ::= #sameTerm ( CTerm , CTerm ) [function]
  rule #sameTerm(TERM, TERM) => true
  rule #sameTerm(_, _) => false [owise]

  syntax Int ::= #conflictCountModules ( CModules , CProduction ) [function]
  rule #conflictCountModules(cModuleNil, _) => 0
  rule #conflictCountModules(cModuleCons(cModule(_, C), R), I)
    => #conflictCountConfigurations(C, I) +Int #conflictCountModules(R, I)
  syntax Int ::= #conflictCountConfigurations ( CConfigurations , CProduction ) [function]
  rule #conflictCountConfigurations(cConfigurationNil, _) => 0
  rule #conflictCountConfigurations(cConfigurationCons(C, R), I)
    => #isConflict(C, I) +Int #conflictCountConfigurations(R, I)
  syntax Int ::= #isConflict ( CConfiguration , CProduction ) [function]
  rule #isConflict(cConfiguration(_, _, _, _, _, _, _, _, _,
         cApply("#configCell", cTermCons(cToken("#CellName", "T", _),
           cTermCons(_, cTermCons(cApply("#cells", cTermCons(
             cApply("#cells", cTermCons(KCELL, cTermCons(STATECELL, cTermNil)), _),
             cTermCons(TRACECELL,
               cTermNil)), _),
             cTermCons(cToken("#CellName", "T", _), cTermNil)))), _)), I) => 1
    requires #isKCell(KCELL) andBool #isStateCell(STATECELL)
     andBool #hasName(TRACECELL, "trace")
     andBool notBool #isExpectedClone(TRACECELL, STATECELL, "trace", I)
  rule #isConflict(_, _) => 0 [owise]
  syntax Bool ::= #hasName ( CTerm , String ) [function]
  rule #hasName(cApply("#configCell", cTermCons(cToken(_, NAME, _), _), _), NAME) => true
  rule #hasName(_, _) => false [owise]

  syntax CCandidates ::= #appendCandidates ( CCandidates , CCandidates ) [function]
  rule #appendCandidates(cCandidateNil, R) => R
  rule #appendCandidates(cCandidateCons(I, L), R)
    => cCandidateCons(I, #appendCandidates(L, R))
  syntax Int ::= #candidateCount ( CCandidates ) [function]
  rule #candidateCount(cCandidateNil) => 0
  rule #candidateCount(cCandidateCons(_, R)) => 1 +Int #candidateCount(R)
  syntax Int ::= #productionCount ( CProductions ) [function]
  rule #productionCount(cProductionNil) => 0
  rule #productionCount(cProductionCons(_, R)) => 1 +Int #productionCount(R)
endmodule
