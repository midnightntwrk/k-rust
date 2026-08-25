module KINK-CONFIGURATION-AUGMENTATION-SYNTAX
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

  syntax CConfiguration ::= cConfiguration (
    String , String , String , String , String , String , String , String ,
    String , CTerm
  )
  syntax CConfigurations ::= "cConfigurationNil" [symbol(cConfigurationNil)]
                           | cConfigurationCons ( CConfiguration , CConfigurations )
  syntax CModule ::= cModule ( String , CConfigurations )
  syntax CModules ::= "cModuleNil" [symbol(cModuleNil)]
                    | cModuleCons ( CModule , CModules )
  syntax CDefinition ::= cDefinition ( String , String , CModules )

  syntax CPathStep ::= cApplicationArgument ( Int )
  syntax CPath ::= "cPathNil" [symbol(cPathNil)]
                 | cPathCons ( CPathStep , CPath )
  syntax COperation ::= cCloneLeafCellFromInput (
    CPath , CPath , String , String
  )
  syntax CAugmentationResult ::= cAugmentationResult (
    String , String , String , Int , String , String , String , String ,
    String , String , COperation
  )
  syntax CAugmentationFailure ::= cAugmentationFailure ( String , String , Int )
  syntax CAugmentationOutcome ::= CAugmentationResult | CAugmentationFailure

  syntax CProgram ::= proposeConfigurationAugmentation ( String , CDefinition )
endmodule

module KINK-CONFIGURATION-AUGMENTATION
  imports KINK-CONFIGURATION-AUGMENTATION-SYNTAX

  configuration <k> $PGM:CProgram </k>

  rule <k> proposeConfigurationAugmentation(
             MODE,
             cDefinition("KConfigurationAugmentation-v1", DEFINITION, MODULES)
           )
        => #emit(
             MODE,
             DEFINITION,
             #modeCandidates(MODE, #selectModules(MODULES)),
             #conflictCountModules(MODULES)
           )
        ... </k>

  syntax CCandidate ::= cCandidate (
    String , String , String , String , String , String , CPath , CPath
  )
  syntax CCandidates ::= "cCandidateNil" [symbol(cCandidateNil)]
                       | cCandidateCons ( CCandidate , CCandidates )

  syntax CCandidates ::= #modeCandidates ( String , CCandidates ) [function]
  rule #modeCandidates("zero-target", _) => cCandidateNil
  rule #modeCandidates(
         "duplicate-target",
         cCandidateCons(ITEM, cCandidateNil)
       ) => cCandidateCons(ITEM, cCandidateCons(ITEM, cCandidateNil))
  rule #modeCandidates(MODE, ITEMS) => ITEMS
    requires MODE =/=String "zero-target"
     andBool MODE =/=String "duplicate-target"

  syntax CAugmentationOutcome ::= #emit (
    String , String , CCandidates , Int
  ) [function]
  rule #emit(_, _, _, CONFLICTS)
    => cAugmentationFailure(
         "KConfigurationAugmentation-v1",
         "conflicting-existing-state",
         CONFLICTS
       )
    requires CONFLICTS >Int 0
  rule #emit(
         MODE,
         DEFINITION,
         cCandidateCons(
           cCandidate(STATUS, LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES, PARENT, TEMPLATE),
           cCandidateNil
         ),
         0
       )
    => #emitOne(
         MODE, DEFINITION, STATUS, LINEAGE, CONTENT, BODY, ENSURES,
         ATTRIBUTES, PARENT, TEMPLATE
       )
  rule #emit(_, _, ITEMS, 0)
    => cAugmentationFailure(
         "KConfigurationAugmentation-v1",
         "structural-target-cardinality",
         #candidateCount(ITEMS)
       ) [owise]

  syntax CAugmentationResult ::= #emitOne (
    String , String , String , String , String , String , String , String ,
    CPath , CPath
  ) [function]
  rule #emitOne(
         "stale-target-content", DEFINITION, STATUS, LINEAGE, _, BODY,
         ENSURES, ATTRIBUTES, PARENT, TEMPLATE
       )
    => #result(
         DEFINITION, STATUS, LINEAGE,
         "0000000000000000000000000000000000000000000000000000000000000000",
         BODY, ENSURES, ATTRIBUTES, PARENT, TEMPLATE
       )
  rule #emitOne(
         "unsupported-path", DEFINITION, STATUS, LINEAGE, CONTENT, BODY,
         ENSURES, ATTRIBUTES, PARENT, _
       )
    => #result(
         DEFINITION, STATUS, LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES,
         PARENT, cPathCons(cApplicationArgument(99), cPathNil)
       )
  rule #emitOne(
         "false-already-present", DEFINITION, _, LINEAGE, CONTENT, BODY,
         ENSURES, ATTRIBUTES, PARENT, TEMPLATE
       )
    => #result(
         DEFINITION, "already-present", LINEAGE, CONTENT, BODY, ENSURES,
         ATTRIBUTES, PARENT, TEMPLATE
       )
  rule #emitOne(
         MODE, DEFINITION, STATUS, LINEAGE, CONTENT, BODY, ENSURES,
         ATTRIBUTES, PARENT, TEMPLATE
       )
    => #result(
         DEFINITION, STATUS, LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES,
         PARENT, TEMPLATE
       )
    requires MODE =/=String "stale-target-content"
     andBool MODE =/=String "unsupported-path"
     andBool MODE =/=String "false-already-present"

  syntax CAugmentationResult ::= #result (
    String , String , String , String , String , String , String , CPath , CPath
  ) [function]
  rule #result(
         DEFINITION, STATUS, LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES,
         PARENT, TEMPLATE
       )
    => cAugmentationResult(
         "KConfigurationAugmentation-v1",
         "p3-add-observation-cell@1",
         DEFINITION,
         1,
         STATUS,
         LINEAGE,
         CONTENT,
         BODY,
         ENSURES,
         ATTRIBUTES,
         cCloneLeafCellFromInput(PARENT, TEMPLATE, "observation", "0")
       )

  syntax CCandidates ::= #selectModules ( CModules ) [function]
  rule #selectModules(cModuleNil) => cCandidateNil
  rule #selectModules(cModuleCons(cModule(_, CONFIGS), REST))
    => #appendCandidates(#selectConfigurations(CONFIGS), #selectModules(REST))

  syntax CCandidates ::= #selectConfigurations ( CConfigurations ) [function]
  rule #selectConfigurations(cConfigurationNil) => cCandidateNil
  rule #selectConfigurations(cConfigurationCons(CONFIG, REST))
    => #appendCandidates(#selectConfiguration(CONFIG), #selectConfigurations(REST))

  syntax CCandidates ::= #selectConfiguration ( CConfiguration ) [function]
  rule #selectConfiguration(
         cConfiguration(
           _, _, _, _, LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES,
           cApply(
             "#configCell",
             cTermCons(
               cToken("#CellName", "T", _),
               cTermCons(
                 _,
                 cTermCons(
                   cApply(
                     "#cells",
                     cTermCons(
                       KCELL,
                       cTermCons(STATECELL, cTermNil)
                     ),
                     _
                   ),
                   cTermCons(cToken("#CellName", "T", _), cTermNil)
                 )
               )
             ),
             _
           )
         )
       )
    => cCandidateCons(
         cCandidate(
           "apply", LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES,
           cPathCons(cApplicationArgument(2), cPathNil),
           cPathCons(
             cApplicationArgument(2),
             cPathCons(cApplicationArgument(1), cPathNil)
           )
         ),
         cCandidateNil
       )
    requires #isKCell(KCELL) andBool #isStateCell(STATECELL)
  rule #selectConfiguration(
         cConfiguration(
           _, _, _, _, LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES,
           cApply(
             "#configCell",
             cTermCons(
               cToken("#CellName", "T", _),
               cTermCons(
                 _,
                 cTermCons(
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
                   ),
                   cTermCons(cToken("#CellName", "T", _), cTermNil)
                 )
               )
             ),
             _
           )
         )
       )
    => cCandidateCons(
         cCandidate(
           "already-present", LINEAGE, CONTENT, BODY, ENSURES, ATTRIBUTES,
           cPathCons(cApplicationArgument(2), cPathNil),
           cPathCons(
             cApplicationArgument(2),
             cPathCons(
               cApplicationArgument(0),
               cPathCons(cApplicationArgument(1), cPathNil)
             )
           )
         ),
         cCandidateNil
       )
    requires #isKCell(KCELL)
     andBool #isStateCell(STATECELL)
     andBool #isObservationCell(OBSERVATION)
  rule #selectConfiguration(_) => cCandidateNil [owise]

  syntax Bool ::= #isKCell ( CTerm ) [function]
  rule #isKCell(cApply(
         "#configCell",
         cTermCons(
           cToken("#CellName", "k", _),
           cTermCons(_, cTermCons(_, cTermCons(cToken("#CellName", "k", _), cTermNil)))
         ),
         _
       )) => true
  rule #isKCell(_) => false [owise]

  syntax Bool ::= #isStateCell ( CTerm ) [function]
  rule #isStateCell(cApply(
         "#configCell",
         cTermCons(
           cToken("#CellName", "state", _),
           cTermCons(
             _,
             cTermCons(
               cToken("Int", "1", _),
               cTermCons(cToken("#CellName", "state", _), cTermNil)
             )
           )
         ),
         _
       )) => true
  rule #isStateCell(_) => false [owise]

  syntax Bool ::= #isObservationCell ( CTerm ) [function]
  rule #isObservationCell(cApply(
         "#configCell",
         cTermCons(
           cToken("#CellName", "observation", _),
           cTermCons(
             _,
             cTermCons(
               cToken("Int", "0", _),
               cTermCons(cToken("#CellName", "observation", _), cTermNil)
             )
           )
         ),
         _
       )) => true
  rule #isObservationCell(_) => false [owise]

  syntax Int ::= #conflictCountModules ( CModules ) [function]
  rule #conflictCountModules(cModuleNil) => 0
  rule #conflictCountModules(cModuleCons(cModule(_, CONFIGS), REST))
    => #conflictCountConfigurations(CONFIGS) +Int #conflictCountModules(REST)

  syntax Int ::= #conflictCountConfigurations ( CConfigurations ) [function]
  rule #conflictCountConfigurations(cConfigurationNil) => 0
  rule #conflictCountConfigurations(cConfigurationCons(CONFIG, REST))
    => #isConflict(CONFIG) +Int #conflictCountConfigurations(REST)

  syntax Int ::= #isConflict ( CConfiguration ) [function]
  rule #isConflict(
         cConfiguration(
           _, _, _, _, _, _, _, _, _,
           cApply(
             "#configCell",
             cTermCons(
               cToken("#CellName", "T", _),
               cTermCons(
                 _,
                 cTermCons(
                   cApply(
                     "#cells",
                     cTermCons(
                       cApply(
                         "#cells",
                         cTermCons(KCELL, cTermCons(STATECELL, cTermNil)),
                         _
                       ),
                       cTermCons(
                         cApply(
                           "#configCell",
                           cTermCons(
                             cToken("#CellName", "observation", _),
                             cTermCons(_, cTermCons(VALUE, cTermCons(cToken("#CellName", "observation", _), cTermNil)))
                           ),
                           _
                         ),
                         cTermNil
                       )
                     ),
                     _
                   ),
                   cTermCons(cToken("#CellName", "T", _), cTermNil)
                 )
               )
             ),
             _
           )
         )
       ) => 1
    requires #isKCell(KCELL)
     andBool #isStateCell(STATECELL)
     andBool notBool #isExactObservationValue(VALUE)
  rule #isConflict(_) => 0 [owise]

  syntax Bool ::= #isExactObservationValue ( CTerm ) [function]
  rule #isExactObservationValue(cToken("Int", "0", _)) => true
  rule #isExactObservationValue(_) => false [owise]

  syntax CCandidates ::= #appendCandidates ( CCandidates , CCandidates ) [function]
  rule #appendCandidates(cCandidateNil, RIGHT) => RIGHT
  rule #appendCandidates(cCandidateCons(ITEM, REST), RIGHT)
    => cCandidateCons(ITEM, #appendCandidates(REST, RIGHT))

  syntax Int ::= #candidateCount ( CCandidates ) [function]
  rule #candidateCount(cCandidateNil) => 0
  rule #candidateCount(cCandidateCons(_, REST)) => 1 +Int #candidateCount(REST)
endmodule
