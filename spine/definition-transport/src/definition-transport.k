module KINK-DEFINITION-TRANSPORT-SYNTAX
  imports STRING
  imports INT
  imports BOOL

  syntax DImport ::= dImport ( String , Bool )
  syntax DImports ::= "dImportNil" [symbol(dImportNil)]
                    | dImportCons ( DImport , DImports )

  syntax DMeta ::= dMeta ( String , String , String )

  syntax DTerms ::= "dTermNil" [symbol(dTermNil)]
                  | dTermCons ( DTerm , DTerms )

  syntax DTerm ::= dApply ( String , DTerms , DMeta )
                 | dToken ( String , String , DMeta )
                 | dVariable ( String , DMeta )
                 | dRewrite ( DTerm , DTerm , DMeta )
                 | dSequence ( DTerms , DMeta )
                 | dAs ( DTerm , DTerm , DMeta )
                 | dInjectedLabel ( String , DMeta )

  syntax DIdentity ::= dIdentity (
    String , Int , String , String , String , String , String , String
  )

  syntax DSentence ::= dRule (
    DIdentity , DTerm , DTerm , DTerm , String , String , String
  )

  syntax DSentences ::= "dSentenceNil" [symbol(dSentenceNil)]
                      | dSentenceCons ( DSentence , DSentences )

  syntax DModule ::= dModule ( String , DImports , DSentences )
  syntax DModules ::= "dModuleNil" [symbol(dModuleNil)]
                    | dModuleCons ( DModule , DModules )

  syntax DDefinition ::= dDefinition ( String , String , DModules )

  syntax DSelection ::= dSelection ( String , String , String )
  syntax DSelections ::= "dSelectionNil" [symbol(dSelectionNil)]
                       | dSelectionCons ( DSelection , DSelections )

  syntax DResult ::= dResult ( String , Int , DSelections )

  syntax DPathStep ::= "dRewriteLeft" [symbol(dRewriteLeft)]
                     | "dRewriteRight" [symbol(dRewriteRight)]
                     | dApplicationArgument ( Int )
                     | dSequenceItem ( Int )
  syntax DPath ::= "dPathNil" [symbol(dPathNil)]
                 | dPathCons ( DPathStep , DPath )

  syntax DEdit ::= dReplaceTermFromInput ( DPath , DPath )
  syntax DEdits ::= "dEditNil" [symbol(dEditNil)]
                  | dEditCons ( DEdit , DEdits )

  syntax DPatchCandidate ::= dPatchCandidate (
    String , String , String , DPath , DPath
  )
  syntax DPatchCandidates ::= "dPatchCandidateNil" [symbol(dPatchCandidateNil)]
                            | dPatchCandidateCons ( DPatchCandidate , DPatchCandidates )

  syntax DPatchResult ::= dPatchResult (
    String , String , String , Int , String , String , String , Int , DEdits
  )

  syntax DTransactionEdit ::= dTransactionEdit (
    String , String , String , DEdit
  )
  syntax DTransactionEdits ::= "dTransactionEditNil" [symbol(dTransactionEditNil)]
                             | dTransactionEditCons (
                                 DTransactionEdit , DTransactionEdits
                               )
  syntax DTransactionResult ::= dTransactionResult (
    String , String , String , Int , Int , DTransactionEdits
  )

  syntax DProgram ::= selectDefinition ( DDefinition )
                    | proposeDefinitionPatch ( String , DDefinition )
                    | proposeDefinitionTransaction ( String , DDefinition )
endmodule

module KINK-DEFINITION-TRANSPORT
  imports KINK-DEFINITION-TRANSPORT-SYNTAX

  configuration <k> $PGM:DProgram </k>

  rule <k> selectDefinition(dDefinition("KDefinitionTransport-v1", FINGERPRINT, MODULES))
        => dResult(
             FINGERPRINT,
             #selectionCount(#selectModules(MODULES)),
             #selectModules(MODULES)
           )
        ... </k>

  rule <k> proposeDefinitionPatch(
             MODE,
             dDefinition("KDefinitionTransport-v1", FINGERPRINT, MODULES)
           )
        => #makePatch(MODE, FINGERPRINT, #patchModules(MODULES))
        ... </k>

  rule <k> proposeDefinitionTransaction(
             MODE,
             dDefinition("KDefinitionTransport-v1", FINGERPRINT, MODULES)
           )
        => #makeTransaction(MODE, FINGERPRINT, #transactionModules(MODULES))
        ... </k>

  syntax DTransactionResult ::= #makeTransaction (
    String , String , DPatchCandidates
  ) [function]
  rule #makeTransaction(
         MODE,
         FINGERPRINT,
         dPatchCandidateCons(FIRST, dPatchCandidateCons(SECOND, dPatchCandidateNil))
       )
    => #emitTransaction(MODE, FINGERPRINT, #orderTwoCandidates(FIRST, SECOND))

  syntax DPatchCandidates ::= #orderTwoCandidates (
    DPatchCandidate , DPatchCandidate
  ) [function]
  rule #orderTwoCandidates(FIRST, SECOND)
    => dPatchCandidateCons(FIRST, dPatchCandidateCons(SECOND, dPatchCandidateNil))
    requires #candidateCanonical(FIRST) <=String #candidateCanonical(SECOND)
  rule #orderTwoCandidates(FIRST, SECOND)
    => dPatchCandidateCons(SECOND, dPatchCandidateCons(FIRST, dPatchCandidateNil))
    requires #candidateCanonical(FIRST) >String #candidateCanonical(SECOND)

  syntax DTransactionResult ::= #emitTransaction (
    String , String , DPatchCandidates
  ) [function]
  rule #emitTransaction(
         "transaction",
         FINGERPRINT,
         dPatchCandidateCons(FIRST, dPatchCandidateCons(SECOND, dPatchCandidateNil))
       )
    => #transactionResult(FINGERPRINT, FIRST, SECOND)
  rule #emitTransaction(
         "transaction-stale-first",
         FINGERPRINT,
         dPatchCandidateCons(
           dPatchCandidate(FIRST_LINEAGE, _, FIRST_BODY, FIRST_TARGET, FIRST_REPLACEMENT),
           dPatchCandidateCons(SECOND, dPatchCandidateNil)
         )
       )
    => #transactionResult(
         FINGERPRINT,
         dPatchCandidate(
           FIRST_LINEAGE,
           "0000000000000000000000000000000000000000000000000000000000000000",
           FIRST_BODY,
           FIRST_TARGET,
           FIRST_REPLACEMENT
         ),
         SECOND
       )
  rule #emitTransaction(
         "transaction-stale-second",
         FINGERPRINT,
         dPatchCandidateCons(
           FIRST,
           dPatchCandidateCons(
             dPatchCandidate(SECOND_LINEAGE, _, SECOND_BODY, SECOND_TARGET, SECOND_REPLACEMENT),
             dPatchCandidateNil
           )
         )
       )
    => #transactionResult(
         FINGERPRINT,
         FIRST,
         dPatchCandidate(
           SECOND_LINEAGE,
           "0000000000000000000000000000000000000000000000000000000000000000",
           SECOND_BODY,
           SECOND_TARGET,
           SECOND_REPLACEMENT
         )
       )
  rule #emitTransaction(
         "transaction-duplicate-target",
         FINGERPRINT,
         dPatchCandidateCons(FIRST, dPatchCandidateCons(_, dPatchCandidateNil))
       )
    => #transactionResult(FINGERPRINT, FIRST, FIRST)

  syntax DTransactionResult ::= #transactionResult (
    String , DPatchCandidate , DPatchCandidate
  ) [function]
  rule #transactionResult(
         FINGERPRINT,
         dPatchCandidate(
           FIRST_LINEAGE,
           FIRST_CONTENT,
           FIRST_BODY,
           FIRST_TARGET,
           FIRST_REPLACEMENT
         ),
         dPatchCandidate(
           SECOND_LINEAGE,
           SECOND_CONTENT,
           SECOND_BODY,
           SECOND_TARGET,
           SECOND_REPLACEMENT
         )
       )
    => dTransactionResult(
         "KDefinitionPatch-v2",
         "p3-start-and-add-values@1",
         FINGERPRINT,
         1,
         2,
         dTransactionEditCons(
           dTransactionEdit(
             FIRST_LINEAGE,
             FIRST_CONTENT,
             FIRST_BODY,
             dReplaceTermFromInput(FIRST_TARGET, FIRST_REPLACEMENT)
           ),
           dTransactionEditCons(
             dTransactionEdit(
               SECOND_LINEAGE,
               SECOND_CONTENT,
               SECOND_BODY,
               dReplaceTermFromInput(SECOND_TARGET, SECOND_REPLACEMENT)
             ),
             dTransactionEditNil
           )
         )
       )

  syntax String ::= #candidateCanonical ( DPatchCandidate ) [function]
  rule #candidateCanonical(
         dPatchCandidate(LINEAGE, CONTENT, BODY, TARGET, REPLACEMENT)
       )
    => "dTransactionEdit(\""
       +String LINEAGE
       +String "\",\""
       +String CONTENT
       +String "\",\""
       +String BODY
       +String "\",dReplaceTermFromInput("
       +String #pathCanonical(TARGET)
       +String ","
       +String #pathCanonical(REPLACEMENT)
       +String "))"

  syntax String ::= #pathCanonical ( DPath ) [function]
  rule #pathCanonical(dPathNil) => "dPathNil"
  rule #pathCanonical(dPathCons(STEP, REST))
    => "dPathCons("
       +String #pathStepCanonical(STEP)
       +String ","
       +String #pathCanonical(REST)
       +String ")"

  syntax String ::= #pathStepCanonical ( DPathStep ) [function]
  rule #pathStepCanonical(dRewriteLeft) => "dRewriteLeft"
  rule #pathStepCanonical(dRewriteRight) => "dRewriteRight"
  rule #pathStepCanonical(dApplicationArgument(INDEX))
    => "dApplicationArgument(" +String Int2String(INDEX) +String ")"
  rule #pathStepCanonical(dSequenceItem(INDEX))
    => "dSequenceItem(" +String Int2String(INDEX) +String ")"

  syntax DPatchCandidates ::= #transactionModules ( DModules ) [function]
  rule #transactionModules(dModuleNil) => dPatchCandidateNil
  rule #transactionModules(dModuleCons(dModule(_, _, SENTENCES), REST))
    => #appendPatchCandidates(
         #transactionSentences(SENTENCES),
         #transactionModules(REST)
       )

  syntax DPatchCandidates ::= #transactionSentences ( DSentences ) [function]
  rule #transactionSentences(dSentenceNil) => dPatchCandidateNil
  rule #transactionSentences(dSentenceCons(SENTENCE, REST))
    => #appendPatchCandidates(
         #transactionSentence(SENTENCE),
         #transactionSentences(REST)
       )

  syntax DPatchCandidates ::= #transactionSentence ( DSentence ) [function]
  rule #transactionSentence(
         dRule(
           dIdentity(_, _, _, _, _, _, LINEAGE, CONTENT),
           BODY,
           _,
           _,
           _,
           _,
           BODY_FINGERPRINT
         )
       )
    => dPatchCandidateCons(
         dPatchCandidate(
           LINEAGE,
           CONTENT,
           BODY_FINGERPRINT,
           dPathCons(dRewriteRight, dPathNil),
           dPathCons(
             dRewriteRight,
             dPathCons(dApplicationArgument(1), dPathNil)
           )
         ),
         dPatchCandidateNil
       )
    requires #isStartReadBump(BODY)
  rule #transactionSentence(
         dRule(
           dIdentity(_, _, _, _, _, _, LINEAGE, CONTENT),
           BODY,
           _,
           _,
           _,
           _,
           BODY_FINGERPRINT
         )
       )
    => dPatchCandidateCons(
         dPatchCandidate(
           LINEAGE,
           CONTENT,
           BODY_FINGERPRINT,
           dPathCons(dRewriteRight, dPathNil),
           dPathCons(
             dRewriteLeft,
             dPathCons(dApplicationArgument(1), dPathNil)
           )
         ),
         dPatchCandidateNil
       )
    requires #isVariableAddition(BODY)
  rule #transactionSentence(_) => dPatchCandidateNil [owise]

  syntax DPatchResult ::= #makePatch ( String , String , DPatchCandidates ) [function]
  rule #makePatch(
         "patch",
         FINGERPRINT,
         dPatchCandidateCons(
           dPatchCandidate(LINEAGE, CONTENT, BODY, TARGET_PATH, REPLACEMENT_PATH),
           dPatchCandidateNil
         )
       )
    => dPatchResult(
         "KDefinitionPatch-v1",
         "p3-start-to-bump@1",
         FINGERPRINT,
         1,
         LINEAGE,
         CONTENT,
         BODY,
         1,
         dEditCons(
           dReplaceTermFromInput(TARGET_PATH, REPLACEMENT_PATH),
           dEditNil
         )
       )
  rule #makePatch(
         "patch-stale-content",
         FINGERPRINT,
         dPatchCandidateCons(
           dPatchCandidate(LINEAGE, _, BODY, TARGET_PATH, REPLACEMENT_PATH),
           dPatchCandidateNil
         )
       )
    => dPatchResult(
         "KDefinitionPatch-v1",
         "p3-start-to-bump@1",
         FINGERPRINT,
         1,
         LINEAGE,
         "0000000000000000000000000000000000000000000000000000000000000000",
         BODY,
         1,
         dEditCons(
           dReplaceTermFromInput(TARGET_PATH, REPLACEMENT_PATH),
           dEditNil
         )
       )
  rule #makePatch(
         "patch-unsupported-path",
         FINGERPRINT,
         dPatchCandidateCons(
           dPatchCandidate(LINEAGE, CONTENT, BODY, _, REPLACEMENT_PATH),
           dPatchCandidateNil
         )
       )
    => dPatchResult(
         "KDefinitionPatch-v1",
         "p3-start-to-bump@1",
         FINGERPRINT,
         1,
         LINEAGE,
         CONTENT,
         BODY,
         1,
         dEditCons(
           dReplaceTermFromInput(
             dPathCons(dSequenceItem(0), dPathNil),
             REPLACEMENT_PATH
           ),
           dEditNil
         )
       )

  syntax DPatchCandidates ::= #patchModules ( DModules ) [function]
  rule #patchModules(dModuleNil) => dPatchCandidateNil
  rule #patchModules(dModuleCons(dModule(_, _, SENTENCES), REST))
    => #appendPatchCandidates(#patchSentences(SENTENCES), #patchModules(REST))

  syntax DPatchCandidates ::= #patchSentences ( DSentences ) [function]
  rule #patchSentences(dSentenceNil) => dPatchCandidateNil
  rule #patchSentences(dSentenceCons(SENTENCE, REST))
    => #appendPatchCandidates(#patchSentence(SENTENCE), #patchSentences(REST))

  syntax DPatchCandidates ::= #patchSentence ( DSentence ) [function]
  rule #patchSentence(
         dRule(
           dIdentity(_, _, _, _, _, _, LINEAGE, CONTENT),
           BODY,
           _,
           _,
           _,
           _,
           BODY_FINGERPRINT
         )
       )
    => dPatchCandidateCons(
         dPatchCandidate(
           LINEAGE,
           CONTENT,
           BODY_FINGERPRINT,
           dPathCons(dRewriteRight, dPathNil),
           dPathCons(
             dRewriteRight,
             dPathCons(dApplicationArgument(1), dPathNil)
           )
         ),
         dPatchCandidateNil
       )
    requires #isStartReadBump(BODY)
  rule #patchSentence(_) => dPatchCandidateNil [owise]

  syntax DPatchCandidates ::= #appendPatchCandidates (
    DPatchCandidates , DPatchCandidates
  ) [function]
  rule #appendPatchCandidates(dPatchCandidateNil, RIGHT) => RIGHT
  rule #appendPatchCandidates(dPatchCandidateCons(ITEM, REST), RIGHT)
    => dPatchCandidateCons(ITEM, #appendPatchCandidates(REST, RIGHT))

  syntax DSelections ::= #selectModules ( DModules ) [function]
  rule #selectModules(dModuleNil) => dSelectionNil
  rule #selectModules(dModuleCons(dModule(_, _, SENTENCES), REST))
    => #appendSelections(#selectSentences(SENTENCES), #selectModules(REST))

  syntax DSelections ::= #selectSentences ( DSentences ) [function]
  rule #selectSentences(dSentenceNil) => dSelectionNil
  rule #selectSentences(dSentenceCons(SENTENCE, REST))
    => #appendSelections(#selectSentence(SENTENCE), #selectSentences(REST))

  syntax DSelections ::= #selectSentence ( DSentence ) [function]
  rule #selectSentence(
         dRule(
           dIdentity(_, _, _, _, _, _, LINEAGE, CONTENT),
           BODY,
           _,
           _,
           _,
           _,
           BODY_FINGERPRINT
         )
       )
    => dSelectionCons(dSelection(LINEAGE, CONTENT, BODY_FINGERPRINT), dSelectionNil)
    requires #isStartReadBump(BODY)
  rule #selectSentence(_) => dSelectionNil [owise]

  syntax Bool ::= #isStartReadBump ( DTerm ) [function]
  rule #isStartReadBump(
         dRewrite(
           dApply("start", dTermNil, _),
           dApply(
             "add",
             dTermCons(
               dApply("read", dTermNil, _),
               dTermCons(dApply("bump", dTermNil, _), dTermNil)
             ),
             _
           ),
           _
         )
       ) => true
  rule #isStartReadBump(_) => false [owise]

  syntax Bool ::= #isVariableAddition ( DTerm ) [function]
  rule #isVariableAddition(
         dRewrite(
           dApply(
             "add",
             dTermCons(
               dApply(
                 "#SemanticCastToInt",
                 dTermCons(dVariable(FIRST, _), dTermNil),
                 _
               ),
               dTermCons(
                 dApply(
                   "#SemanticCastToInt",
                   dTermCons(dVariable(SECOND, _), dTermNil),
                   _
                 ),
                 dTermNil
               )
             ),
             _
           ),
           dApply(
             "_+Int_",
             dTermCons(
               dApply(
                 "#SemanticCastToInt",
                 dTermCons(dVariable(FIRST, _), dTermNil),
                 _
               ),
               dTermCons(
                 dApply(
                   "#SemanticCastToInt",
                   dTermCons(dVariable(SECOND, _), dTermNil),
                   _
                 ),
                 dTermNil
               )
             ),
             _
           ),
           _
         )
       ) => true
  rule #isVariableAddition(_) => false [owise]

  syntax DSelections ::= #appendSelections ( DSelections , DSelections ) [function]
  rule #appendSelections(dSelectionNil, RIGHT) => RIGHT
  rule #appendSelections(dSelectionCons(ITEM, REST), RIGHT)
    => dSelectionCons(ITEM, #appendSelections(REST, RIGHT))

  syntax Int ::= #selectionCount ( DSelections ) [function]
  rule #selectionCount(dSelectionNil) => 0
  rule #selectionCount(dSelectionCons(_, REST)) => 1 +Int #selectionCount(REST)
endmodule
