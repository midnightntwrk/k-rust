module P1-SYNTAX
  imports STRING

  syntax PSort ::= pSort ( String )
  syntax PSorts ::= "pSortNil" [symbol(pSortNil)]
                  | pSortCons ( PSort , PSorts )

  syntax PTerms ::= "pTermNil" [symbol(pTermNil)]
                  | pTermCons ( PTerm , PTerms )
  syntax PTerm ::= pVar ( String , String )
                 | pApp ( String , PTerms )
                 | pToken ( String , String )

  syntax PProduction ::= pConstructor ( String , String , PSorts )
                       | pFunction ( String , String , PSorts )
  syntax PProductions ::= "pProductionNil" [symbol(pProductionNil)]
                        | pProductionCons ( PProduction , PProductions )

  syntax PRule ::= pEquation ( PTerm , PTerm , PTerm , PTerm )
                 | pRewrite ( PTerm , PTerm , PTerm , PTerm )
  syntax PRules ::= "pRuleNil" [symbol(pRuleNil)]
                  | pRuleCons ( PRule , PRules )

  syntax PDefinition ::= pDefinition ( String , PSorts , PProductions , PRules )

  syntax KoreSortDecl ::= koreSort ( String )
  syntax KoreSortDecls ::= "koreSortNil" [symbol(koreSortNil)]
                         | koreSortCons ( KoreSortDecl , KoreSortDecls )

  syntax KoreSymbolAttrs ::= "koreConstructorAttrs" [symbol(koreConstructorAttrs)]
                           | "koreFunctionAttrs" [symbol(koreFunctionAttrs)]
  syntax KoreSymbolDecl ::= koreSymbol ( String , String , PSorts , KoreSymbolAttrs )
  syntax KoreSymbolDecls ::= "koreSymbolNil" [symbol(koreSymbolNil)]
                           | koreSymbolCons ( KoreSymbolDecl , KoreSymbolDecls )

  syntax PConstructor ::= pCtor ( String , String )
  syntax PConstructors ::= "pCtorNil" [symbol(pCtorNil)]
                         | pCtorCons ( PConstructor , PConstructors )
  syntax PLabels ::= "pLabelNil" [symbol(pLabelNil)]
                   | pLabelCons ( String , PLabels )

  syntax KoreAxiom ::= koreFunctional ( String )
                     | koreNoConfusionSame ( String )
                     | koreNoConfusionDifferent ( String , String )
                     | koreNoJunk ( String , PLabels )
                     | koreEquation ( PTerm , PTerm , PTerm , PTerm )
                     | koreRewrite ( PTerm , PTerm , PTerm , PTerm )
  syntax KoreAxioms ::= "koreAxiomNil" [symbol(koreAxiomNil)]
                      | koreAxiomCons ( KoreAxiom , KoreAxioms )

  syntax KoreModule ::= koreModule ( String , KoreSortDecls , KoreSymbolDecls , KoreAxioms )
  syntax PProgram ::= PDefinition | KoreModule
endmodule

module P1
  imports P1-SYNTAX
  imports STRING

  syntax PPhase ::= "pIdle"        [symbol(pIdle)]
                  | "pSorts"       [symbol(pSorts)]
                  | "pProductions" [symbol(pProductions)]
                  | "pRules"       [symbol(pRules)]
                  | "pBuild"       [symbol(pBuild)]
                  | "pHalted"      [symbol(pHalted)]

  configuration
    <p1>
      <k> $PGM:PProgram </k>
      <phase> pIdle </phase>
      <moduleName> "" </moduleName>
      <pendingSorts> pSortNil </pendingSorts>
      <allSorts> pSortNil </allSorts>
      <pendingProductions> pProductionNil </pendingProductions>
      <pendingRules> pRuleNil </pendingRules>
      <constructors> pCtorNil </constructors>
      <koreSorts> koreSortNil </koreSorts>
      <koreSymbols> koreSymbolNil </koreSymbols>
      <koreAxioms> koreAxiomNil </koreAxioms>
      <result> .K </result>
    </p1>

  rule <k> pDefinition(MODULE, SORTS, PRODUCTIONS, RULES) => .K ... </k>
       <phase> pIdle => pSorts </phase>
       <moduleName> _ => MODULE </moduleName>
       <pendingSorts> _ => SORTS </pendingSorts>
       <allSorts> _ => SORTS </allSorts>
       <pendingProductions> _ => PRODUCTIONS </pendingProductions>
       <pendingRules> _ => RULES </pendingRules>

  rule <k> MODULE:KoreModule => .K ... </k>
       <phase> pIdle => pHalted </phase>
       <result> .K => MODULE </result>

  rule <phase> pSorts </phase>
       <pendingSorts> pSortCons(pSort(SORT), REST) => REST </pendingSorts>
       <koreSorts> SORTS => koreSortCons(koreSort(SORT), SORTS) </koreSorts>

  rule <phase> pSorts => pProductions </phase>
       <pendingSorts> pSortNil </pendingSorts>

  rule <phase> pProductions </phase>
       <pendingProductions>
         pProductionCons(pConstructor(LABEL, SORT, pSortNil), REST) => REST
       </pendingProductions>
       <constructors> CTORS => pCtorCons(pCtor(LABEL, SORT), CTORS) </constructors>
       <koreSymbols>
         SYMBOLS => koreSymbolCons(koreSymbol(LABEL, SORT, pSortNil, koreConstructorAttrs), SYMBOLS)
       </koreSymbols>
       <koreAxioms>
         AXIOMS => #addDifferent(
           LABEL,
           SORT,
           CTORS,
           koreAxiomCons(koreFunctional(LABEL), AXIOMS)
         )
       </koreAxioms>

  rule <phase> pProductions </phase>
       <pendingProductions>
         pProductionCons(pConstructor(LABEL, SORT, pSortCons(ARG, ARGREST)), REST) => REST
       </pendingProductions>
       <constructors> CTORS => pCtorCons(pCtor(LABEL, SORT), CTORS) </constructors>
       <koreSymbols>
         SYMBOLS => koreSymbolCons(
           koreSymbol(LABEL, SORT, pSortCons(ARG, ARGREST), koreConstructorAttrs), SYMBOLS
         )
       </koreSymbols>
       <koreAxioms>
         AXIOMS => #addDifferent(
           LABEL,
           SORT,
           CTORS,
           koreAxiomCons(
             koreNoConfusionSame(LABEL),
             koreAxiomCons(koreFunctional(LABEL), AXIOMS)
           )
         )
       </koreAxioms>

  rule <phase> pProductions </phase>
       <pendingProductions>
         pProductionCons(pFunction(LABEL, SORT, ARGS), REST) => REST
       </pendingProductions>
       <koreSymbols>
         SYMBOLS => koreSymbolCons(koreSymbol(LABEL, SORT, ARGS, koreFunctionAttrs), SYMBOLS)
       </koreSymbols>

  rule <phase> pProductions => pRules </phase>
       <pendingProductions> pProductionNil </pendingProductions>

  rule <phase> pRules </phase>
       <pendingRules>
         pRuleCons(pEquation(LHS, RHS, REQUIRES, ENSURES), REST) => REST
       </pendingRules>
       <koreAxioms>
         AXIOMS => koreAxiomCons(koreEquation(LHS, RHS, REQUIRES, ENSURES), AXIOMS)
       </koreAxioms>

  rule <phase> pRules </phase>
       <pendingRules>
         pRuleCons(pRewrite(LHS, RHS, REQUIRES, ENSURES), REST) => REST
       </pendingRules>
       <koreAxioms>
         AXIOMS => koreAxiomCons(koreRewrite(LHS, RHS, REQUIRES, ENSURES), AXIOMS)
       </koreAxioms>

  rule <phase> pRules => pBuild </phase>
       <pendingRules> pRuleNil </pendingRules>
       <allSorts> SORTS </allSorts>
       <constructors> CTORS </constructors>
       <koreAxioms> AXIOMS => #addNoJunk(SORTS, CTORS, AXIOMS) </koreAxioms>

  rule <phase> pBuild => pHalted </phase>
       <moduleName> MODULE </moduleName>
       <koreSorts> SORTS </koreSorts>
       <koreSymbols> SYMBOLS </koreSymbols>
       <koreAxioms> AXIOMS </koreAxioms>
       <result> .K => koreModule(MODULE, SORTS, SYMBOLS, AXIOMS) </result>

  syntax KoreAxioms ::= #addDifferent ( String , String , PConstructors , KoreAxioms ) [function]
  rule #addDifferent(_, _, pCtorNil, AXIOMS) => AXIOMS
  rule #addDifferent(LABEL, SORT, pCtorCons(pCtor(OTHER, SORT), REST), AXIOMS)
    => #addDifferent(
         LABEL,
         SORT,
         REST,
         koreAxiomCons(koreNoConfusionDifferent(LABEL, OTHER), AXIOMS)
       )
  rule #addDifferent(LABEL, SORT, pCtorCons(pCtor(_, OTHER_SORT), REST), AXIOMS)
    => #addDifferent(LABEL, SORT, REST, AXIOMS)
    requires SORT =/=String OTHER_SORT

  syntax PLabels ::= #labelsForSort ( String , PConstructors ) [function]
  rule #labelsForSort(_, pCtorNil) => pLabelNil
  rule #labelsForSort(SORT, pCtorCons(pCtor(LABEL, SORT), REST))
    => pLabelCons(LABEL, #labelsForSort(SORT, REST))
  rule #labelsForSort(SORT, pCtorCons(pCtor(_, OTHER_SORT), REST))
    => #labelsForSort(SORT, REST)
    requires SORT =/=String OTHER_SORT

  syntax KoreAxioms ::= #addNoJunk ( PSorts , PConstructors , KoreAxioms ) [function]
  rule #addNoJunk(pSortNil, _, AXIOMS) => AXIOMS
  rule #addNoJunk(pSortCons(pSort(SORT), REST), CTORS, AXIOMS)
    => #addNoJunk(
         REST,
         CTORS,
         koreAxiomCons(koreNoJunk(SORT, #labelsForSort(SORT, CTORS)), AXIOMS)
       )
endmodule
