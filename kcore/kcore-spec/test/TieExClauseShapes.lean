/-
  The existential-clause sentences of the CE texts against Γ's items, one namespace per fixture
  (test/constructs/fixtures), each on the fixture's kompiled text under f2-examples. Indices are
  `AxiomDecl.index`. Run from the package root: `lake env lean -j1 test/TieExClauseShapes.lean`.

  Γ reads each of these equations as one clause with existential variables (`existentialClause`,
  `Parse.ceRead`); its item is not the sentence's translation (`un<j>_differs` in the fixture's
  tie). For each sentence here:
  - `text_shape<n>` (kernel): the translated sentence is `eqnPat` with the right side the text
    writes; `gamma_shape<n>` (kernel): Γ's item j is `eqnPat` over the same guards, premise, sort and
    left side, with the clause's right side. The parts are read off the sentence (`rhsK`, `argK`,
    `exBK`, ...), so the two shapes share them.
  - `iff<n>`: the two hold in the same interpretations among those with the signature's facts
    (`TieFRSig.SigFacts`: definedness, the item of `⌈_⌉`, each numbered sort one sort), by the lemma
    of `KcoreSpec/TieExClause.lean` its header line names. Where the lemma is
    `ExEnsTop.eqnPat_ensTop` no fact is read. Sentence 204 of e3-ml-eq-rhs-ceil-and reads one more
    fact of the signature: the elements of `f(X)` lie in Int (`TieFRSig.TermsInSortNI`, from f's
    arity item in `ΓSig`), so that an element of `f(X) ∧ g(X)` is one the clause's variable holds.
  - `ex_from_text<n>` (W1), for every H: Γ's item j is a consequence of
    `TiePair.Texts [sentence n] ∪ ΓSig (cH H)` (the sentence, definedness, the signature); no
    `ΓDomains`, no `Γcl`, no functional sentence.
  - `ex_entailed<n>` (E), for every H: `Γ (cH H)` entails sentence n; `ex_entailed_c<n>`: so does
    `Γc (cH H)`.

  The sentence of e3-eq-exists-partial-ml (131) is tied in test/TieE3EqExistsPartialMl131.lean.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieExClauseShapes

open ML KoreAML KoreAML.TieFR KCore.TieExClause

/-! ## The parts of an equation sentence -/

def premK : Kore.Pattern → Kore.Pattern
  | .implies _ p _ => p
  | p => p
def lhsK : Kore.Pattern → Kore.Pattern
  | .implies _ _ (.equals _ _ l _) => l
  | p => p
def rhsK : Kore.Pattern → Kore.Pattern
  | .implies _ _ (.equals _ _ _ (.and _ [r, _])) => r
  | p => p
def ensK : Kore.Pattern → Kore.Pattern
  | .implies _ _ (.equals _ _ _ (.and _ [_, e])) => e
  | p => p
/-- The body of an `\exists`. -/
def exBK : Kore.Pattern → Kore.Pattern
  | .exist _ _ b => b
  | p => p
/-- The variable an `\exists` binds, in the table. -/
def exVK (tbl : VarTable) : Kore.Pattern → EVar
  | .exist _ x _ => tbl.ev (evarKey x)
  | _ => ⟨0⟩
/-- The operand i of a conjunction, a disjunction or an application. -/
def argK (i : Nat) : Kore.Pattern → Kore.Pattern
  | .and _ ps => ps.getD i (.string "")
  | .or _ ps => ps.getD i (.string "")
  | .app _ _ ps => ps.getD i (.string "")
  | p => p
def ceilK : Kore.Pattern → Kore.Pattern
  | .ceil _ _ p => p
  | p => p
def eqLK : Kore.Pattern → Kore.Pattern
  | .equals _ _ l _ => l
  | p => p
def eqRK : Kore.Pattern → Kore.Pattern
  | .equals _ _ _ r => r
  | p => p

/-- A numbered sort's pattern, by its name, denotes a sort. -/
theorem sortAtN {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M} (F : TieFRSig.SigFacts c I)
    {s : Srt} {n : String} (hn : c.sortName s = n) (hs : s < nRegSorts + c.sortNames.length) (tbl : VarTable) :
    ∃ τ, SortAt I (trSort tbl (srt n)) τ := by
  obtain ⟨τ, h⟩ := sortAt_sig F hs tbl
  have he : srtOf c s = srt n := by unfold srtOf; rw [hn]
  exact ⟨τ, he ▸ h⟩

/-! ## e3-eq-exists-ctor-ml -/

namespace Ctor

kore_term kore from "f2-examples/e3-eq-exists-ctor-ml.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ctor-ml.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ctor-ml.kompile.kore" module "E3-EQ-EXISTS-CTOR-ML"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK


/-! ### Sentence 187: `pick(X) => #Exists C:Col. (C #And {(C =/=K X) #Equals true})` (`ExEnsTop.eqnPat_ensTop`) -/

noncomputable def tbl187 : VarTable := tableOf U.ax187.ax.sortVars U.ax187.ax.pattern
noncomputable abbrev ctx187 : Ctx := ⟨tbl187, kore.aliasNames⟩
noncomputable def ws187 : List P := guardsOf U.ax187.ax
noncomputable def r187 : EVar := tbl187.ev (sortVarKey Rv)
noncomputable def prem187 : P := tr ctx187 (premK U.ax187.ax.pattern)
noncomputable def S187 : P := trSort tbl187 (srt "Col")
noncomputable def F187 : P := tr ctx187 (lhsK U.ax187.ax.pattern)
noncomputable def ens187 : P := tr ctx187 (ensK U.ax187.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K187 : Kore.Pattern := rhsK U.ax187.ax.pattern
noncomputable def x187 : EVar := exVK tbl187 K187
noncomputable def psi187 : P := tr ctx187 (argK 1 (exBK K187))

theorem text_shape187 : (trS U.ax187).pat = eqnPat ws187 r187 prem187 S187 F187 (sAnd (sExists x187 S187 (sAnd (.evar x187) psi187)) ens187) := by
  decide +kernel

theorem gamma_shape187 : (TiePair.gammaPats c)[0]? = some (eqnPat ws187 r187 prem187 S187 F187 (sAnd (sExists x187 S187 (sAnd (.evar x187) (sAnd (sTop S187) psi187))) ens187)) := by
  decide +kernel

theorem guard_r187 : sortGuard r187 ∈ ws187 := by decide +kernel
theorem top_free187 : S187.isFreeEvar topVar = false := by decide +kernel

theorem iff187 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (_F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws187 r187 prem187 S187 F187 (sAnd (sExists x187 S187 (sAnd (.evar x187) (sAnd (sTop S187) psi187))) ens187)) ↔ (I ⊧ᴵ (trS U.ax187).pat) := by
  rw [text_shape187]
  exact ExEnsTop.eqnPat_ensTop top_free187

/-- **W1**: Γ's item 0 is a consequence of sentence 187 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text187 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax187).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape187) fun F _ => iff187 H F).1

/-- **E**: Γ entails sentence 187, for every H. -/
theorem ex_entailed187 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax187).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape187) fun F _ => iff187 H F).2

theorem ex_entailed_c187 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax187).pat := by
  intro M _ I hIc
  exact ex_entailed187 H fun φ hφ => hIc φ (Or.inl hφ)

end Ctor

/-! ## e3-eq-exists-ml-supersort -/

namespace Supersort

kore_term kore from "f2-examples/e3-eq-exists-ml-supersort.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-supersort.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-supersort.kompile.kore" module "E3-EQ-EXISTS-ML-SUPERSORT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameKItem (H : HookParams) : (cH H).sortName (Srt.kitem) = "KItem" := (by decide +kernel : c.sortName (Srt.kitem) = "KItem")
theorem ltKItem (H : HookParams) : (Srt.kitem : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.kitem : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 200: `f(X) => #Exists B:Bool. (B #And {B #Equals (X >Int 0)})`, f of sort KItem (`ensTop_ex_body`) -/

noncomputable def tbl200 : VarTable := tableOf U.ax200.ax.sortVars U.ax200.ax.pattern
noncomputable abbrev ctx200 : Ctx := ⟨tbl200, kore.aliasNames⟩
noncomputable def ws200 : List P := guardsOf U.ax200.ax
noncomputable def r200 : EVar := tbl200.ev (sortVarKey Rv)
noncomputable def prem200 : P := tr ctx200 (premK U.ax200.ax.pattern)
noncomputable def S200 : P := trSort tbl200 (srt "KItem")
noncomputable def F200 : P := tr ctx200 (lhsK U.ax200.ax.pattern)
noncomputable def ens200 : P := tr ctx200 (ensK U.ax200.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K200 : Kore.Pattern := rhsK U.ax200.ax.pattern
noncomputable def x200 : EVar := exVK tbl200 K200
noncomputable def sB200 : P := trSort tbl200 (srt "Bool")
noncomputable def t200 : P := tr ctx200 (argK 0 (exBK K200))
noncomputable def psi200 : P := tr ctx200 (argK 1 (exBK K200))

theorem text_shape200 : (trS U.ax200).pat = eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists x200 sB200 (sAnd t200 psi200)) ens200) := by
  decide +kernel

theorem gamma_shape200 : (TiePair.gammaPats c)[0]? = some (eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists x200 sB200 (sAnd t200 (sAnd (sTop S200) psi200))) ens200)) := by
  decide +kernel

theorem guard_r200 : sortGuard r200 ∈ ws200 := by decide +kernel

theorem iff200 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists x200 sB200 (sAnd t200 (sAnd (sTop S200) psi200))) ens200)) ↔ (I ⊧ᴵ (trS U.ax200).pat) := by
  rw [text_shape200]
  obtain ⟨σ, hS⟩ := sortAtN F (nameKItem H) (ltKItem H) tbl200
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r200 (guardsOf_pred F.defOK U.ax200.ax) fun e m hat a ha =>
    ensTop_ex_body F.defOK hS ha

/-- **W1**: Γ's item 0 is a consequence of sentence 200 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text200 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax200).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape200) fun F _ => iff200 H F).1

/-- **E**: Γ entails sentence 200, for every H. -/
theorem ex_entailed200 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax200).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape200) fun F _ => iff200 H F).2

theorem ex_entailed_c200 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax200).pat := by
  intro M _ I hIc
  exact ex_entailed200 H fun φ hφ => hIc φ (Or.inl hφ)

/-! ### Sentence 203: `h(K) => #Exists Z:Int. (Z #And {Z #Equals K})` (`ExEnsTop.eqnPat_ensTop`) -/

noncomputable def tbl203 : VarTable := tableOf U.ax203.ax.sortVars U.ax203.ax.pattern
noncomputable abbrev ctx203 : Ctx := ⟨tbl203, kore.aliasNames⟩
noncomputable def ws203 : List P := guardsOf U.ax203.ax
noncomputable def r203 : EVar := tbl203.ev (sortVarKey Rv)
noncomputable def prem203 : P := tr ctx203 (premK U.ax203.ax.pattern)
noncomputable def S203 : P := trSort tbl203 (srt "Int")
noncomputable def F203 : P := tr ctx203 (lhsK U.ax203.ax.pattern)
noncomputable def ens203 : P := tr ctx203 (ensK U.ax203.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K203 : Kore.Pattern := rhsK U.ax203.ax.pattern
noncomputable def x203 : EVar := exVK tbl203 K203
noncomputable def psi203 : P := tr ctx203 (argK 1 (exBK K203))

theorem text_shape203 : (trS U.ax203).pat = eqnPat ws203 r203 prem203 S203 F203 (sAnd (sExists x203 S203 (sAnd (.evar x203) psi203)) ens203) := by
  decide +kernel

theorem gamma_shape203 : (TiePair.gammaPats c)[1]? = some (eqnPat ws203 r203 prem203 S203 F203 (sAnd (sExists x203 S203 (sAnd (.evar x203) (sAnd (sTop S203) psi203))) ens203)) := by
  decide +kernel

theorem guard_r203 : sortGuard r203 ∈ ws203 := by decide +kernel
theorem top_free203 : S203.isFreeEvar topVar = false := by decide +kernel

theorem iff203 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (_F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws203 r203 prem203 S203 F203 (sAnd (sExists x203 S203 (sAnd (.evar x203) (sAnd (sTop S203) psi203))) ens203)) ↔ (I ⊧ᴵ (trS U.ax203).pat) := by
  rw [text_shape203]
  exact ExEnsTop.eqnPat_ensTop top_free203

/-- **W1**: Γ's item 1 is a consequence of sentence 203 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text203 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[1]? = some it →
    (TiePair.Texts [(trS U.ax203).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape203) fun F _ => iff203 H F).1

/-- **E**: Γ entails sentence 203, for every H. -/
theorem ex_entailed203 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax203).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape203) fun F _ => iff203 H F).2

theorem ex_entailed_c203 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax203).pat := by
  intro M _ I hIc
  exact ex_entailed203 H fun φ hφ => hIc φ (Or.inl hφ)

end Supersort

/-! ## e3-eq-exists-ml-and-terms -/

namespace AndTerms

kore_term kore from "f2-examples/e3-eq-exists-ml-and-terms.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-and-terms.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-and-terms.kompile.kore" module "E3-EQ-EXISTS-ML-AND-TERMS"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameBool (H : HookParams) : (cH H).sortName (Srt.bool) = "Bool" := (by decide +kernel : c.sortName (Srt.bool) = "Bool")
theorem ltBool (H : HookParams) : (Srt.bool : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.bool : Srt) < nRegSorts + c.sortNames.length)
theorem nameInt (H : HookParams) : (cH H).sortName (Srt.int) = "Int" := (by decide +kernel : c.sortName (Srt.int) = "Int")
theorem ltInt (H : HookParams) : (Srt.int : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.int : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 200: `f(X) => #Exists B:Bool. (B #And (notBool X))` (`memTerm_body`) -/

noncomputable def tbl200 : VarTable := tableOf U.ax200.ax.sortVars U.ax200.ax.pattern
noncomputable abbrev ctx200 : Ctx := ⟨tbl200, kore.aliasNames⟩
noncomputable def ws200 : List P := guardsOf U.ax200.ax
noncomputable def r200 : EVar := tbl200.ev (sortVarKey Rv)
noncomputable def prem200 : P := tr ctx200 (premK U.ax200.ax.pattern)
noncomputable def S200 : P := trSort tbl200 (srt "Bool")
noncomputable def F200 : P := tr ctx200 (lhsK U.ax200.ax.pattern)
noncomputable def ens200 : P := tr ctx200 (ensK U.ax200.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K200 : Kore.Pattern := rhsK U.ax200.ax.pattern
noncomputable def x200 : EVar := exVK tbl200 K200
noncomputable def t200 : P := tr ctx200 (argK 1 (exBK K200))

theorem text_shape200 : (trS U.ax200).pat = eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists x200 S200 (sAnd (.evar x200) t200)) ens200) := by
  decide +kernel

theorem gamma_shape200 : (TiePair.gammaPats c)[0]? = some (eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists x200 S200 (sAnd (.evar x200) (sAnd (sTop S200) (sIn S200 S200 (.evar x200) t200)))) ens200)) := by
  decide +kernel

theorem guard_r200 : sortGuard r200 ∈ ws200 := by decide +kernel

theorem iff200 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists x200 S200 (sAnd (.evar x200) (sAnd (sTop S200) (sIn S200 S200 (.evar x200) t200)))) ens200)) ↔ (I ⊧ᴵ (trS U.ax200).pat) := by
  rw [text_shape200]
  obtain ⟨σ, hS⟩ := sortAtN F (nameBool H) (ltBool H) tbl200
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r200 (guardsOf_pred F.defOK U.ax200.ax) fun e m hat a ha =>
    memTerm_body F.defOK F.ceilDef hS ha

/-- **W1**: Γ's item 0 is a consequence of sentence 200 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text200 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax200).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape200) fun F _ => iff200 H F).1

/-- **E**: Γ entails sentence 200, for every H. -/
theorem ex_entailed200 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax200).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape200) fun F _ => iff200 H F).2

theorem ex_entailed_c200 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax200).pat := by
  intro M _ I hIc
  exact ex_entailed200 H fun φ hφ => hIc φ (Or.inl hφ)

/-! ### Sentence 235: `k(X) => #Exists Z:Int. (Z #And (X +Int 1))` (`memTerm_body`) -/

noncomputable def tbl235 : VarTable := tableOf U.ax235.ax.sortVars U.ax235.ax.pattern
noncomputable abbrev ctx235 : Ctx := ⟨tbl235, kore.aliasNames⟩
noncomputable def ws235 : List P := guardsOf U.ax235.ax
noncomputable def r235 : EVar := tbl235.ev (sortVarKey Rv)
noncomputable def prem235 : P := tr ctx235 (premK U.ax235.ax.pattern)
noncomputable def S235 : P := trSort tbl235 (srt "Int")
noncomputable def F235 : P := tr ctx235 (lhsK U.ax235.ax.pattern)
noncomputable def ens235 : P := tr ctx235 (ensK U.ax235.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K235 : Kore.Pattern := rhsK U.ax235.ax.pattern
noncomputable def x235 : EVar := exVK tbl235 K235
noncomputable def t235 : P := tr ctx235 (argK 1 (exBK K235))

theorem text_shape235 : (trS U.ax235).pat = eqnPat ws235 r235 prem235 S235 F235 (sAnd (sExists x235 S235 (sAnd (.evar x235) t235)) ens235) := by
  decide +kernel

theorem gamma_shape235 : (TiePair.gammaPats c)[1]? = some (eqnPat ws235 r235 prem235 S235 F235 (sAnd (sExists x235 S235 (sAnd (.evar x235) (sAnd (sTop S235) (sIn S235 S235 (.evar x235) t235)))) ens235)) := by
  decide +kernel

theorem guard_r235 : sortGuard r235 ∈ ws235 := by decide +kernel

theorem iff235 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws235 r235 prem235 S235 F235 (sAnd (sExists x235 S235 (sAnd (.evar x235) (sAnd (sTop S235) (sIn S235 S235 (.evar x235) t235)))) ens235)) ↔ (I ⊧ᴵ (trS U.ax235).pat) := by
  rw [text_shape235]
  obtain ⟨σ, hS⟩ := sortAtN F (nameInt H) (ltInt H) tbl235
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r235 (guardsOf_pred F.defOK U.ax235.ax) fun e m hat a ha =>
    memTerm_body F.defOK F.ceilDef hS ha

/-- **W1**: Γ's item 1 is a consequence of sentence 235 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text235 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[1]? = some it →
    (TiePair.Texts [(trS U.ax235).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape235) fun F _ => iff235 H F).1

/-- **E**: Γ entails sentence 235, for every H. -/
theorem ex_entailed235 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax235).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape235) fun F _ => iff235 H F).2

theorem ex_entailed_c235 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax235).pat := by
  intro M _ I hIc
  exact ex_entailed235 H fun φ hφ => hIc φ (Or.inl hφ)

end AndTerms

/-! ## e3-eq-exists-ml-and-right -/

namespace AndRight

kore_term kore from "f2-examples/e3-eq-exists-ml-and-right.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-and-right.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-and-right.kompile.kore" module "E3-EQ-EXISTS-ML-AND-RIGHT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameBool (H : HookParams) : (cH H).sortName (Srt.bool) = "Bool" := (by decide +kernel : c.sortName (Srt.bool) = "Bool")
theorem ltBool (H : HookParams) : (Srt.bool : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.bool : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 131: `f(X) => (notBool X) #And (#Exists B:Bool. (B #And {B #Equals X}))` (`andRight_body`) -/

noncomputable def tbl131 : VarTable := tableOf U.ax131.ax.sortVars U.ax131.ax.pattern
noncomputable abbrev ctx131 : Ctx := ⟨tbl131, kore.aliasNames⟩
noncomputable def ws131 : List P := guardsOf U.ax131.ax
noncomputable def r131 : EVar := tbl131.ev (sortVarKey Rv)
noncomputable def prem131 : P := tr ctx131 (premK U.ax131.ax.pattern)
noncomputable def S131 : P := trSort tbl131 (srt "Bool")
noncomputable def F131 : P := tr ctx131 (lhsK U.ax131.ax.pattern)
noncomputable def ens131 : P := tr ctx131 (ensK U.ax131.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K131 : Kore.Pattern := rhsK U.ax131.ax.pattern
noncomputable def x131 : EVar := exVK tbl131 (argK 1 K131)
noncomputable def u131 : P := tr ctx131 (argK 0 K131)
noncomputable def psi131 : P := tr ctx131 (argK 1 (exBK (argK 1 K131)))

theorem text_shape131 : (trS U.ax131).pat = eqnPat ws131 r131 prem131 S131 F131 (sAnd (sAnd u131 (sExists x131 S131 (sAnd (.evar x131) psi131))) ens131) := by
  decide +kernel

theorem gamma_shape131 : (TiePair.gammaPats c)[0]? = some (eqnPat ws131 r131 prem131 S131 F131 (sAnd (sExists x131 S131 (sAnd (.evar x131) (sAnd (sTop S131) (sAnd psi131 (sIn S131 S131 (.evar x131) u131))))) ens131)) := by
  decide +kernel

theorem guard_r131 : sortGuard r131 ∈ ws131 := by decide +kernel
theorem u_free131 : u131.isFreeEvar x131 = false := by decide +kernel

theorem iff131 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws131 r131 prem131 S131 F131 (sAnd (sExists x131 S131 (sAnd (.evar x131) (sAnd (sTop S131) (sAnd psi131 (sIn S131 S131 (.evar x131) u131))))) ens131)) ↔ (I ⊧ᴵ (trS U.ax131).pat) := by
  rw [text_shape131]
  obtain ⟨σ, hS⟩ := sortAtN F (nameBool H) (ltBool H) tbl131
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r131 (guardsOf_pred F.defOK U.ax131.ax) fun e m hat a ha =>
    andRight_body F.defOK F.ceilDef hS u_free131 ha

/-- **W1**: Γ's item 0 is a consequence of sentence 131 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text131 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax131).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape131) fun F _ => iff131 H F).1

/-- **E**: Γ entails sentence 131, for every H. -/
theorem ex_entailed131 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax131).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape131) fun F _ => iff131 H F).2

theorem ex_entailed_c131 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax131).pat := by
  intro M _ I hIc
  exact ex_entailed131 H fun φ hφ => hIc φ (Or.inl hφ)

end AndRight

/-! ## e3-eq-exists-under-app-partial-ml -/

namespace UnderApp

kore_term kore from "f2-examples/e3-eq-exists-under-app-partial-ml.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-under-app-partial-ml.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-under-app-partial-ml.kompile.kore" module "E3-EQ-EXISTS-UNDER-APP-PARTIAL-ML"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameBool (H : HookParams) : (cH H).sortName (Srt.bool) = "Bool" := (by decide +kernel : c.sortName (Srt.bool) = "Bool")
theorem ltBool (H : HookParams) : (Srt.bool : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.bool : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 132: `f(X) => g(#Exists B:Bool. (B #And {B #Equals X}))` (`underApp_body`) -/

noncomputable def tbl132 : VarTable := tableOf U.ax132.ax.sortVars U.ax132.ax.pattern
noncomputable abbrev ctx132 : Ctx := ⟨tbl132, kore.aliasNames⟩
noncomputable def ws132 : List P := guardsOf U.ax132.ax
noncomputable def r132 : EVar := tbl132.ev (sortVarKey Rv)
noncomputable def prem132 : P := tr ctx132 (premK U.ax132.ax.pattern)
noncomputable def S132 : P := trSort tbl132 (srt "Bool")
noncomputable def F132 : P := tr ctx132 (lhsK U.ax132.ax.pattern)
noncomputable def ens132 : P := tr ctx132 (ensK U.ax132.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K132 : Kore.Pattern := rhsK U.ax132.ax.pattern
noncomputable def x132 : EVar := exVK tbl132 (argK 0 K132)
noncomputable def hd132 : P := sym (.symbol "Lblg")
noncomputable def pl132 : P := tr ctx132 (eqLK (argK 1 (exBK (argK 0 K132))))
noncomputable def pr132 : P := tr ctx132 (eqRK (argK 1 (exBK (argK 0 K132))))

theorem text_shape132 : (trS U.ax132).pat = eqnPat ws132 r132 prem132 S132 F132 (sAnd (hd132 ⬝ sExists x132 S132 (sAnd (.evar x132) (sEquals S132 S132 pl132 pr132))) ens132) := by
  decide +kernel

theorem gamma_shape132 : (TiePair.gammaPats c)[0]? = some (eqnPat ws132 r132 prem132 S132 F132 (sAnd (sExists x132 S132 (sAnd (hd132 ⬝ .evar x132) (sAnd (sTop S132) (sEquals S132 S132 pl132 pr132)))) ens132)) := by
  decide +kernel

theorem guard_r132 : sortGuard r132 ∈ ws132 := by decide +kernel
theorem hd_free132 : hd132.isFreeEvar x132 = false := by decide +kernel

theorem iff132 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws132 r132 prem132 S132 F132 (sAnd (sExists x132 S132 (sAnd (hd132 ⬝ .evar x132) (sAnd (sTop S132) (sEquals S132 S132 pl132 pr132)))) ens132)) ↔ (I ⊧ᴵ (trS U.ax132).pat) := by
  rw [text_shape132]
  obtain ⟨σ, hS⟩ := sortAtN F (nameBool H) (ltBool H) tbl132
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r132 (guardsOf_pred F.defOK U.ax132.ax) fun e m hat a ha =>
    underApp_body F.defOK hS hd_free132 (fun b _ => sEquals_predOn F.defOK F.ceilDef hS hS _) ha

/-- **W1**: Γ's item 0 is a consequence of sentence 132 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text132 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax132).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape132) fun F _ => iff132 H F).1

/-- **E**: Γ entails sentence 132, for every H. -/
theorem ex_entailed132 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax132).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape132) fun F _ => iff132 H F).2

theorem ex_entailed_c132 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax132).pat := by
  intro M _ I hIc
  exact ex_entailed132 H fun φ hφ => hIc φ (Or.inl hφ)

end UnderApp

/-! ## e3-eq-exists-ml-confined-fix -/

namespace ConfinedFix

kore_term kore from "f2-examples/e3-eq-exists-ml-confined-fix.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-confined-fix.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-confined-fix.kompile.kore" module "E3-EQ-EXISTS-ML-CONFINED-FIX"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameBool (H : HookParams) : (cH H).sortName (Srt.bool) = "Bool" := (by decide +kernel : c.sortName (Srt.bool) = "Bool")
theorem ltBool (H : HookParams) : (Srt.bool : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.bool : Srt) < nRegSorts + c.sortNames.length)
theorem nameInt (H : HookParams) : (cH H).sortName (Srt.int) = "Int" := (by decide +kernel : c.sortName (Srt.int) = "Int")
theorem ltInt (H : HookParams) : (Srt.int : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.int : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 202: `f(X) => #Exists B:Bool. #Exists Z:Int. (Z #And g(B) #And h(B) #And {B #Equals X})` (`twoBinders_body`) -/

noncomputable def tbl202 : VarTable := tableOf U.ax202.ax.sortVars U.ax202.ax.pattern
noncomputable abbrev ctx202 : Ctx := ⟨tbl202, kore.aliasNames⟩
noncomputable def ws202 : List P := guardsOf U.ax202.ax
noncomputable def r202 : EVar := tbl202.ev (sortVarKey Rv)
noncomputable def prem202 : P := tr ctx202 (premK U.ax202.ax.pattern)
noncomputable def S202 : P := trSort tbl202 (srt "Int")
noncomputable def F202 : P := tr ctx202 (lhsK U.ax202.ax.pattern)
noncomputable def ens202 : P := tr ctx202 (ensK U.ax202.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K202 : Kore.Pattern := rhsK U.ax202.ax.pattern
noncomputable def y202 : EVar := exVK tbl202 K202
noncomputable def z202 : EVar := exVK tbl202 (exBK K202)
noncomputable def sB202 : P := trSort tbl202 (srt "Bool")
noncomputable def t202 : P := tr ctx202 (argK 1 (argK 0 (argK 0 (exBK (exBK K202)))))
noncomputable def u202 : P := tr ctx202 (argK 1 (argK 0 (exBK (exBK K202))))
noncomputable def psi202 : P := tr ctx202 (argK 1 (exBK (exBK K202)))

theorem text_shape202 : (trS U.ax202).pat = eqnPat ws202 r202 prem202 S202 F202 (sAnd (sExists y202 sB202 (sExists z202 S202 (sAnd (sAnd (sAnd (.evar z202) t202) u202) psi202))) ens202) := by
  decide +kernel

theorem gamma_shape202 : (TiePair.gammaPats c)[0]? = some (eqnPat ws202 r202 prem202 S202 F202 (sAnd (sExists y202 sB202 (sExists z202 S202 (sAnd (.evar z202) (sAnd (sTop S202) (sAnd psi202 (sAnd (sIn S202 S202 (.evar z202) t202) (sIn S202 S202 (.evar z202) u202))))))) ens202)) := by
  decide +kernel

theorem guard_r202 : sortGuard r202 ∈ ws202 := by decide +kernel

theorem iff202 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws202 r202 prem202 S202 F202 (sAnd (sExists y202 sB202 (sExists z202 S202 (sAnd (.evar z202) (sAnd (sTop S202) (sAnd psi202 (sAnd (sIn S202 S202 (.evar z202) t202) (sIn S202 S202 (.evar z202) u202))))))) ens202)) ↔ (I ⊧ᴵ (trS U.ax202).pat) := by
  rw [text_shape202]
  obtain ⟨σ, hS⟩ := sortAtN F (nameInt H) (ltInt H) tbl202
  obtain ⟨τ, hB⟩ := sortAtN F (nameBool H) (ltBool H) tbl202
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r202 (guardsOf_pred F.defOK U.ax202.ax) fun e m hat a ha =>
    twoBinders_body F.defOK F.ceilDef hB hS ha

/-- **W1**: Γ's item 0 is a consequence of sentence 202 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text202 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax202).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape202) fun F _ => iff202 H F).1

/-- **E**: Γ entails sentence 202, for every H. -/
theorem ex_entailed202 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax202).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape202) fun F _ => iff202 H F).2

theorem ex_entailed_c202 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax202).pat := by
  intro M _ I hIc
  exact ex_entailed202 H fun φ hφ => hIc φ (Or.inl hφ)

end ConfinedFix

/-! ## e3-ml-eq-rhs-and-term -/

namespace AndTerm

kore_term kore from "f2-examples/e3-ml-eq-rhs-and-term.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-and-term.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-and-term.kompile.kore" module "E3-ML-EQ-RHS-AND-TERM"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameInt (H : HookParams) : (cH H).sortName (Srt.int) = "Int" := (by decide +kernel : c.sortName (Srt.int) = "Int")
theorem ltInt (H : HookParams) : (Srt.int : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.int : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 204: `h(X) => f(X) #And g(X)` (`cutAnd_body`) -/

noncomputable def tbl204 : VarTable := tableOf U.ax204.ax.sortVars U.ax204.ax.pattern
noncomputable abbrev ctx204 : Ctx := ⟨tbl204, kore.aliasNames⟩
noncomputable def ws204 : List P := guardsOf U.ax204.ax
noncomputable def r204 : EVar := tbl204.ev (sortVarKey Rv)
noncomputable def prem204 : P := tr ctx204 (premK U.ax204.ax.pattern)
noncomputable def S204 : P := trSort tbl204 (srt "Int")
noncomputable def F204 : P := tr ctx204 (lhsK U.ax204.ax.pattern)
noncomputable def ens204 : P := tr ctx204 (ensK U.ax204.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K204 : Kore.Pattern := rhsK U.ax204.ax.pattern
noncomputable def z204 : EVar := ⟨4⟩
noncomputable def t204 : P := tr ctx204 (argK 0 K204)
noncomputable def u204 : P := tr ctx204 (argK 1 K204)

theorem text_shape204 : (trS U.ax204).pat = eqnPat ws204 r204 prem204 S204 F204 (sAnd (sAnd t204 u204) ens204) := by
  decide +kernel

theorem gamma_shape204 : (TiePair.gammaPats c)[2]? = some (eqnPat ws204 r204 prem204 S204 F204 (sAnd (sExists z204 S204 (sAnd (.evar z204) (sAnd (sTop S204) (sAnd (sIn S204 S204 (.evar z204) t204) (sIn S204 S204 (.evar z204) u204))))) ens204)) := by
  decide +kernel

theorem guard_r204 : sortGuard r204 ∈ ws204 := by decide +kernel
theorem t_free204 : t204.isFreeEvar z204 = false := by decide +kernel
theorem u_free204 : u204.isFreeEvar z204 = false := by decide +kernel

theorem iff204 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws204 r204 prem204 S204 F204 (sAnd (sExists z204 S204 (sAnd (.evar z204) (sAnd (sTop S204) (sAnd (sIn S204 S204 (.evar z204) t204) (sIn S204 S204 (.evar z204) u204))))) ens204)) ↔ (I ⊧ᴵ (trS U.ax204).pat) := by
  rw [text_shape204]
  obtain ⟨σ, hS⟩ := sortAtN F (nameInt H) (ltInt H) tbl204
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r204 (guardsOf_pred F.defOK U.ax204.ax) fun e m hat a ha =>
    cutAnd_body F.defOK F.ceilDef hS t_free204 u_free204 ha

/-- **W1**: Γ's item 2 is a consequence of sentence 204 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text204 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[2]? = some it →
    (TiePair.Texts [(trS U.ax204).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape204) fun F _ => iff204 H F).1

/-- **E**: Γ entails sentence 204, for every H. -/
theorem ex_entailed204 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax204).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape204) fun F _ => iff204 H F).2

theorem ex_entailed_c204 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax204).pat := by
  intro M _ I hIc
  exact ex_entailed204 H fun φ hφ => hIc φ (Or.inl hφ)

end AndTerm

/-! ## e3-ml-eq-rhs-ceil-and -/

namespace CeilAnd

kore_term kore from "f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-ceil-and.kompile.kore" module "E3-ML-EQ-RHS-CEIL-AND"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameInt (H : HookParams) : (cH H).sortName (Srt.int) = "Int" := (by decide +kernel : c.sortName (Srt.int) = "Int")
theorem ltInt (H : HookParams) : (Srt.int : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.int : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 204: `h(X) => X #And #Ceil(f(X) #And g(X))` (`cutCeil_body`) -/

noncomputable def tbl204 : VarTable := tableOf U.ax204.ax.sortVars U.ax204.ax.pattern
noncomputable abbrev ctx204 : Ctx := ⟨tbl204, kore.aliasNames⟩
noncomputable def ws204 : List P := guardsOf U.ax204.ax
noncomputable def r204 : EVar := tbl204.ev (sortVarKey Rv)
noncomputable def prem204 : P := tr ctx204 (premK U.ax204.ax.pattern)
noncomputable def S204 : P := trSort tbl204 (srt "Int")
noncomputable def F204 : P := tr ctx204 (lhsK U.ax204.ax.pattern)
noncomputable def ens204 : P := tr ctx204 (ensK U.ax204.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K204 : Kore.Pattern := rhsK U.ax204.ax.pattern
noncomputable def z204 : EVar := ⟨4⟩
noncomputable def xX204 : EVar := tbl204.ev (evarKey (evar "VarX" (srt "Int")))
noncomputable def X204 : P := tr ctx204 (argK 0 K204)
noncomputable def t204 : P := tr ctx204 (argK 0 (ceilK (argK 1 K204)))
noncomputable def u204 : P := tr ctx204 (argK 1 (ceilK (argK 1 K204)))

theorem text_shape204 : (trS U.ax204).pat = eqnPat ws204 r204 prem204 S204 F204 (sAnd (sAnd X204 (sCeil S204 S204 (sAnd t204 u204))) ens204) := by
  decide +kernel

theorem gamma_shape204 : (TiePair.gammaPats c)[2]? = some (eqnPat ws204 r204 prem204 S204 F204 (sAnd (sExists z204 S204 (sAnd X204 (sAnd (sTop S204) (sAnd (sCeil S204 S204 (.evar z204)) (sAnd (sIn S204 S204 (.evar z204) t204) (sIn S204 S204 (.evar z204) u204)))))) ens204)) := by
  decide +kernel

theorem guard_r204 : sortGuard r204 ∈ ws204 := by decide +kernel
theorem X_free204 : X204.isFreeEvar z204 = false := by decide +kernel
theorem t_free204 : t204.isFreeEvar z204 = false := by decide +kernel
theorem u_free204 : u204.isFreeEvar z204 = false := by decide +kernel
theorem guard_x204 : (xX204 ∈∈ inhOf S204) ∈ ws204 := by decide +kernel

/-- Γ's table of the clause's variables, and the arity premise's readings (kernel), with any hook
parameters: f's application is the term t, of sort Int, at the sentence's variable. -/
def tblG204 : VarTable := [.sortVar "R", .evar "X0" (srt "Int"), .evar "VarV0" (srt "Int")]
theorem term_fun204 : (fun Hk : HookParams => tr ⟨tblG204, []⟩ (Term.kore (c.withHooks Hk)
    (Faithful.canonVars (c.withHooks Hk) [Srt.int]) (.app 384 [.var 0]))) = fun _ => t204 := by kernel_rfl
theorem sort_fun204 : (fun Hk : HookParams => sortOfTerm ((c.withHooks Hk).rhsCtx ((c.withHooks Hk).fns.map Fn.sig))
    [Srt.int] (.app 384 [.var 0])) = fun _ => some Srt.int := by kernel_rfl
theorem key_fun204 : (fun Hk : HookParams => tblG204.ev (Faithful.canonKey (c.withHooks Hk) [Srt.int] 0)) =
    fun _ => xX204 := by kernel_rfl

theorem iff204 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) (hTS : TieFRSig.TermsInSortNI (cH H) I) :
    (I ⊧ᴵ eqnPat ws204 r204 prem204 S204 F204 (sAnd (sExists z204 S204 (sAnd X204 (sAnd (sTop S204) (sAnd (sCeil S204 S204 (.evar z204)) (sAnd (sIn S204 S204 (.evar z204) t204) (sIn S204 S204 (.evar z204) u204)))))) ens204)) ↔ (I ⊧ᴵ (trS U.ax204).pat) := by
  rw [text_shape204]
  obtain ⟨σ, hS⟩ := sortAtN F (nameInt H) (ltInt H) tbl204
  refine eqnPat_of_body F.defOK F.ceilDef hS guard_r204 (guardsOf_pred F.defOK U.ax204.ax) fun e m hat a ha =>
    cutCeil_body F.defOK F.ceilDef hS X_free204 t_free204 u_free204 (fun b htb _ => ?_) ha
  have hx : Inh I σ (e.evalEvar xX204) := var_in F.defOK hS guard_x204 hat
  have hxS : Faithful.InS I "Int" (e.evalEvar xX204) :=
    (Faithful.inS_iff e).mp ((interp_inhOf_of (hS.den e)).mpr hx)
  have hk : tblG204.ev (Faithful.canonKey (cH H) [Srt.int] 0) = xX204 := congrFun key_fun204 H
  have ht : tr ⟨tblG204, []⟩ (Term.kore (cH H) (Faithful.canonVars (cH H) [Srt.int]) (.app 384 [.var 0])) = t204 :=
    congrFun term_fun204 H
  have h := @hTS [Srt.int] tblG204 e (.app 384 [.var 0]) Srt.int rfl (congrFun sort_fun204 H) (ltInt H)
    (fun i hi => by
      have hi0 : i = 0 := by simpa [varOccs, varOccsList] using hi
      subst hi0
      rw [hk]
      show Faithful.InS I ((cH H).sortName Srt.int) _
      rw [nameInt H]; exact hxS) b (by rw [ht]; exact htb)
  rw [nameInt H] at h
  exact (interp_inhOf_of (hS.den e)).mp ((Faithful.inS_iff e).mpr h)

/-- **W1**: Γ's item 2 is a consequence of sentence 204 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text204 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[2]? = some it →
    (TiePair.Texts [(trS U.ax204).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape204) fun F hTS => iff204 H F hTS).1

/-- **E**: Γ entails sentence 204, for every H. -/
theorem ex_entailed204 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax204).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape204) fun F hTS => iff204 H F hTS).2

theorem ex_entailed_c204 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax204).pat := by
  intro M _ I hIc
  exact ex_entailed204 H fun φ hφ => hIc φ (Or.inl hφ)

end CeilAnd

/-! ## e3-ml-eq-rhs-or -/

namespace RhsOr

kore_term kore from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"
definition_of defn from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"
user_axioms U from "f2-examples/e3-ml-eq-rhs-or.kompile.kore" module "E3-ML-EQ-RHS-OR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameInt (H : HookParams) : (cH H).sortName (Srt.int) = "Int" := (by decide +kernel : c.sortName (Srt.int) = "Int")
theorem ltInt (H : HookParams) : (Srt.int : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.int : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 204: `h(X) => f(X) #Or g(X)` (`cutOr_body`) -/

noncomputable def tbl204 : VarTable := tableOf U.ax204.ax.sortVars U.ax204.ax.pattern
noncomputable abbrev ctx204 : Ctx := ⟨tbl204, kore.aliasNames⟩
noncomputable def ws204 : List P := guardsOf U.ax204.ax
noncomputable def r204 : EVar := tbl204.ev (sortVarKey Rv)
noncomputable def prem204 : P := tr ctx204 (premK U.ax204.ax.pattern)
noncomputable def S204 : P := trSort tbl204 (srt "Int")
noncomputable def F204 : P := tr ctx204 (lhsK U.ax204.ax.pattern)
noncomputable def ens204 : P := tr ctx204 (ensK U.ax204.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K204 : Kore.Pattern := rhsK U.ax204.ax.pattern
noncomputable def z204 : EVar := ⟨4⟩
noncomputable def t204 : P := tr ctx204 (argK 0 K204)
noncomputable def u204 : P := tr ctx204 (argK 1 K204)

theorem text_shape204 : (trS U.ax204).pat = eqnPat ws204 r204 prem204 S204 F204 (sAnd (sOr S204 t204 u204) ens204) := by
  decide +kernel

theorem gamma_shape204 : (TiePair.gammaPats c)[2]? = some (eqnPat ws204 r204 prem204 S204 F204 (sAnd (sExists z204 S204 (sAnd (.evar z204) (sAnd (sTop S204) (sOr S204 (sIn S204 S204 (.evar z204) t204) (sIn S204 S204 (.evar z204) u204))))) ens204)) := by
  decide +kernel

theorem guard_r204 : sortGuard r204 ∈ ws204 := by decide +kernel
theorem t_free204 : t204.isFreeEvar z204 = false := by decide +kernel
theorem u_free204 : u204.isFreeEvar z204 = false := by decide +kernel

theorem iff204 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws204 r204 prem204 S204 F204 (sAnd (sExists z204 S204 (sAnd (.evar z204) (sAnd (sTop S204) (sOr S204 (sIn S204 S204 (.evar z204) t204) (sIn S204 S204 (.evar z204) u204))))) ens204)) ↔ (I ⊧ᴵ (trS U.ax204).pat) := by
  rw [text_shape204]
  obtain ⟨σ, hS⟩ := sortAtN F (nameInt H) (ltInt H) tbl204
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r204 (guardsOf_pred F.defOK U.ax204.ax) fun e m hat a ha =>
    cutOr_body F.defOK F.ceilDef hS t_free204 u_free204 ha

/-- **W1**: Γ's item 2 is a consequence of sentence 204 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text204 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[2]? = some it →
    (TiePair.Texts [(trS U.ax204).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape204) fun F _ => iff204 H F).1

/-- **E**: Γ entails sentence 204, for every H. -/
theorem ex_entailed204 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax204).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape204) fun F _ => iff204 H F).2

theorem ex_entailed_c204 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax204).pat := by
  intro M _ I hIc
  exact ex_entailed204 H fun φ hφ => hIc φ (Or.inl hφ)

end RhsOr

/-! ## e3-eq-exists-ml-in-or -/

namespace InOr

kore_term kore from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-in-or.kompile.kore" module "E3-EQ-EXISTS-ML-IN-OR"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameBool (H : HookParams) : (cH H).sortName (Srt.bool) = "Bool" := (by decide +kernel : c.sortName (Srt.bool) = "Bool")
theorem ltBool (H : HookParams) : (Srt.bool : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.bool : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 131: `f(X) => X #Or (#Exists B:Bool. (B #And {B #Equals notBool X}))` (`inOr_body`) -/

noncomputable def tbl131 : VarTable := tableOf U.ax131.ax.sortVars U.ax131.ax.pattern
noncomputable abbrev ctx131 : Ctx := ⟨tbl131, kore.aliasNames⟩
noncomputable def ws131 : List P := guardsOf U.ax131.ax
noncomputable def r131 : EVar := tbl131.ev (sortVarKey Rv)
noncomputable def prem131 : P := tr ctx131 (premK U.ax131.ax.pattern)
noncomputable def S131 : P := trSort tbl131 (srt "Bool")
noncomputable def F131 : P := tr ctx131 (lhsK U.ax131.ax.pattern)
noncomputable def ens131 : P := tr ctx131 (ensK U.ax131.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K131 : Kore.Pattern := rhsK U.ax131.ax.pattern
noncomputable def y131 : EVar := exVK tbl131 (argK 1 K131)
noncomputable def z131 : EVar := ⟨5⟩
noncomputable def X131 : P := tr ctx131 (argK 0 K131)
noncomputable def psi131 : P := tr ctx131 (argK 1 (exBK (argK 1 K131)))

theorem text_shape131 : (trS U.ax131).pat = eqnPat ws131 r131 prem131 S131 F131 (sAnd (sOr S131 X131 (sExists y131 S131 (sAnd (.evar y131) psi131))) ens131) := by
  decide +kernel

theorem gamma_shape131 : (TiePair.gammaPats c)[0]? = some (eqnPat ws131 r131 prem131 S131 F131 (sAnd (sExists y131 S131 (sExists z131 S131 (sAnd (.evar z131) (sAnd (sTop S131) (sOr S131 (sIn S131 S131 (.evar z131) X131) (sAnd (sIn S131 S131 (.evar z131) (.evar y131)) psi131)))))) ens131)) := by
  decide +kernel

theorem guard_r131 : sortGuard r131 ∈ ws131 := by decide +kernel
theorem Xy_free131 : X131.isFreeEvar y131 = false := by decide +kernel
theorem Xz_free131 : X131.isFreeEvar z131 = false := by decide +kernel
theorem psi_free131 : psi131.isFreeEvar z131 = false := by decide +kernel
theorem zy131 : z131 ≠ y131 := by decide +kernel

theorem iff131 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws131 r131 prem131 S131 F131 (sAnd (sExists y131 S131 (sExists z131 S131 (sAnd (.evar z131) (sAnd (sTop S131) (sOr S131 (sIn S131 S131 (.evar z131) X131) (sAnd (sIn S131 S131 (.evar z131) (.evar y131)) psi131)))))) ens131)) ↔ (I ⊧ᴵ (trS U.ax131).pat) := by
  rw [text_shape131]
  obtain ⟨σ, hS⟩ := sortAtN F (nameBool H) (ltBool H) tbl131
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r131 (guardsOf_pred F.defOK U.ax131.ax) fun e m hat a ha =>
    inOr_body F.defOK F.ceilDef hS Xy_free131 Xz_free131 psi_free131 zy131 ha

/-- **W1**: Γ's item 0 is a consequence of sentence 131 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text131 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax131).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape131) fun F _ => iff131 H F).1

/-- **E**: Γ entails sentence 131, for every H. -/
theorem ex_entailed131 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax131).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape131) fun F _ => iff131 H F).2

theorem ex_entailed_c131 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax131).pat := by
  intro M _ I hIc
  exact ex_entailed131 H fun φ hφ => hIc φ (Or.inl hφ)

/-! ### Sentence 132: `fx(X) => X #Or (#Exists B:Bool. (B #And {B #Equals X}))` (`inOr_body`) -/

noncomputable def tbl132 : VarTable := tableOf U.ax132.ax.sortVars U.ax132.ax.pattern
noncomputable abbrev ctx132 : Ctx := ⟨tbl132, kore.aliasNames⟩
noncomputable def ws132 : List P := guardsOf U.ax132.ax
noncomputable def r132 : EVar := tbl132.ev (sortVarKey Rv)
noncomputable def prem132 : P := tr ctx132 (premK U.ax132.ax.pattern)
noncomputable def S132 : P := trSort tbl132 (srt "Bool")
noncomputable def F132 : P := tr ctx132 (lhsK U.ax132.ax.pattern)
noncomputable def ens132 : P := tr ctx132 (ensK U.ax132.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K132 : Kore.Pattern := rhsK U.ax132.ax.pattern
noncomputable def y132 : EVar := exVK tbl132 (argK 1 K132)
noncomputable def z132 : EVar := ⟨5⟩
noncomputable def X132 : P := tr ctx132 (argK 0 K132)
noncomputable def psi132 : P := tr ctx132 (argK 1 (exBK (argK 1 K132)))

theorem text_shape132 : (trS U.ax132).pat = eqnPat ws132 r132 prem132 S132 F132 (sAnd (sOr S132 X132 (sExists y132 S132 (sAnd (.evar y132) psi132))) ens132) := by
  decide +kernel

theorem gamma_shape132 : (TiePair.gammaPats c)[1]? = some (eqnPat ws132 r132 prem132 S132 F132 (sAnd (sExists y132 S132 (sExists z132 S132 (sAnd (.evar z132) (sAnd (sTop S132) (sOr S132 (sIn S132 S132 (.evar z132) X132) (sAnd (sIn S132 S132 (.evar z132) (.evar y132)) psi132)))))) ens132)) := by
  decide +kernel

theorem guard_r132 : sortGuard r132 ∈ ws132 := by decide +kernel
theorem Xy_free132 : X132.isFreeEvar y132 = false := by decide +kernel
theorem Xz_free132 : X132.isFreeEvar z132 = false := by decide +kernel
theorem psi_free132 : psi132.isFreeEvar z132 = false := by decide +kernel
theorem zy132 : z132 ≠ y132 := by decide +kernel

theorem iff132 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws132 r132 prem132 S132 F132 (sAnd (sExists y132 S132 (sExists z132 S132 (sAnd (.evar z132) (sAnd (sTop S132) (sOr S132 (sIn S132 S132 (.evar z132) X132) (sAnd (sIn S132 S132 (.evar z132) (.evar y132)) psi132)))))) ens132)) ↔ (I ⊧ᴵ (trS U.ax132).pat) := by
  rw [text_shape132]
  obtain ⟨σ, hS⟩ := sortAtN F (nameBool H) (ltBool H) tbl132
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r132 (guardsOf_pred F.defOK U.ax132.ax) fun e m hat a ha =>
    inOr_body F.defOK F.ceilDef hS Xy_free132 Xz_free132 psi_free132 zy132 ha

/-- **W1**: Γ's item 1 is a consequence of sentence 132 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text132 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[1]? = some it →
    (TiePair.Texts [(trS U.ax132).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape132) fun F _ => iff132 H F).1

/-- **E**: Γ entails sentence 132, for every H. -/
theorem ex_entailed132 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax132).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape132) fun F _ => iff132 H F).2

theorem ex_entailed_c132 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax132).pat := by
  intro M _ I hIc
  exact ex_entailed132 H fun φ hφ => hIc φ (Or.inl hφ)

end InOr

/-! ## e3-eq-exists-ml-in-or-int -/

namespace InOrInt

kore_term kore from "f2-examples/e3-eq-exists-ml-in-or-int.kompile.kore"
definition_of defn from "f2-examples/e3-eq-exists-ml-in-or-int.kompile.kore"
user_axioms U from "f2-examples/e3-eq-exists-ml-in-or-int.kompile.kore" module "E3-EQ-EXISTS-ML-IN-OR-INT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

set_option maxHeartbeats 1000000 in
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK

theorem nameInt (H : HookParams) : (cH H).sortName (Srt.int) = "Int" := (by decide +kernel : c.sortName (Srt.int) = "Int")
theorem ltInt (H : HookParams) : (Srt.int : Srt) < nRegSorts + (cH H).sortNames.length :=
  (by decide +kernel : (Srt.int : Srt) < nRegSorts + c.sortNames.length)

/-! ### Sentence 200: `f(X) => X #Or (#Exists B:Int. (B #And {B #Equals X +Int 1}))` (`inOrEx_body, renamed_body`) -/

noncomputable def tbl200 : VarTable := tableOf U.ax200.ax.sortVars U.ax200.ax.pattern
noncomputable abbrev ctx200 : Ctx := ⟨tbl200, kore.aliasNames⟩
noncomputable def ws200 : List P := guardsOf U.ax200.ax
noncomputable def r200 : EVar := tbl200.ev (sortVarKey Rv)
noncomputable def prem200 : P := tr ctx200 (premK U.ax200.ax.pattern)
noncomputable def S200 : P := trSort tbl200 (srt "Int")
noncomputable def F200 : P := tr ctx200 (lhsK U.ax200.ax.pattern)
noncomputable def ens200 : P := tr ctx200 (ensK U.ax200.ax.pattern)
/-- The right side the text writes. -/
noncomputable def K200 : Kore.Pattern := rhsK U.ax200.ax.pattern
noncomputable def y200 : EVar := exVK tbl200 (argK 1 K200)
noncomputable def y2200 : EVar := ⟨5⟩
noncomputable def X200 : P := tr ctx200 (argK 0 K200)
noncomputable def psi200 : P := tr ctx200 (argK 1 (exBK (argK 1 K200)))

theorem text_shape200 : (trS U.ax200).pat = eqnPat ws200 r200 prem200 S200 F200 (sAnd (sOr S200 X200 (sExists y200 S200 (sAnd (.evar y200) psi200))) ens200) := by
  decide +kernel

theorem gamma_shape200 : (TiePair.gammaPats c)[0]? = some (eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists y200 S200 (sAnd (.evar y200) (sAnd (sTop S200) (sOr S200 (sIn S200 S200 (.evar y200) X200) (sExists y2200 S200 (sAnd (sIn S200 S200 (.evar y200) (.evar y2200)) (psi200.substEvar y200 (.evar y2200)))))))) ens200)) := by
  decide +kernel

theorem guard_r200 : sortGuard r200 ∈ ws200 := by decide +kernel
theorem X_free200 : X200.isFreeEvar y200 = false := by decide +kernel
theorem yy200 : y200 ≠ y2200 := by decide +kernel
theorem ren_ok200 : Faithful.renOK y200 y2200 psi200 = true := by decide +kernel
theorem y2_free200 : psi200.isFreeEvar y2200 = false := by decide +kernel

theorem iff200 (H : HookParams) {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (F : TieFRSig.SigFacts (cH H) I) :
    (I ⊧ᴵ eqnPat ws200 r200 prem200 S200 F200 (sAnd (sExists y200 S200 (sAnd (.evar y200) (sAnd (sTop S200) (sOr S200 (sIn S200 S200 (.evar y200) X200) (sExists y2200 S200 (sAnd (sIn S200 S200 (.evar y200) (.evar y2200)) (psi200.substEvar y200 (.evar y2200)))))))) ens200)) ↔ (I ⊧ᴵ (trS U.ax200).pat) := by
  rw [text_shape200]
  obtain ⟨σ, hS⟩ := sortAtN F (nameInt H) (ltInt H) tbl200
  exact eqnPat_of_body F.defOK F.ceilDef hS guard_r200 (guardsOf_pred F.defOK U.ax200.ax) fun e m hat a ha =>
    inOrEx_body F.defOK F.ceilDef hS X_free200 yy200
      (fun v w m => renamed_body ren_ok200 y2_free200 (Or.inr (Or.inl rfl)) e v w m) ha

/-- **W1**: Γ's item 0 is a consequence of sentence 200 with definedness and `ΓSig (cH H)`, for every H. -/
theorem ex_from_text200 (H : HookParams) : ∀ it, (Faithful.fnItems (cH H))[0]? = some it →
    (TiePair.Texts [(trS U.ax200).pat] ∪ Faithful.ΓSig (cH H)) ⊧ it.pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape200) fun F _ => iff200 H F).1

/-- **E**: Γ entails sentence 200, for every H. -/
theorem ex_entailed200 (H : HookParams) : Faithful.Γ (cH H) ⊧ (trS U.ax200).pat :=
  (tie_of_iff (coreOKH H) (by rw [TiePair.gammaPats_withHooks]; exact gamma_shape200) fun F _ => iff200 H F).2

theorem ex_entailed_c200 (H : HookParams) : Faithful.Γc (cH H) ⊧ (trS U.ax200).pat := by
  intro M _ I hIc
  exact ex_entailed200 H fun φ hφ => hIc φ (Or.inl hφ)

end InOrInt

end KCore.TieExClauseShapes

#check @KCore.TieExClauseShapes.Ctor.ex_from_text187
#print axioms KCore.TieExClauseShapes.Ctor.ex_from_text187
#check @KCore.TieExClauseShapes.Ctor.ex_entailed_c187
#print axioms KCore.TieExClauseShapes.Ctor.ex_entailed_c187
#check @KCore.TieExClauseShapes.Supersort.ex_from_text200
#print axioms KCore.TieExClauseShapes.Supersort.ex_from_text200
#check @KCore.TieExClauseShapes.Supersort.ex_entailed_c200
#print axioms KCore.TieExClauseShapes.Supersort.ex_entailed_c200
#check @KCore.TieExClauseShapes.Supersort.ex_from_text203
#print axioms KCore.TieExClauseShapes.Supersort.ex_from_text203
#check @KCore.TieExClauseShapes.Supersort.ex_entailed_c203
#print axioms KCore.TieExClauseShapes.Supersort.ex_entailed_c203
#check @KCore.TieExClauseShapes.AndTerms.ex_from_text200
#print axioms KCore.TieExClauseShapes.AndTerms.ex_from_text200
#check @KCore.TieExClauseShapes.AndTerms.ex_entailed_c200
#print axioms KCore.TieExClauseShapes.AndTerms.ex_entailed_c200
#check @KCore.TieExClauseShapes.AndTerms.ex_from_text235
#print axioms KCore.TieExClauseShapes.AndTerms.ex_from_text235
#check @KCore.TieExClauseShapes.AndTerms.ex_entailed_c235
#print axioms KCore.TieExClauseShapes.AndTerms.ex_entailed_c235
#check @KCore.TieExClauseShapes.AndRight.ex_from_text131
#print axioms KCore.TieExClauseShapes.AndRight.ex_from_text131
#check @KCore.TieExClauseShapes.AndRight.ex_entailed_c131
#print axioms KCore.TieExClauseShapes.AndRight.ex_entailed_c131
#check @KCore.TieExClauseShapes.UnderApp.ex_from_text132
#print axioms KCore.TieExClauseShapes.UnderApp.ex_from_text132
#check @KCore.TieExClauseShapes.UnderApp.ex_entailed_c132
#print axioms KCore.TieExClauseShapes.UnderApp.ex_entailed_c132
#check @KCore.TieExClauseShapes.ConfinedFix.ex_from_text202
#print axioms KCore.TieExClauseShapes.ConfinedFix.ex_from_text202
#check @KCore.TieExClauseShapes.ConfinedFix.ex_entailed_c202
#print axioms KCore.TieExClauseShapes.ConfinedFix.ex_entailed_c202
#check @KCore.TieExClauseShapes.AndTerm.ex_from_text204
#print axioms KCore.TieExClauseShapes.AndTerm.ex_from_text204
#check @KCore.TieExClauseShapes.AndTerm.ex_entailed_c204
#print axioms KCore.TieExClauseShapes.AndTerm.ex_entailed_c204
#check @KCore.TieExClauseShapes.CeilAnd.ex_from_text204
#print axioms KCore.TieExClauseShapes.CeilAnd.ex_from_text204
#check @KCore.TieExClauseShapes.CeilAnd.ex_entailed_c204
#print axioms KCore.TieExClauseShapes.CeilAnd.ex_entailed_c204
#check @KCore.TieExClauseShapes.RhsOr.ex_from_text204
#print axioms KCore.TieExClauseShapes.RhsOr.ex_from_text204
#check @KCore.TieExClauseShapes.RhsOr.ex_entailed_c204
#print axioms KCore.TieExClauseShapes.RhsOr.ex_entailed_c204
#check @KCore.TieExClauseShapes.InOr.ex_from_text131
#print axioms KCore.TieExClauseShapes.InOr.ex_from_text131
#check @KCore.TieExClauseShapes.InOr.ex_entailed_c131
#print axioms KCore.TieExClauseShapes.InOr.ex_entailed_c131
#check @KCore.TieExClauseShapes.InOr.ex_from_text132
#print axioms KCore.TieExClauseShapes.InOr.ex_from_text132
#check @KCore.TieExClauseShapes.InOr.ex_entailed_c132
#print axioms KCore.TieExClauseShapes.InOr.ex_entailed_c132
#check @KCore.TieExClauseShapes.InOrInt.ex_from_text200
#print axioms KCore.TieExClauseShapes.InOrInt.ex_from_text200
#check @KCore.TieExClauseShapes.InOrInt.ex_entailed_c200
#print axioms KCore.TieExClauseShapes.InOrInt.ex_entailed_c200
