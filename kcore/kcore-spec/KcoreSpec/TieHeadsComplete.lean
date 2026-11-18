/-
  Every head a premise of the theory applies is one of Γ's heads (`gammaHeads`), under `coreOK`.

  A premise of `Γc c ∪ Γstep c` is an AML pattern; `GHWalk.headsP` reads the heads it applies, each
  the name of a symbol with the sorts it is applied to, and `GHWalk.gammaHeadsP c` is `gammaHeads c`
  as the translation writes it.

  - **The functions and the rules** (`fnItems_inGH`, `ruleItems_inGH`): each item is the translation
    of an axiom whose KORE pattern applies Γ's heads only (`GHKore.prioEquation_coreOK`,
    `GHKore.prioRuleK_coreOK`), and the translation adds no head (`GHAml.trAxiom_inGH`).
  - **The step's closure** (`Γstep_inGH`): each disjunct is the translation of the two sides of a
    rule's axiom under existentials guarded by translated sorts (`closureDisjunct_inGH`).
  - **Every premise** (`gamma_heads_complete`): the seven parts of `Γ`, Bool's closure and the
    step's closure.
  - **A head and its translation** (`headP_mem_iff`): the translation of a head, at any variable
    table, is one of `gammaHeadsP c` exactly when the head is one of `gammaHeads c`; the sort
    arguments of Γ's heads are sort constants, and only a sort constant translates to one.
  - **A head Γ lacks is applied by no premise** (`gamma_lacks_head`): where `gammaHasHead c g` is
    false, no premise has the head `headP t g`, at any variable table `t`.
  - **The names** (`premise_symbol_names`): a symbol in a premise is named `inj` or as the head of
    one of Γ's symbols.
-/
import KcoreSpec.TieHeadsKore
import KcoreSpec.TieHeadsValues
import KcoreSpec.FaithfulComplete

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GHComplete

open KoreAML (P)
open GHWalk GHAml

variable {c : Semantics}

/-! ## The functions and the rules -/

/-- The items of sentences whose axioms apply Γ's heads only apply Γ's heads only. -/
theorem kernelItems_inGH {ss : List Kore.Sentence} (h : ∀ s ∈ ss, GHKore.SentHIn c s) :
    ∀ it ∈ kernelItems ss, InGH c it.pat := by
  intro it hit
  obtain ⟨s, hs, he⟩ := List.mem_filterMap.mp hit
  have hs' := h s hs
  split at he
  · rw [← Option.some.inj he]
    exact trAxiom_inGH [] [] _ fun g hg => hs' hg
  · cases he

/-- **The functions' equations apply Γ's heads only**, under `coreOK`. -/
theorem fnItems_inGH (h : c.coreOK = true) : ∀ it ∈ fnItems c, InGH c it.pat := by
  intro it hit
  obtain ⟨f, hf, hit⟩ := List.mem_flatMap.mp hit
  refine kernelItems_inGH (fun s hs => ?_) it hit
  obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hs
  exact GHKore.prioEquation_coreOK h hf hcl

/-- **The rules' axioms apply Γ's heads only**, under `coreOK`. -/
theorem ruleItems_inGH (h : c.coreOK = true) : ∀ it ∈ ruleItems c, InGH c it.pat := by
  intro it hit
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hit
  exact trAxiom_inGH [] [] _ fun g hg => GHKore.prioRuleK_coreOK h hr hg

/-! ## The step's closure -/

/-- Existentials over variables guarded by translated sorts add no head. -/
theorem sExists_foldr_inGH (tbl : KoreAML.VarTable) {body : P} (hb : InGH c body) :
    ∀ free : List (KoreAML.VarKey × Kore.KSort),
      InGH c (free.foldr (fun (k, s) φ => KoreAML.sExists (tbl.ev k) (KoreAML.trSort tbl s) φ) body)
  | [] => hb
  | (_, _) :: free => inGH_sExists _ (inGH_trSort _ _) (sExists_foldr_inGH tbl hb free)

/-- A closure disjunct of `\rewrites(L, R)` applies Γ's heads only where `L` and `R` do. -/
theorem closureDisjunct_inGH (off : Nat) (y : EVar) (S : Kore.KSort) {L R : Kore.Pattern}
    (hL : GHKore.HIn c L) (hR : GHKore.HIn c R) :
    InGH c (KoreAML.closureDisjunct [] off y (.rewrites S L R)).2 := by
  rw [closureDisjunct_rewrites]
  exact sExists_foldr_inGH _ (inGH_and (headsP_tr_gamma c _ _ fun g hg => hL hg)
    (inGH_member y (headsP_tr_gamma c _ _ fun g hg => hR hg))) _

/-- A rule's axiom is a `\rewrites`. -/
theorem prioRuleK_rewrites (c : Semantics) (r : Rule) : ∃ S L R, prioRuleK c r = .rewrites S L R := by
  unfold prioRuleK
  dsimp only
  split <;> exact ⟨_, _, _, rfl⟩

/-- **The step's closure applies Γ's heads only**, under `coreOK`. -/
theorem Γstep_inGH (h : c.coreOK = true) : ∀ φ, Γstep c φ → InGH c φ := by
  intro φ hφ
  have hφ' := Eq.trans hφ (Model.stepClosure_pat c)
  rw [hφ']
  dsimp only
  refine inGH_forall _ (inGH_included (inGH_sNext (inGH_evar _)) (inGH_disjList _ fun ψ hψ => ?_))
  rcases stepF_cases _ _ _ ψ hψ with hψ | ⟨p, hp, off, -, rfl⟩
  · exact absurd hψ List.not_mem_nil
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  obtain ⟨S, L, R, he⟩ := prioRuleK_rewrites c r
  have hin : GHKore.HIn c (prioRuleK c r) := GHKore.prioRuleK_coreOK h hr
  rw [he] at hin ⊢
  have hLR : GHKore.HIn c L ∧ GHKore.HIn c R := by
    simp only [GHKore.HIn, appHeadsOf, List.append_subset] at hin ⊢
    exact hin
  exact closureDisjunct_inGH off _ S hLR.1 hLR.2

/-! ## Every premise -/

/-- **Every head a premise of the theory applies is one of Γ's heads**, under `coreOK`: each head
of a premise of `Γc c ∪ Γstep c` (a symbol's name with the sorts it is applied to, `headsP`) is a
head of `gammaHeads c` as the translation writes it (`gammaHeadsP`). -/
theorem gamma_heads_complete (c : Semantics) (h : c.coreOK = true) :
    ∀ φ, (Γc c ∪ Γstep c) φ → ∀ g ∈ headsP φ, g ∈ gammaHeadsP c := by
  intro φ hφ
  show InGH c φ
  rcases hφ with hφ | hφ
  rotate_left
  · exact Γstep_inGH h φ hφ
  rcases hφ with hφ | hφ
  rotate_left
  · exact Γcl_inGH φ hφ
  rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
  · exact ΓSig_inGH φ hφ
  · exact ΓCons_inGH h φ hφ
  · exact GHVal.ΓDomains_inGH h φ hφ
  · exact ΓColls_inGH h φ hφ
  · exact itemsPremises_inGH (fnItems_inGH h) φ hφ
  · exact itemsPremises_inGH (ruleItems_inGH h) φ hφ
  · exact GHVal.ΓFallback_inGH h φ hφ

/-! ## A head and its translation -/

/-- A sort applied to arguments translates to an application. -/
theorem trSortApp_isApp (t : KoreAML.VarTable) : ∀ (ss : List Kore.KSort) (a b : P),
    ∃ a' b', KoreAML.trSortApp t (a ⬝ b) ss = a' ⬝ b'
  | [], a, b => ⟨a, b, by simp [KoreAML.trSortApp]⟩
  | s :: ss, a, b => by
    rw [KoreAML.trSortApp]
    exact trSortApp_isApp t ss _ _

/-- Only a sort constant translates to a sort symbol. -/
theorem trSort_eq_sortSym {t : KoreAML.VarTable} {s : Kore.KSort} {X : String}
    (h : KoreAML.trSort t s = KoreAML.sym (.sort ("Sort" ++ X))) : s = KoreAML.srt X := by
  cases s with
  | var α => simp [KoreAML.trSort, KoreAML.sym] at h
  | ctor C args =>
    cases args with
    | nil =>
      obtain ⟨⟨n⟩⟩ := C
      simp only [KoreAML.trSort, KoreAML.trSortApp, KoreAML.sym, Pattern.symbol.injEq,
        KoreAML.Sym.sort.injEq] at h
      subst h
      rfl
    | cons s ss =>
      rw [KoreAML.trSort, KoreAML.trSortApp] at h
      obtain ⟨a', b', he⟩ := trSortApp_isApp t ss (KoreAML.sym (.sort C.ident.name)) (KoreAML.trSort t s)
      rw [he] at h
      simp [KoreAML.sym] at h

/-- Sorts that translate as a list of sort constants are those constants. -/
theorem map_trSort_inj {t t' : KoreAML.VarTable} : ∀ {ss' ss : List Kore.KSort},
    (∀ s ∈ ss', ∃ X, s = KoreAML.srt X) → ss.map (KoreAML.trSort t) = ss'.map (KoreAML.trSort t') → ss = ss'
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | s' :: ss', s :: ss, hs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨X, rfl⟩ := hs s' (List.mem_cons_self ..)
    rw [trSort_srtG] at h
    rw [trSort_eq_sortSym h.1, map_trSort_inj (fun x hx => hs x (List.mem_cons_of_mem _ hx)) h.2]

/-- **The translation of a head is one of Γ's exactly when the head is**, at every variable
table: the sort arguments of Γ's heads are sort constants, and only a sort constant translates to
one. -/
theorem headP_mem_iff {t : KoreAML.VarTable} {g : String × List Kore.KSort} :
    headP t g ∈ gammaHeadsP c ↔ g ∈ gammaHeads c := by
  constructor
  · intro hm
    obtain ⟨g', hg', he⟩ := List.mem_map.mp hm
    have hgg : g = g' := by
      obtain ⟨n, ss⟩ := g
      obtain ⟨n', ss'⟩ := g'
      simp only [headP, Prod.mk.injEq] at he
      rw [he.1, map_trSort_inj (gammaHeads_sorts c _ hg') he.2.symm]
    exact hgg ▸ hg'
  · intro hg
    rw [headP_gamma hg]
    exact List.mem_map_of_mem hg

/-- **A head Γ lacks is applied by no premise of the theory**, under `coreOK`: where
`gammaHasHead c g` is false, no premise of `Γc c ∪ Γstep c` has the head `g` as the translation
writes it at any variable table. A sort argument of `g` that is a sort variable translates to an
element variable, which `headsP` reads as no sort argument: the statement says nothing of a
sentence's head read at a sort variable. -/
theorem gamma_lacks_head (c : Semantics) (h : c.coreOK = true) (g : String × List Kore.KSort)
    (hg : gammaHasHead c g = false) :
    ∀ φ, (Γc c ∪ Γstep c) φ → ∀ t : KoreAML.VarTable, headP t g ∉ headsP φ := by
  intro φ hφ t hm
  have h1 := headP_mem_iff.mp (gamma_heads_complete c h φ hφ _ hm)
  have h2 : gammaHasHead c g = true := List.any_eq_true.mpr ⟨g, h1, by simp⟩
  rw [hg] at h2
  cases h2

/-! ## The names -/

/-- Every symbol `.symbol n` of a pattern is the name of one of its heads. -/
theorem headsA_of_psyms {n : String} : ∀ (φ : P) (args : List P), KoreAML.Sym.symbol n ∈ psyms φ →
    ∃ ss, (n, ss) ∈ headsA args φ
  | .application a b, args, h => by
    simp only [psyms, List.mem_append] at h
    rw [headsA_app]
    rcases h with h | h
    · obtain ⟨ss, hs⟩ := headsA_of_psyms a (b :: args) h
      exact ⟨ss, List.mem_append_left _ hs⟩
    · obtain ⟨ss, hs⟩ := headsA_of_psyms b [] h
      exact ⟨ss, List.mem_append_right _ hs⟩
  | .implication a b, args, h => by
    simp only [psyms, List.mem_append] at h
    rw [headsA_imp]
    rcases h with h | h
    · obtain ⟨ss, hs⟩ := headsA_of_psyms a [] h
      exact ⟨ss, List.mem_append_left _ hs⟩
    · obtain ⟨ss, hs⟩ := headsA_of_psyms b [] h
      exact ⟨ss, List.mem_append_right _ hs⟩
  | .existential _ a, args, h => by
    simp only [psyms] at h
    simpa [headsA] using headsA_of_psyms a [] h
  | .mu _ a, args, h => by
    simp only [psyms] at h
    simpa [headsA] using headsA_of_psyms a [] h
  | .symbol σ, args, h => by
    simp only [psyms, List.mem_singleton] at h
    subst h
    exact ⟨args.takeWhile sortArgB, by simp [headsA]⟩
  | .evar _, _, h | .svar _, _, h | .bottom, _, h => by simp [psyms] at h

/-- **A symbol in a premise of the theory is named `inj` or as the head of one of Γ's symbols**,
under `coreOK`: the name of `gammaHead` at a symbol of `kernelSyms`, which is the symbol's name,
or `Lblite` for a symbol named as an instance of `ite`. -/
theorem premise_symbol_names (c : Semantics) (h : c.coreOK = true) :
    ∀ φ, (Γc c ∪ Γstep c) φ → ∀ n, KoreAML.Sym.symbol n ∈ psyms φ →
      n = "inj" ∨ ∃ k ∈ kernelSyms c, n = (gammaHead c k.name).1 := by
  intro φ hφ n hn
  obtain ⟨ss, hs⟩ := headsA_of_psyms φ [] hn
  obtain ⟨g, hg, he⟩ := List.mem_map.mp (gamma_heads_complete c h φ hφ _ hs)
  have hn' : n = g.1 := (congrArg Prod.fst he).symm
  simp only [gammaHeads, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨k, hk, rfl⟩ | ⟨⟨a, b⟩, -, rfl⟩
  · exact .inr ⟨k, hk, hn'⟩
  · exact .inl hn'

end GHComplete

end KCore
