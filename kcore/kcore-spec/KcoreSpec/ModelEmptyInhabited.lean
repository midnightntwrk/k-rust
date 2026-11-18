/-
  KCore. A second model of `Γc c ∪ Γstep c`, in which a sort E that has no value in c has one.

  `plus c E` is c with one more parameter symbol: an open generator (`raw`) of sort E with no
  argument, numbered after the definition's own symbols (`eSym`). Its application `e` is a value of
  sort E wherever the interpretation leaves it raw (`sortOf_e`), and where nothing else ends at E
  it is E's one value (`value_E_eq`). It is a parameter rather than a constructor because `idsOK`
  numbers the definition's own symbols constructors first, then functions, then parameters, then
  overloading symbols: a constructor numbered after the definition's symbols breaks that order
  wherever the definition has a function, a parameter only where it has an overloading symbol
  (`c.ovls = []` is asked). The added symbol is named `""`, the name `Semantics.symName` gives every
  number past the definition's names, so every symbol has the same name in both semantics
  (`symName_plus`) and every translation into matching logic that reads the semantics only
  through names gives the same pattern in both.

  `premises_sub` states that every premise of `Γc c ∪ Γstep c` is one of `Γc (plus c E) ∪ Γstep
  (plus c E)`. Signature, constructors, collections, functions, rules and the step's closure follow
  from the names and lookups being the same: c's symbols are symbols of `plus c E` with the same
  signatures, the sorts' generators are the same except E's, at which c has none (`c.gens E = []`),
  and every value of c is one of `plus c E` with the same sort (`sortOf_plus`). Two parts of `Γ`
  read the interpretation and evaluation, and are hypotheses:
  - the domains read `paramVal` and the silent points read `fallback`, whose answers are kept only
    where they have the symbol's result sort, which `plus c E` widens; the hypothesis is that both
    agree at c's points;
  - the fallback of a function holds at the points where every clause fails, and a clause whose
    condition ranges over a sort that gains a value may stop failing; the hypothesis is that at
    c's points where every clause of a function fails they fail in `plus c E` too, with the same
    rest.
  The closure axiom `boolClosed` is in `Γcl` where the definition reads a confined sort and Bool
  holds only its literals; both are asked of `plus c E` where c has them.

  A model of `Γc (plus c E) ∪ Γstep (plus c E)` is then one of `Γc c ∪ Γstep c` (`model_of_plus`;
  `model_exists` takes it from `sound_hyp` at `plus c E`), and in it E holds an element, `e`'s
  (`inhabited_of_plus`). Under `premises_sub`'s hypotheses such a model cannot exist for every c:
  where c's theory refutes that E has an element, `plus c E`'s has no model. The hypotheses where the interpretation gives no value
  and every function has a clause that fails nowhere: `fallback_plus_of_none`, `keepsRaw_of_none`,
  `hfails_of_noFail` (the sort predicates by `sortPreds_noFail`).
-/
import KcoreSpec.Sound

set_option autoImplicit false

namespace KCore

namespace EmptyInh

open ML Faithful

/-- The number of the added symbol: the next after the definition's own symbols. -/
def eSym (c : Semantics) : Sym := nRegSyms + c.symNames.length

/-- The added open generator: a constant of sort E, with no law. -/
def eParam (c : Semantics) (E : Srt) : ParamSig := { sig := ⟨eSym c, [], E⟩, raw := true }

/-- c with the open generator `eParam c E`, named `""`. -/
def plus (c : Semantics) (E : Srt) : Semantics :=
  { c with params := c.params ++ [eParam c E], symNames := c.symNames ++ [""] }

/-- The added constant as a value. -/
def eVal (c : Semantics) : GroundTerm := .ctor (eSym c) []

variable {c : Semantics} {E : Srt}

/-! ## Names -/

theorem getD_append_empty (l : List String) (i : Nat) : (l ++ [""]).getD i "" = l.getD i "" := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · rfl
  · rename_i h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)]
    cases h' : i - l.length with
    | zero => rfl
    | succ n => simp

/-- **Every symbol has the same name in both semantics.** -/
theorem symName_plus (f : Sym) : (plus c E).symName f = c.symName f := by
  unfold Semantics.symName
  split
  · rfl
  · exact getD_append_empty c.symNames _

theorem symName_plus_fun : (plus c E).symName = c.symName := funext symName_plus

/-! ## The translations read names only -/

mutual
  theorem termKore_plus (vs : List KoreAML.Var) : ∀ t : Term, Term.kore (plus c E) vs t = Term.kore c vs t
    | .var _ => rfl
    | .app f ts => by
      simp only [Term.kore, symName_plus, termKoreList_plus vs ts]
    | .inj a b t => by simp only [Term.kore, termKore_plus vs t]; rfl
    | .as t i => by simp only [Term.kore, termKore_plus vs t]
    | .dv _ _ => rfl
  theorem termKoreList_plus (vs : List KoreAML.Var) :
      ∀ ts : List Term, Term.koreList (plus c E) vs ts = Term.koreList c vs ts
    | [] => rfl
    | t :: ts => by simp only [Term.koreList, termKore_plus vs t, termKoreList_plus vs ts]
end

theorem termKore_plus_fun : Term.kore (plus c E) = Term.kore c :=
  funext fun vs => funext (termKore_plus vs)

theorem termKoreList_plus_fun : Term.koreList (plus c E) = Term.koreList c :=
  funext fun vs => funext (termKoreList_plus vs)

theorem condKore_plus : ∀ (vs : List KoreAML.Var) (S : Kore.KSort) (p : Cond),
    Cond.kore (plus c E) vs S p = Cond.kore c vs S p
  | _, _, .top => rfl
  | _, _, .bot => rfl
  | vs, S, .not p => by simp only [Cond.kore, condKore_plus vs S p]
  | vs, S, .and p q => by simp only [Cond.kore, condKore_plus vs S p, condKore_plus vs S q]
  | vs, S, .or p q => by simp only [Cond.kore, condKore_plus vs S p, condKore_plus vs S q]
  | vs, S, .implies p q => by simp only [Cond.kore, condKore_plus vs S p, condKore_plus vs S q]
  | vs, S, .ceil s t => by simp only [Cond.kore, termKore_plus_fun]; rfl
  | vs, S, .equals s t u => by simp only [Cond.kore, termKore_plus_fun]; rfl
  | vs, S, .mem s t u => by simp only [Cond.kore, termKore_plus_fun]; rfl
  | vs, S, .exMatch ys s p t body => by
    simp only [Cond.kore, termKore_plus_fun]
    rw [condKore_plus]; rfl
  | vs, S, .ex s body => by simp only [Cond.kore]; rw [condKore_plus]; rfl
  | vs, S, .all s body => by simp only [Cond.kore]; rw [condKore_plus]; rfl

theorem condKore_plus_fun : Cond.kore (plus c E) = Cond.kore c :=
  funext fun vs => funext fun S => funext (condKore_plus vs S)

mutual
  theorem gKore_plus : ∀ t : GroundTerm, GroundTerm.kore (plus c E) t = GroundTerm.kore c t
    | .ctor f ts => by simp only [GroundTerm.kore, symName_plus, gKoreList_plus ts]
    | .inj a b t => by simp only [GroundTerm.kore, gKore_plus t]; rfl
    | .dv _ _ => rfl
    | .map s es => by simp only [GroundTerm.kore]; exact gKoreEntries_plus _ es
    | .set s es => by simp only [GroundTerm.kore]; exact gKoreElems_plus _ es
    | .list s es => by simp only [GroundTerm.kore]; exact gKoreElems_plus _ es
  theorem gKoreList_plus : ∀ ts : List GroundTerm, GroundTerm.koreList (plus c E) ts = GroundTerm.koreList c ts
    | [] => rfl
    | t :: ts => by simp only [GroundTerm.koreList, gKore_plus t, gKoreList_plus ts]
  theorem gKoreEntries_plus (k : CollSig) : ∀ es : List (GroundTerm × GroundTerm),
      GroundTerm.koreEntries (plus c E) k es = GroundTerm.koreEntries c k es
    | [] => by simp only [GroundTerm.koreEntries, symName_plus]
    | [e] => by simp only [GroundTerm.koreEntries]; exact gKoreEntry_plus k e
    | e :: e' :: es => by
      simp only [GroundTerm.koreEntries, symName_plus, gKoreEntry_plus k e, gKoreEntries_plus k (e' :: es)]
  theorem gKoreEntry_plus (k : CollSig) : ∀ e : GroundTerm × GroundTerm,
      GroundTerm.koreEntry (plus c E) k e = GroundTerm.koreEntry c k e
    | (x, v) => by simp only [GroundTerm.koreEntry, symName_plus, gKore_plus x, gKore_plus v]
  theorem gKoreElems_plus (k : CollSig) : ∀ es : List GroundTerm,
      GroundTerm.koreElems (plus c E) k es = GroundTerm.koreElems c k es
    | [] => by simp only [GroundTerm.koreElems, symName_plus]
    | [e] => by simp only [GroundTerm.koreElems, symName_plus, gKore_plus e]
    | e :: e' :: es => by
      simp only [GroundTerm.koreElems, symName_plus, gKore_plus e, gKoreElems_plus k (e' :: es)]
end

theorem den_plus (v : GroundTerm) : den (plus c E) v = den c v := by
  unfold den; rw [gKore_plus]

theorem koreList_plus_fun : GroundTerm.koreList (plus c E) = GroundTerm.koreList c := funext gKoreList_plus

theorem symApp_plus (f : Sym) (args : List Kore.Pattern) : symApp (plus c E) f args = symApp c f args := by
  simp only [symApp, symName_plus]

theorem exclusion_plus (f : Fn) (cl : Clause) (cp : ClausePres) :
    exclusion (plus c E) f cl cp = exclusion c f cl cp := by
  simp only [exclusion, withPre, termKore_plus_fun, termKoreList_plus_fun, condKore_plus_fun]
  rfl

theorem prioEquation_plus (f : Fn) (cl : Clause) : prioEquation (plus c E) f cl = prioEquation c f cl := by
  unfold prioEquation clauseEquation competingEquation
  simp only [exclusion_plus, eqnSentence, symApp_plus, withPre, clauseRhs, Cond.conj, termKore_plus_fun,
    termKoreList_plus_fun, condKore_plus_fun, symName_plus]
  rfl

theorem fnItems_plus : fnItems (plus c E) = fnItems c := by
  have h : prioEquation (plus c E) = prioEquation c := funext fun f => funext (prioEquation_plus f)
  simp only [fnItems, fnEquationsK, h]
  rfl

theorem prioRuleK_plus (r : Rule) : prioRuleK (plus c E) r = prioRuleK c r := by
  simp only [prioRuleK, applies, ruleRight, Cond.conj, termKore_plus_fun, condKore_plus_fun]
  rfl

theorem prioRuleK_plus_fun : prioRuleK (plus c E) = prioRuleK c := funext prioRuleK_plus

theorem ruleItems_plus : ruleItems (plus c E) = ruleItems c := by
  simp only [ruleItems, prioRuleK_plus_fun]
  rfl

theorem stepClosureItem_plus : stepClosureItem (plus c E) = stepClosureItem c := by
  simp only [stepClosureItem, prioRuleK_plus_fun]
  rfl

theorem collAxioms_plus (k : CollSig) : collAxioms (plus c E) k = collAxioms c k := by
  simp only [collAxioms, mapCollAxioms, setCollAxioms, listCollAxioms, mapUnitSplitAx, mapElemNotUnitAx,
    mapElemAtomAx, mapDecompAx, listUnitSplitAx, listElemNotUnitAx, listElemAtomAx, listElemAtomBackAx,
    listDecompAx, setUnitSplitAx, setElemNotUnitAx, setElemAtomAx, setDecompAx, collU, collE, collC,
    collI, inSort, symName_plus]
  rfl

theorem collNoJunk_plus (k : CollSig) : collNoJunk (plus c E) k = collNoJunk c k := by
  simp only [collNoJunk, symName_plus]
  rfl

theorem boolClosed_plus : boolClosed (plus c E) = boolClosed c := by
  simp only [boolClosed, den_plus]
  rfl

theorem toK_plus (k : CtorSig) : toK (plus c E) k = toK c k := by
  simp only [toK, symName_plus]
  rfl

theorem genToK_plus (g : Gen) : Gen.toK (plus c E) g = Gen.toK c g := by
  cases g <;> simp only [Gen.toK, toK_plus] <;> rfl

theorem symArityItem_plus (k : CtorSig) : symArityItem (plus c E) k = symArityItem c k := by
  simp only [symArityItem, symName_plus]
  rfl

/-! ## Every value of c is one of `plus c E`, of the same sort -/

theorem plus_ctorSigs : (plus c E).ctorSigs = c.ctorSigs := rfl
theorem plus_lookupOvl : (plus c E).lookupOvl = c.lookupOvl := rfl
theorem plus_uncovered : (plus c E).uncovered = c.uncovered := rfl
theorem plus_keepsRaw : (plus c E).keepsRaw = c.keepsRaw := rfl
theorem plus_subsorts : (plus c E).subsorts = c.subsorts := rfl
theorem plus_lib : (plus c E).lib = c.lib := rfl
theorem plus_collOf : (plus c E).collOf = c.collOf := rfl

theorem lookupOpen_plus {f : Sym} {k : ParamSig} (h : c.lookupOpen f = some k) :
    (plus c E).lookupOpen f = some k := by
  unfold Semantics.lookupOpen at h ⊢
  split at h
  · rename_i hf
    simp only [hf, ↓reduceIte]
    show (c.params ++ [eParam c E]).find? _ = some k
    rw [List.find?_append, h]; rfl
  · cases h

mutual
  theorem sortOf_plus : ∀ {v : GroundTerm} {s : Srt}, c.sortOf v = some s → (plus c E).sortOf v = some s
    | .ctor f ts, s, h => by
      simp only [Semantics.sortOf, plus_ctorSigs, plus_lookupOvl, plus_uncovered, plus_keepsRaw] at h ⊢
      cases hk : lookupSig c.ctorSigs f with
      | some k =>
        rw [hk] at h
        simp only at h ⊢
        cases hs : c.sortsOf ts with
        | none => rw [hs] at h; simp at h
        | some ss => rw [hs] at h; rw [sortsOf_plus hs]; exact h
      | none =>
        rw [hk] at h
        simp only at h ⊢
        cases ho : c.lookupOvl f with
        | some o =>
          rw [ho] at h
          simp only at h ⊢
          cases hs : c.sortsOf ts with
          | none => rw [hs] at h; simp at h
          | some ss => rw [hs] at h; rw [sortsOf_plus hs]; exact h
        | none =>
          rw [ho] at h
          simp only at h ⊢
          cases hp : c.lookupOpen f with
          | none => rw [hp] at h; cases h
          | some k =>
            rw [hp] at h
            rw [lookupOpen_plus hp]
            simp only at h ⊢
            cases hs : c.sortsOf ts with
            | none => rw [hs] at h; simp at h
            | some ss => rw [hs] at h; rw [sortsOf_plus hs]; exact h
    | .inj a b t, s, h => by
      simp only [Semantics.sortOf, plus_subsorts] at h ⊢
      cases ht : c.sortOf t with
      | none => rw [ht] at h; simp at h
      | some s' => rw [ht] at h; rw [sortOf_plus ht]; exact h
    | .dv _ _, _, h => h
    | .map s es, s', h => by
      simp only [Semantics.sortOf, plus_collOf] at h ⊢
      cases hk : c.collOf s with
      | none => rw [hk] at h; cases h
      | some k =>
        rw [hk] at h
        simp only at h ⊢
        cases hv : k.val with
        | none => rw [hv] at h; cases h
        | some vs =>
          rw [hv] at h
          simp only at h ⊢
          cases he : c.entriesOK k.key vs es with
          | false => rw [he] at h; simp at h
          | true => rw [he] at h; rw [entriesOK_plus he]; exact h
    | .set s es, s', h => by
      simp only [Semantics.sortOf, plus_collOf] at h ⊢
      cases hs : c.sortsOf es with
      | none => rw [hs] at h; split at h <;> simp_all
      | some ss => rw [hs] at h; rw [sortsOf_plus hs]; exact h
    | .list s es, s', h => by
      simp only [Semantics.sortOf, plus_collOf] at h ⊢
      cases hs : c.sortsOf es with
      | none => rw [hs] at h; split at h <;> simp_all
      | some ss => rw [hs] at h; rw [sortsOf_plus hs]; exact h
  theorem sortsOf_plus : ∀ {vs : List GroundTerm} {ss : List Srt}, c.sortsOf vs = some ss →
      (plus c E).sortsOf vs = some ss
    | [], _, h => h
    | t :: ts, ss, h => by
      simp only [Semantics.sortsOf] at h ⊢
      cases ht : c.sortOf t with
      | none => rw [ht] at h; cases h
      | some s =>
        cases hts : c.sortsOf ts with
        | none => rw [ht, hts] at h; cases h
        | some ss' => rw [ht, hts] at h; rw [sortOf_plus ht, sortsOf_plus hts]; exact h
  theorem entriesOK_plus {ks vs : Srt} : ∀ {es : List (GroundTerm × GroundTerm)},
      c.entriesOK ks vs es = true → (plus c E).entriesOK ks vs es = true
    | [], _ => rfl
    | e :: es, h => by
      simp only [Semantics.entriesOK, Bool.and_eq_true] at h ⊢
      exact ⟨entryOK_plus h.1, entriesOK_plus h.2⟩
  theorem entryOK_plus {ks vs : Srt} : ∀ {e : GroundTerm × GroundTerm},
      c.entryOK ks vs e = true → (plus c E).entryOK ks vs e = true
    | (k, v), h => by
      simp only [Semantics.entryOK, Bool.and_eq_true, beq_iff_eq] at h ⊢
      exact ⟨sortOf_plus h.1, sortOf_plus h.2⟩
end

/-! ## The constructors -/

theorem plus_ovls : (plus c E).ovls = c.ovls := rfl

theorem lookupOpen_plus_ne {f : Sym} (hf : f ≠ eSym c) : (plus c E).lookupOpen f = c.lookupOpen f := by
  unfold Semantics.lookupOpen
  split
  · show (c.params ++ [eParam c E]).find? _ = _
    rw [List.find?_append]
    cases c.params.find? (fun k => k.raw && k.sig.name == f) with
    | some k => rfl
    | none =>
      have : (eSym c == f) = false := beq_false_of_ne (Ne.symm hf)
      simp only [Option.none_or, List.find?_cons, List.find?_nil, eParam, Bool.true_and, this]
  · rfl

theorem isOvl_noOvl (c : Semantics) (hovl : c.ovls = []) (f : Sym) : c.isOvl f = false := by
  simp [Semantics.isOvl, Semantics.lookupOvl, hovl]

theorem fnOvl_plus (hovl : c.ovls = []) : (plus c E).fnOvl = c.fnOvl := by
  funext g
  cases g <;> simp [Semantics.fnOvl, isOvl_noOvl _ hovl, isOvl_noOvl (plus c E) hovl]

theorem distGuarded_plus (hovl : c.ovls = []) : (plus c E).distGuarded = c.distGuarded := by
  funext g g'
  cases g <;> cases g' <;>
    simp [Semantics.distGuarded, Semantics.fnOvl, isOvl_noOvl _ hovl, isOvl_noOvl (plus c E) hovl]

theorem isOvl_plus (hovl : c.ovls = []) : (plus c E).isOvl = c.isOvl := by
  funext f; rw [isOvl_noOvl _ hovl, isOvl_noOvl (plus c E) hovl]

/-- The sorts other than E have the same generators. -/
theorem gens_plus {N : Srt} (hN : N ≠ E) : (plus c E).gens N = c.gens N := by
  simp only [Semantics.gens, plus_ctorSigs, plus_subsorts]
  show _ ++ _ ++ ((((c.params ++ [eParam c E]).filter (·.raw)).map (·.sig)).filter (·.result == N)).map Gen.ctor ++ _ = _
  simp [List.filter_append, eParam, Ne.symm hN]
  rfl

/-- c's generators are open in `plus c E` exactly where they are in c, where no constructor of c is
numbered `eSym c`. -/
theorem isOpenGen_plus (hfresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c) (hovl : c.ovls = []) {N : Srt} :
    ∀ g ∈ c.gens N, (plus c E).isOpenGen g = c.isOpenGen g := by
  intro g hg
  cases g with
  | inj a => rfl
  | ctor k =>
    simp only [Semantics.isOpenGen]
    by_cases hk : k.name = eSym c
    · -- a raw parameter of c numbered `eSym c`: c's lookup finds it already
      simp only [Semantics.gens, List.mem_append, List.mem_map, List.mem_filter] at hg
      rcases hg with ((⟨k', ⟨hk', -⟩, he⟩ | ⟨k', ⟨hk', -⟩, he⟩) | ⟨k', ⟨hk', -⟩, he⟩) | ⟨_, -, he⟩
      · cases he; exact absurd hk (hfresh k hk')
      · simp [Semantics.ovlSigs, hovl] at hk'
      · cases he
        obtain ⟨p, ⟨hp, hraw⟩, rfl⟩ := hk'
        have hsome : (c.lookupOpen p.sig.name).isSome = true := by
          unfold Semantics.lookupOpen
          simp only [show nRegSyms ≤ p.sig.name by rw [hk]; exact Nat.le_add_right _ _, ↓reduceIte]
          exact List.find?_isSome.mpr ⟨p, hp, by simp [hraw]⟩
        obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hsome
        rw [lookupOpen_plus hk0, hk0]
      · cases he
    · rw [lookupOpen_plus_ne hk]

theorem genToK_plus_fun : Gen.toK (plus c E) = Gen.toK c := funext genToK_plus

theorem assocAxK_plus (k : ParamSig) : assocAxK (plus c E) k = assocAxK c k := by
  simp only [assocAxK, symName_plus]; rfl

theorem idemAxK_plus (k : ParamSig) : idemAxK (plus c E) k = idemAxK c k := by
  simp only [idemAxK, symName_plus]; rfl

/-- The added generator has no law. -/
theorem lawItemsK_plus : lawItemsK (plus c E) = lawItemsK c := by
  simp only [lawItemsK, assocAxK_plus, idemAxK_plus]
  show (c.params ++ [eParam c E]).flatMap _ = _
  rw [List.flatMap_append]
  simp [eParam]

/-- **c's constructor items are items of `plus c E`**, where E has no generator in c. -/
theorem consItemsK_sub (hovl : c.ovls = []) (hfresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c)
    (hE : c.gens E = []) : ∀ it ∈ consItemsK c, it ∈ consItemsK (plus c E) := by
  intro it h
  unfold consItemsK at h ⊢
  simp only [fnOvl_plus hovl, distGuarded_plus hovl, isOvl_plus hovl, genToK_plus_fun, toK_plus,
    lawItemsK_plus] 
  simp only [List.mem_append, List.mem_flatMap] at h ⊢
  rcases h with ((⟨N, hN, h⟩ | h) | h) | h
  · refine Or.inl (Or.inl (Or.inl ⟨N, hN, ?_⟩))
    by_cases hNE : N = E
    · subst hNE; simp [hE, pairs] at h
    · have hfil : (c.gens N).filter (fun g => !(plus c E).isOpenGen g) = (c.gens N).filter (fun g => !c.isOpenGen g) :=
        List.filter_congr (fun g hg => by rw [isOpenGen_plus hfresh hovl g hg])
      rw [gens_plus hNE, hfil]
      exact h
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-! ## The premises -/

theorem itemsPremises_mono {l l' : List KoreAML.Item} (h : ∀ it ∈ l, it ∈ l') {φ : KoreAML.P}
    (hφ : KoreAML.itemsPremises l φ) : KoreAML.itemsPremises l' φ := by
  rcases hφ with ⟨it, hit, rfl⟩ | hd
  · exact .inl ⟨it, h it hit, rfl⟩
  · exact .inr hd

theorem sigItems_sub : ∀ it ∈ sigItems c, it ∈ sigItems (plus c E) := by
  intro it h
  simp only [sigItems, List.mem_append, List.mem_map] at h ⊢
  rcases h with ((h | ⟨s, hs, rfl⟩) | ⟨k, hk, rfl⟩) | h
  · exact .inl (.inl (.inl h))
  · exact .inl (.inl (.inr ⟨s, hs, rfl⟩))
  · refine .inl (.inr ⟨k, ?_, symArityItem_plus k⟩)
    simp only [kernelSyms, List.mem_append, List.mem_map] at hk ⊢
    rcases hk with (((hk | hk) | ⟨p, hp, rfl⟩) | hk) | hk
    · exact .inl (.inl (.inl (.inl hk)))
    · exact .inl (.inl (.inl (.inr hk)))
    · exact .inl (.inl (.inr ⟨p, List.mem_append_left _ hp, rfl⟩))
    · exact .inl (.inr hk)
    · exact .inr hk
  · exact .inr h

/-- **Every premise of `Γc c ∪ Γstep c` is one of `Γc (plus c E) ∪ Γstep (plus c E)`**, where c has
no overloading symbol and no constructor numbered `eSym c`, E has no generator in c, the domains'
parameter values and fallbacks agree at c's points, where every clause of a function fails at c's
point it fails in `plus c E` with the same rest, and `plus c E` reads a confined sort and holds only
Bool's literals in Bool where c does. -/
theorem premises_sub (hovl : c.ovls = []) (hfresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c)
    (hE : c.gens E = [])
    (hpv : ∀ k ∈ c.params, ∀ vs, c.sortsOf vs = some k.sig.args →
      (plus c E).paramVal k.sig.name vs = c.paramVal k.sig.name vs)
    (hfb : ∀ k ∈ hookSigs, ∀ vs, c.sortsOf vs = some k.args → hook k.name vs = some none →
      silent k.name vs = true → (plus c E).fallback k.name vs = c.fallback k.name vs)
    (hfails : ∀ fn ∈ c.allFns, ∀ vs, c.sortsOf vs = some fn.args → (∀ cl ∈ fn.clauses, Fails c vs cl) →
      (∀ cl ∈ fn.clauses, Fails (plus c E) vs cl) ∧ (plus c E).fnRest fn vs = c.fnRest fn vs)
    (hrc : c.readsConfined = true → (plus c E).readsConfined = true)
    (hlit : c.litSort Srt.bool = true → (plus c E).litSort Srt.bool = true) :
    ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc (plus c E) ∪ Γstep (plus c E) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · refine .inl (.inl ?_)
    rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · -- the signature
      refine .inl (.inl (.inl (.inl (.inl (.inl ?_)))))
      rcases hφ with hφ | hφ
      · exact .inl (itemsPremises_mono sigItems_sub hφ)
      · exact .inr hφ
    · -- the constructors
      exact .inl (.inl (.inl (.inl (.inl (.inr (itemsPremises_mono (consItemsK_sub hovl hfresh hE) hφ))))))
    · -- the domains
      refine .inl (.inl (.inl (.inl (.inr ?_))))
      rcases hφ with ⟨k, vs, r, hk, hvs, hh, hs, rfl⟩ | ⟨k, vs, hk, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ |
          ⟨v, w, s, hd, hv, hw, hne, rfl⟩ | ⟨k, hk, rfl⟩
      · refine .inl ⟨k, vs, r, hk, sortsOf_plus hvs, hh, hs, ?_⟩
        simp only [symApp_plus, koreList_plus_fun, den_plus]
      · refine .inr (.inl ⟨k, vs, List.mem_append_left _ hk, sortsOf_plus hvs, ?_⟩)
        simp only [symApp_plus, koreList_plus_fun, den_plus, hpv k hk vs hvs]
      · refine .inr (.inr (.inl ⟨v, s, sortOf_plus hv, ?_⟩))
        simp only [den_plus]; rfl
      · refine .inr (.inr (.inr (.inl ⟨v, w, s, hd, sortOf_plus hv, sortOf_plus hw, hne, ?_⟩)))
        simp only [den_plus]
      · exact .inr (.inr (.inr (.inr ⟨k, hk, (collNoJunk_plus k).symm⟩)))
    · -- the collections
      obtain ⟨k, hk, hφ⟩ := hφ
      exact .inl (.inl (.inl (.inr ⟨k, hk, by rw [collAxioms_plus]; exact hφ⟩)))
    · -- the functions
      exact .inl (.inl (.inr (by unfold ΓFns; rw [fnItems_plus]; exact hφ)))
    · -- the rules
      exact .inl (.inr (by unfold ΓRules; rw [ruleItems_plus]; exact hφ))
    · -- the fallback
      refine .inr ?_
      rcases hφ with ⟨k, vs, hk, hvs, hh, hs, rfl⟩ | ⟨fn, vs, hfn, hvs, hf, rfl⟩
      · refine .inl ⟨k, vs, hk, sortsOf_plus hvs, hh, hs, ?_⟩
        simp only [symApp_plus, koreList_plus_fun, den_plus, hfb k hk vs hvs hh hs]
      · obtain ⟨hf', hrest⟩ := hfails fn hfn vs hvs hf
        refine .inr ⟨fn, vs, hfn, sortsOf_plus hvs, hf', ?_⟩
        simp only [symApp_plus, koreList_plus_fun, den_plus, hrest]
  · obtain ⟨hr, hl, rfl⟩ := hφ
    exact .inl (.inr ⟨hrc hr, hlit hl, boolClosed_plus.symm⟩)
  · refine .inr ?_
    show φ = (stepClosureItem (plus c E)).pat
    rw [stepClosureItem_plus]; exact hφ

/-- **A model of `plus c E`'s theory is one of c's.** -/
theorem model_of_plus
    (hsub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc (plus c E) ∪ Γstep (plus c E))
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP (Γc (plus c E) ∪ Γstep (plus c E))) : I ⊧ᴵP (Γc c ∪ Γstep c) :=
  fun φ hφ => hI φ (hsub φ hφ)

/-! ## E holds an element -/

/-- **The added constant is a value of sort E** where c has no constructor, overloading symbol or
parameter numbered `eSym c` and the interpretation leaves it raw. -/
theorem sortOf_e (hovl : c.ovls = []) (hfresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c)
    (hfp : ∀ k ∈ c.params, k.sig.name ≠ eSym c) (hraw : c.keepsRaw (eSym c) [] = true) :
    (plus c E).sortOf (eVal c) = some E := by
  have hk : lookupSig c.ctorSigs (eSym c) = none := by
    rw [lookupSig_eq, List.find?_eq_none]
    intro k hk; simpa using hfresh k hk
  have ho : c.lookupOvl (eSym c) = none := by simp [Semantics.lookupOvl, hovl]
  have hp : (plus c E).lookupOpen (eSym c) = some (eParam c E) := by
    unfold Semantics.lookupOpen
    simp only [show nRegSyms ≤ eSym c from Nat.le_add_right _ _, ↓reduceIte]
    show (c.params ++ [eParam c E]).find? _ = _
    rw [List.find?_append, List.find?_eq_none.mpr (fun k hk => by simp [hfp k hk])]
    simp [eParam]
  simp only [eVal, Semantics.sortOf, plus_ctorSigs, plus_lookupOvl, hk, ho, hp, plus_keepsRaw, hraw]
  rfl

/-- **In a model of `plus c E`'s theory, E holds an element**: the added constant's, by the item of
`ΓDomains` that every value of a sort denotes one element of it. -/
theorem inhabited_of_plus (hovl : c.ovls = []) (hfresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c)
    (hfp : ∀ k ∈ c.params, k.sig.name ≠ eSym c) (hraw : c.keepsRaw (eSym c) [] = true)
    {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
    (hI : I ⊧ᴵP (Γc (plus c E) ∪ Γstep (plus c E))) :
    I ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName E)) (den c (eVal c) ≡ .evar ⟨1⟩) := by
  have hd : KoreAML.sExists ⟨1⟩ (sortP ((plus c E).sortName E)) (den (plus c E) (eVal c) ≡ .evar ⟨1⟩) ∈
      ΓDomains (plus c E) := .inr (.inr (.inl ⟨eVal c, E, sortOf_e hovl hfresh hfp hraw, rfl⟩))
  have h := hI _ (.inl (.inl (.inl (.inl (.inl (.inl (.inr hd)))))))
  rw [den_plus] at h
  exact h

/-- **A model of both theories**, from `plus c E`'s soundness hypotheses (`sound_hyp`). -/
theorem model_exists
    (hsub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc (plus c E) ∪ Γstep (plus c E))
    (hcore : (plus c E).coreOK = true) (hfn : FnHyp (plus c E)) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (plus c E) ∪ Γstep (plus c E))) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) := by
  obtain ⟨M, hM, I, hI⟩ := (sound_hyp (plus c E) hcore hfn).1
  exact ⟨M, hM, I, hI, model_of_plus hsub hI⟩

/-! ## The hypotheses where the interpretation gives nothing and no clause fails -/

/-- Where the interpretation gives no value anywhere, the fallbacks agree. -/
theorem fallback_plus_of_none (h : ∀ f vs, c.hooks.app f vs = none) (f : Sym) (vs : List GroundTerm) :
    (plus c E).fallback f vs = c.fallback f vs := by
  unfold Semantics.fallback
  split
  · show Option.filter _ (c.hooks.app f vs) = Option.filter _ (c.hooks.app f vs)
    rw [h]; rfl
  · rfl

/-- Where the interpretation gives no value anywhere, the added constant is left raw. -/
theorem keepsRaw_of_none (h : ∀ f vs, c.hooks.app f vs = none) : c.keepsRaw (eSym c) [] = true := by
  simp [Semantics.keepsRaw, h]

/-- A clause with no `requires`, the predicate `\top` and a match at `vs` does not fail there. -/
theorem not_fails_of {cl : Clause} {vs : List GroundTerm} {σ : Subst} (hreq : cl.req = none)
    (hpre : cl.pre = .top) (hσ : c.WellSortedAt cl.vars cl.leftVars σ) (hm : PatVals c σ cl.pats vs) :
    ¬ Fails c vs cl := by
  rintro ⟨h⟩
  cases h σ hσ hm with
  | intro ht _ _ => rw [hreq] at ht; cases ht
  | pre h => rw [hpre] at h; exact absurd (Holds.top_eq h) (by simp)

/-- A clause `f(X:s) => …` with no `requires` and the predicate `\top` does not fail at a value of
s. -/
theorem not_fails_var {cl : Clause} {s : Srt} {v : GroundTerm} (hv : cl.vars = [s]) (hp : cl.pats = [.var 0])
    (hreq : cl.req = none) (hpre : cl.pre = .top) (hs : c.sortOf v = some s) : ¬ Fails c [v] cl := by
  refine not_fails_of (σ := [(0, v)]) hreq hpre (fun i _ s' hi => ?_) (by rw [hp]; exact .cons (.var rfl) .nil)
  rw [hv] at hi
  cases i with
  | zero => cases hi; exact ⟨v, rfl, hs⟩
  | succ i => simp at hi

/-- A clause with no pattern, no `requires` and the predicate `\top` does not fail at `[]`. -/
theorem not_fails_nil {cl : Clause} (hp : cl.pats = []) (hl : cl.leftVars = []) (hreq : cl.req = none)
    (hpre : cl.pre = .top) : ¬ Fails c [] cl :=
  not_fails_of (σ := []) hreq hpre (fun i hi => by rw [hl] at hi; cases hi) (by rw [hp]; exact .nil)

theorem sortsOf_nil_of {d : Semantics} {vs : List GroundTerm} (h : d.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [Semantics.sortsOf] at h; split at h <;> cases h

theorem sortsOf_single {vs : List GroundTerm} {s : Srt} (h : c.sortsOf vs = some [s]) :
    ∃ v, vs = [v] ∧ c.sortOf v = some s := by
  match vs, h with
  | [], h => simp [Semantics.sortsOf] at h
  | v :: vs, h =>
    simp only [Semantics.sortsOf] at h
    cases hv : c.sortOf v with
    | none => rw [hv] at h; cases h
    | some s' =>
      cases hvs : c.sortsOf vs with
      | none => rw [hv, hvs] at h; cases h
      | some ss =>
        rw [hv, hvs] at h
        cases h
        exact ⟨v, by rw [sortsOf_nil_of hvs], hv⟩

/-- **No sort predicate has a point where every clause fails**: its last clause is `X:K`, with no
`requires`. -/
theorem sortPreds_noFail : ∀ fn ∈ c.sortPreds, ∀ vs, c.sortsOf vs = some fn.args →
    ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  simp only [Semantics.sortPreds, List.mem_append, List.mem_cons, List.mem_filterMap, List.not_mem_nil,
    or_false, Option.map_eq_some_iff] at hfn
  rcases hfn with (rfl | rfl) | ⟨X, -, p, -, rfl⟩
  · obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    exact ⟨_, List.mem_cons_self, not_fails_var rfl rfl rfl rfl hv⟩
  · obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, not_fails_var rfl rfl rfl rfl hv⟩
  · obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, not_fails_var rfl rfl rfl rfl hv⟩

/-- **The fallback hypothesis holds where no function of c has a point where every clause fails**:
the user's functions by `hu`, the sort predicates by `sortPreds_noFail`. -/
theorem hfails_of_noFail
    (hu : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl) :
    ∀ fn ∈ c.allFns, ∀ vs, c.sortsOf vs = some fn.args → (∀ cl ∈ fn.clauses, Fails c vs cl) →
      (∀ cl ∈ fn.clauses, Fails (plus c E) vs cl) ∧ (plus c E).fnRest fn vs = c.fnRest fn vs := by
  intro fn hfn vs hvs hall
  exfalso
  obtain ⟨cl, hcl, hnf⟩ := (List.mem_append.mp hfn).elim (fun h => hu fn h vs hvs)
    (fun h => sortPreds_noFail fn h vs hvs)
  exact hnf (hall cl hcl)

/-! ## E's one value -/


/-- **The added constant is the one value of sort E** in `plus c E`, where in c no constructor,
overloading symbol, open generator or subsort ends at E, no literal is of it and it is no
collection sort. -/
theorem value_E_eq (hctor : c.ctorSigs.all (·.result != E) = true) (hovl : c.ovls = [])
    (hraw : ∀ k ∈ c.params, k.raw = false) (hsub : c.subsorts.all (fun p => p.2 != E) = true)
    (hcoll : c.collOf E = none) (hcarr : c.lib.carriers.all (·.1 != E) = true)
    (hlit : (E != Srt.int && E != Srt.bool && E != Srt.kconfigVar && E != Srt.string && E != Srt.bytes &&
      E != Srt.float && !c.lib.tokenSorts.contains E && !c.lib.byteSorts.contains E) = true)
    {v : GroundTerm} (h : (plus c E).sortOf v = some E) : v = eVal c := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hlit
  obtain ⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hk⟩, hs⟩, hy⟩, hf⟩, ht⟩, hbs⟩ := hlit
  cases v with
  | ctor f ts =>
    simp only [Semantics.sortOf, plus_ctorSigs, plus_lookupOvl, plus_uncovered, plus_keepsRaw] at h
    have ho : c.lookupOvl f = none := by simp [Semantics.lookupOvl, hovl]
    cases hk' : lookupSig c.ctorSigs f with
    | some k =>
      rw [hk'] at h
      simp only at h
      have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk')
      have := List.all_eq_true.mp hctor k hm
      split at h
      · rw [Option.some.inj h] at this; simp at this
      · cases h
    | none =>
      rw [hk', ho] at h
      simp only at h
      cases hp : (plus c E).lookupOpen f with
      | none => rw [hp] at h; cases h
      | some k =>
        rw [hp] at h
        simp only at h
        obtain ⟨hm, hr, hn, -⟩ := Semantics.lookupOpen_spec _ hp
        rcases List.mem_append.mp hm with hm | hm
        · exact absurd hr (by rw [hraw k hm]; simp)
        · rw [List.mem_singleton] at hm
          subst hm
          have hts : (plus c E).sortsOf ts = some [] := by
            cases hb' : ((plus c E).sortsOf ts == some (eParam c E).sig.args) with
            | false => rw [hb'] at h; simp at h
            | true => exact beq_iff_eq.mp hb'
          rw [sortsOf_nil_of hts, ← hn]; rfl
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp hsub _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp h
    have hcs := Lib.carrier_of_not _ hcarr
    cases lit with
    | int _ => simp only [dvOK, plus_lib, hcs, beq_iff_eq] at hd; exact absurd hd hi
    | bool _ => simp only [dvOK, plus_lib, hcs, beq_iff_eq] at hd; exact absurd hd hb
    | float _ _ _ => simp only [dvOK, plus_lib, hcs, Bool.and_eq_true, beq_iff_eq] at hd; exact absurd hd.1 hf
    | tok t =>
      simp only [dvOK, plus_lib, hcs, ht, hbs, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true,
        beq_iff_eq] at hd
      rcases hd with (hd | hd) | ⟨hd, -⟩
      · exact absurd hd hk
      · exact absurd hd hs
      · exact absurd hd hy
  | map s' es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [plus_collOf, hcoll] at hco; cases hco
  | set s' es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [plus_collOf, hcoll] at hco; cases hco
  | list s' es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp h
    rw [plus_collOf, hcoll] at hco; cases hco

end EmptyInh

end KCore


