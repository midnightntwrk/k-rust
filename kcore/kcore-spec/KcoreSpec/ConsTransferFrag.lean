/-
  The translation of a KORE pattern whose sorts are all sort constants is of the class `OwnSorted`
  (ConsTransfer.lean) at no name, of kind `ex` (`own_kfrag_fg`): its connectives are sorted at a
  sort constant, its quantifiers range over a sort constant, and its free variables are among those
  listed. `KFrag` is that fragment: variables, symbol applications at constant sort arguments,
  literals, strings, the sorted connectives, `\exists`, `\forall`, `\ceil`, `\floor`, `\equals`,
  `\in`, `\next` and `\rewrites`. Its free variables are element variables of sort constants
  (`freeOf_kfrag_fg`).

  The patterns of terms (`Term.kore`), conditions (`Cond.kore`), a rule's competitors (`applies`)
  and a rule's axiom with its priority read (`prioRuleK`) are in the fragment
  (`kfrag_prioRuleK_fg`). So the translation of a rule's sentence, which has no sort variable, is
  a guarded premise of the class (`transfer_trAxiom_fg`), and the extension satisfies every premise
  of `ΓRules` that names nothing of `D` (`sat_own_rules`).

  The step's closure `∀y. •y ⊆ ⋁ disjuncts` quantifies `y` unsorted, so it is not of the class.
  Its disjuncts are (`own_closureDisjunct_fg`), and at an added `y` the premise holds because an
  added element has no successor: next holds only of old elements, and an old element applied to an
  added one gives nothing (`transfer_closure_fg`, `sat_own_step`).
-/
import KcoreSpec.ConsTransferDomains

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort VarKey VarTable)

local notation "Own0" => OwnSorted (fun _ => False)

/-- **The fragment.** KORE patterns whose sorts are sort constants. -/
inductive KFrag : Kore.Pattern → Prop
  | var {x : Kore.EVar} : (∃ C, x.sort = .ctor C []) → KFrag (.var (.evar x))
  | app {h : Kore.SymbolIdent} {ss : List Kore.KSort} {ps : List Kore.Pattern} :
      (∀ s ∈ ss, ∃ C, s = .ctor C []) → (∀ p ∈ ps, KFrag p) → KFrag (.app h ss ps)
  | dv {C : Kore.SortIdent} {lit : String} : KFrag (.dv (.ctor C []) lit)
  | str {s : String} : KFrag (.string s)
  | top {C : Kore.SortIdent} : KFrag (.top (.ctor C []))
  | bottom {C : Kore.SortIdent} : KFrag (.bottom (.ctor C []))
  | not {C : Kore.SortIdent} {p : Kore.Pattern} : KFrag p → KFrag (.not (.ctor C []) p)
  | and {C : Kore.SortIdent} {ps : List Kore.Pattern} : (∀ p ∈ ps, KFrag p) → KFrag (.and (.ctor C []) ps)
  | or {C : Kore.SortIdent} {ps : List Kore.Pattern} : (∀ p ∈ ps, KFrag p) → KFrag (.or (.ctor C []) ps)
  | implies {C : Kore.SortIdent} {p q : Kore.Pattern} : KFrag p → KFrag q → KFrag (.implies (.ctor C []) p q)
  | exist {S : Kore.KSort} {x : Kore.EVar} {p : Kore.Pattern} :
      (∃ C, x.sort = .ctor C []) → KFrag p → KFrag (.exist S x p)
  | all {C : Kore.SortIdent} {x : Kore.EVar} {p : Kore.Pattern} :
      (∃ C', x.sort = .ctor C' []) → KFrag p → KFrag (.forall (.ctor C []) x p)
  | ceil {C C' : Kore.SortIdent} {p : Kore.Pattern} : KFrag p → KFrag (.ceil (.ctor C []) (.ctor C' []) p)
  | floor {C C' : Kore.SortIdent} {p : Kore.Pattern} : KFrag p → KFrag (.floor (.ctor C []) (.ctor C' []) p)
  | equals {C C' : Kore.SortIdent} {p q : Kore.Pattern} : KFrag p → KFrag q →
      KFrag (.equals (.ctor C []) (.ctor C' []) p q)
  | inn {C C' : Kore.SortIdent} {p q : Kore.Pattern} : KFrag p → KFrag q →
      KFrag (.in (.ctor C []) (.ctor C' []) p q)
  | next {S : Kore.KSort} {p : Kore.Pattern} : KFrag p → KFrag (.next S p)
  | rewrites {C : Kore.SortIdent} {p q : Kore.Pattern} : KFrag p → KFrag q → KFrag (.rewrites (.ctor C []) p q)

section
variable {V : List EVar}

theorem own_trSort_fg (t : VarTable) (C : Kore.SortIdent) : Own0 V [] .ex (KoreAML.trSort t (.ctor C [])) := by
  rw [KoreAML.trSort_const]; exact .sortC id

theorem own_trSortApp_fg (t : VarTable) : ∀ {acc : KoreAML.P} {ss : List Kore.KSort},
    Own0 V [] .ex acc → (∀ s ∈ ss, ∃ C, s = .ctor C []) → Own0 V [] .ex (KoreAML.trSortApp t acc ss)
  | _, [], h, _ => by rw [KoreAML.trSortApp]; exact h
  | _, s :: ss, h, hs => by
    rw [KoreAML.trSortApp]
    obtain ⟨C, rfl⟩ := hs s (List.mem_cons_self ..)
    exact own_trSortApp_fg t (.appE h (own_trSort_fg t C).toOld) fun s' h' => hs s' (List.mem_cons_of_mem _ h')

theorem own_trAndList_fg (ctx : KoreAML.Ctx) (n : String) : ∀ {ps : List Kore.Pattern},
    (∀ p ∈ ps, Own0 V [] .ex (KoreAML.tr ctx p)) →
    Own0 V [] .ex (KoreAML.trAndList ctx (KoreAML.sym (.sort n)) ps)
  | [], _ => by rw [KoreAML.trAndList]; exact own_sTop_cs n
  | [p], h => by rw [KoreAML.trAndList]; exact h p (List.mem_singleton_self _)
  | p :: q :: ps, h => by
    rw [KoreAML.trAndList]
    exact .sAnd (h p (List.mem_cons_self ..))
      (own_trAndList_fg ctx n (ps := q :: ps) fun r hr => h r (List.mem_cons_of_mem _ hr)).toOld

/-- **The translation of a pattern of the fragment is of the class**, of kind `ex`, at variables
`V` that hold the indices of the bound keys `B` and of the free keys. -/
theorem own_kfrag_fg (t : VarTable) {p : Kore.Pattern} (hp : KFrag p) :
    ∀ (B : List VarKey) (V : List EVar), (∀ k ∈ B, t.ev k ∈ V) → (∀ k ∈ KoreAML.freeOf B p, t.ev k ∈ V) →
      Own0 V [] .ex (KoreAML.tr ⟨t, []⟩ p) := by
  induction hp with
  | @var x _ =>
    intro B V hB hf
    rw [KoreAML.tr]
    refine .evar ?_
    rw [KoreAML.freeOf] at hf
    by_cases hc : B.contains (KoreAML.evarKey x) = true
    · exact hB _ (List.contains_iff_mem.mp hc)
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hf
      exact hf _ (List.mem_singleton_self _)
  | @app h ss ps hs _ ih =>
    intro B V hB hf
    have htr : KoreAML.tr ⟨t, []⟩ (.app h ss ps) =
        KoreAML.appList (KoreAML.trSortApp t (KoreAML.sym (.symbol h.ident.name)) ss)
          (ps.map (KoreAML.tr ⟨t, []⟩)) := by
      rw [KoreAML.tr]
      simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
      exact Faithful.trArgs_appList _ _ _
    rw [htr]
    rw [KoreAML.freeOf] at hf
    refine .appList (own_trSortApp_fg t (.symC id) hs) fun a ha => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    exact (ih q hq B V hB fun k hk => hf k (mem_freeOfList hq hk)).toOld
  | dv =>
    intro B V _ _
    rw [KoreAML.tr]
    exact .appH (.dv _) (own_trSort_fg t _)
  | str => intro B V _ _; rw [KoreAML.tr]; exact .sym trivial id
  | top => intro B V _ _; rw [KoreAML.tr, KoreAML.trSort_const]; exact own_sTop_cs _
  | bottom => intro B V _ _; rw [KoreAML.tr, KoreAML.trSort_const]; exact own_sBot_cs _
  | not _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sNot (own_trSort_fg t _) (ih B V hB hf).toOld
  | @and C ps _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr, KoreAML.trSort_const]
    exact own_trAndList_fg _ _ fun q hq => ih q hq B V hB fun k hk => hf k (mem_freeOfList hq hk)
  | @or C ps _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr, KoreAML.trSort_const]
    exact own_trOrList_cs _ _ fun q hq => ih q hq B V hB fun k hk => hf k (mem_freeOfList hq hk)
  | implies _ _ ih1 ih2 =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sImp (own_trSort_fg t _) (ih1 B V hB fun k hk => hf k (List.mem_append_left _ hk)).toOld
      (ih2 B V hB fun k hk => hf k (List.mem_append_right _ hk)).toOld
  | @exist S x q hx _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    obtain ⟨C, hC⟩ := hx
    refine .sEx (V' := []) (by rw [hC]; exact own_trSort_fg t C) nil_sub (.inl rfl)
      (ih (KoreAML.evarKey x :: B) _ (fun k hk => ?_) fun k hk => List.mem_cons_of_mem _ (hf k hk))
    rcases List.mem_cons.mp hk with rfl | hk
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hB k hk)
  | @all C x q hx _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    obtain ⟨C', hC⟩ := hx
    refine .sNot (own_trSort_fg t _) (.toOld (.sEx (V' := []) (by rw [hC]; exact own_trSort_fg t C') nil_sub
      (.inl rfl) (.sNot (own_trSort_fg t _) (.toOld
        (ih (KoreAML.evarKey x :: B) _ (fun k hk => ?_) fun k hk => List.mem_cons_of_mem _ (hf k hk))))))
    rcases List.mem_cons.mp hk with rfl | hk
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hB k hk)
  | ceil _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sCeil (own_trSort_fg t _) (own_trSort_fg t _) (ih B V hB hf).toOld
  | floor _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sFloor (own_trSort_fg t _) (own_trSort_fg t _) (ih B V hB hf).toOld
  | equals _ _ ih1 ih2 =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sEquals (own_trSort_fg t _) (own_trSort_fg t _)
      (ih1 B V hB fun k hk => hf k (List.mem_append_left _ hk)).toOld
      (ih2 B V hB fun k hk => hf k (List.mem_append_right _ hk)).toOld
  | inn _ _ ih1 ih2 =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sIn (own_trSort_fg t _) (own_trSort_fg t _)
      (ih1 B V hB fun k hk => hf k (List.mem_append_left _ hk)).toOld
      (ih2 B V hB fun k hk => hf k (List.mem_append_right _ hk)).toOld
  | next _ ih =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sNext id (ih B V hB hf).toOld
  | rewrites _ _ ih1 ih2 =>
    intro B V hB hf
    rw [KoreAML.freeOf] at hf
    rw [KoreAML.tr]
    exact .sImp (own_trSort_fg t _) (ih1 B V hB fun k hk => hf k (List.mem_append_left _ hk)).toOld
      (OwnSorted.sNext id (ih2 B V hB fun k hk => hf k (List.mem_append_right _ hk)).toOld).toOld

end

/-! ## Patterns of the fragment -/

theorem kfrag_existsAll_fg (S : Kore.KSort) {body : Kore.Pattern} (hb : KFrag body) :
    ∀ (bs : List Kore.EVar), (∀ b ∈ bs, ∃ C, b.sort = .ctor C []) → KFrag (KoreAML.existsAll S bs body)
  | [], _ => hb
  | b :: bs, h => .exist (h b (List.mem_cons_self ..))
      (kfrag_existsAll_fg S hb bs fun b' h' => h b' (List.mem_cons_of_mem _ h'))

theorem varKore_sort_fg (v : KoreAML.Var) : ∃ C, v.kore.sort = .ctor C [] := ⟨_, rfl⟩

mutual
  theorem kfrag_kore_fg (c : Semantics) (vs : List KoreAML.Var) : ∀ t : Term, KFrag (Term.kore c vs t)
    | .var i => by rw [Term.kore]; exact .var (varKore_sort_fg _)
    | .app f ts => by
      rw [Term.kore]
      split
      · exact .app (fun s hs => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp hs; exact ⟨_, rfl⟩)
          (kfrag_koreList_fg c vs ts)
      · exact .app (fun s hs => absurd hs List.not_mem_nil) (kfrag_koreList_fg c vs ts)
    | .inj a b t => by
      rw [Term.kore]
      unfold KoreAML.injP
      refine .app (fun s hs => ?_) (fun p hp => ?_)
      · rcases mem_two hs with rfl | rfl <;> exact ⟨_, rfl⟩
      · rw [mem_one hp]; exact kfrag_kore_fg c vs t
    | .as t i => by
      rw [Term.kore]
      refine .and fun p hp => ?_
      rcases mem_two hp with rfl | rfl
      · exact kfrag_kore_fg c vs t
      · exact .var (varKore_sort_fg _)
    | .dv s lit => by rw [Term.kore]; exact .dv
  theorem kfrag_koreList_fg (c : Semantics) (vs : List KoreAML.Var) :
      ∀ ts : List Term, ∀ p ∈ Term.koreList c vs ts, KFrag p
    | [] => by intro p hp; rw [Term.koreList] at hp; exact absurd hp List.not_mem_nil
    | t :: ts => by
      intro p hp
      rw [Term.koreList] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact kfrag_kore_fg c vs t
      · exact kfrag_koreList_fg c vs ts p hp
end

theorem kfrag_cond_fg (c : Semantics) (C : Kore.SortIdent) :
    ∀ (p : Cond) (vs : List KoreAML.Var), KFrag (Cond.kore c vs (.ctor C []) p) := by
  intro p
  induction p with
  | top => intro vs; rw [Cond.kore]; exact .top
  | bot => intro vs; rw [Cond.kore]; exact .bottom
  | not p ih => intro vs; rw [Cond.kore]; exact .not (ih vs)
  | and p q ih1 ih2 =>
    intro vs; rw [Cond.kore]
    exact .and fun r hr => by rcases mem_two hr with rfl | rfl; exact ih1 vs; exact ih2 vs
  | or p q ih1 ih2 =>
    intro vs; rw [Cond.kore]
    exact .or fun r hr => by rcases mem_two hr with rfl | rfl; exact ih1 vs; exact ih2 vs
  | implies p q ih1 ih2 => intro vs; rw [Cond.kore]; exact .implies (ih1 vs) (ih2 vs)
  | ceil s t => intro vs; rw [Cond.kore]; exact .ceil (kfrag_kore_fg c vs t)
  | equals s t u => intro vs; rw [Cond.kore]; exact .equals (kfrag_kore_fg c vs t) (kfrag_kore_fg c vs u)
  | mem s t u => intro vs; rw [Cond.kore]; exact .inn (kfrag_kore_fg c vs t) (kfrag_kore_fg c vs u)
  | exMatch ys s p t body ih =>
    intro vs; rw [Cond.kore]
    refine kfrag_existsAll_fg _ (.and fun r hr => ?_) _ fun b hb => ?_
    · rcases mem_two hr with rfl | rfl
      · exact .inn (kfrag_kore_fg c vs t) (kfrag_kore_fg c _ p)
      · exact ih _
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
      exact varKore_sort_fg v
  | ex s body ih => intro vs; rw [Cond.kore]; exact .exist (varKore_sort_fg _) (ih _)
  | all s body ih => intro vs; rw [Cond.kore]; exact .all (varKore_sort_fg _) (ih _)

theorem kfrag_conj_fg (c : Semantics) (C : Kore.SortIdent) (vs : List KoreAML.Var) (p : Cond) :
    ∀ q ∈ Cond.conj c vs (.ctor C []) p, KFrag q := fun q hq => by
  unfold Cond.conj at hq
  split at hq
  · exact absurd hq List.not_mem_nil
  · rw [mem_one hq]; exact kfrag_cond_fg c C p vs

theorem kfrag_reqPat_fg (C : Kore.SortIdent) : ∀ (r : Option Kore.Pattern), (∀ p, r = some p → KFrag p) →
    KFrag (reqPat (.ctor C []) r)
  | none, _ => by rw [reqPat]; exact .top
  | some p, h => by rw [reqPat]; exact .equals (h p rfl) .dv

theorem kfrag_applies_fg (c : Semantics) (r : Rule) (rp : RulePres) : KFrag (applies c r rp) := by
  unfold applies
  refine kfrag_existsAll_fg _ (.and fun q hq => ?_) _ fun b hb => ?_
  · rcases List.mem_append.mp hq with hq | hq
    · rcases mem_two hq with rfl | rfl
      · exact kfrag_kore_fg c _ r.lhs
      · exact kfrag_reqPat_fg _ _ fun p hp => by
          obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hp
          exact kfrag_kore_fg c _ t
    · exact kfrag_conj_fg c _ _ r.pre q hq
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
    exact varKore_sort_fg v

theorem kfrag_anyOfC_fg (C : Kore.SortIdent) : ∀ (ps : List Kore.Pattern), (∀ p ∈ ps, KFrag p) →
    KFrag (anyOfC (.ctor C []) ps)
  | [], _ => by rw [anyOfC]; exact .bottom
  | p :: ps, h => by
    rw [anyOfC]
    exact .or fun q hq => by
      rcases mem_two hq with rfl | rfl
      · exact h _ (List.mem_cons_self ..)
      · exact kfrag_anyOfC_fg C ps fun p' h' => h p' (List.mem_cons_of_mem _ h')

theorem kfrag_ruleRight_fg (c : Semantics) (r : Rule) : KFrag (ruleRight c r) := by
  unfold ruleRight
  dsimp only
  generalize (r.exs.filterMap ((canonVars c r.vars)[·]?)) = bs
  induction bs with
  | nil =>
    exact .and fun q hq => by
      rcases List.mem_append.mp hq with hq | hq
      · rcases mem_two hq with rfl | rfl
        · exact kfrag_kore_fg c _ r.rhs
        · exact kfrag_reqPat_fg _ _ fun p hp => by
            obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hp
            exact kfrag_kore_fg c _ t
      · exact kfrag_conj_fg c _ _ r.post q hq
  | cons v bs ih => exact .exist (varKore_sort_fg v) ih

/-- **A rule's axiom with its priority read is in the fragment.** -/
theorem kfrag_prioRuleK_fg (c : Semantics) (r : Rule) : KFrag (prioRuleK c r) := by
  have hl : ∀ q ∈ [Term.kore c (canonVars c r.vars) r.lhs,
      reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))] ++
      Cond.conj c (canonVars c r.vars) (srtOf c topCellSort) r.pre, KFrag q := fun q hq => by
    rcases List.mem_append.mp hq with hq | hq
    · rcases mem_two hq with rfl | rfl
      · exact kfrag_kore_fg c _ r.lhs
      · exact kfrag_reqPat_fg _ _ fun p hp => by
          obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp hp
          exact kfrag_kore_fg c _ t
    · exact kfrag_conj_fg c _ _ r.pre q hq
  unfold prioRuleK
  dsimp only
  split
  · refine .rewrites (.and fun q hq => ?_) (kfrag_ruleRight_fg c r)
    rcases List.mem_append.mp hq with hq | hq
    · exact hl q hq
    · rw [mem_one hq]; exact .ceil (kfrag_ruleRight_fg c r)
  · refine .rewrites (.and fun q hq => ?_) (kfrag_ruleRight_fg c r)
    rcases List.mem_append.mp hq with hq | hq
    · exact hl q hq
    · rcases mem_two hq with rfl | rfl
      · refine .not (kfrag_anyOfC_fg _ _ fun p hp => ?_)
        obtain ⟨r', -, rfl⟩ := List.mem_map.mp hp
        exact kfrag_applies_fg c r' _
      · exact .ceil (kfrag_ruleRight_fg c r)

/-! ## The free variables of a pattern of the fragment -/

/-- A free variable of a pattern of the fragment is an element variable of a sort constant. -/
theorem freeOf_kfrag_fg {p : Kore.Pattern} (hp : KFrag p) :
    ∀ (B : List VarKey) {k : VarKey}, k ∈ KoreAML.freeOf B p → ∃ n C, k = .evar n (.ctor C []) := by
  induction hp with
  | @var x hx =>
    intro B k hk
    rw [KoreAML.freeOf] at hk
    split at hk
    · exact absurd hk List.not_mem_nil
    · obtain ⟨C, hC⟩ := hx
      rw [mem_one hk]
      exact ⟨x.var.ident.name, C, by rw [← hC]; rfl⟩
  | @app h ss ps _ _ ih =>
    intro B k hk
    rw [KoreAML.freeOf] at hk
    obtain ⟨q, hq, hk⟩ := mem_freeOfList_inv_fg hk
    exact ih q hq B hk
  | dv | str | top | bottom => intro B k hk; rw [KoreAML.freeOf] at hk; exact absurd hk List.not_mem_nil
  | not _ ih | ceil _ ih | floor _ ih | next _ ih =>
    intro B k hk; rw [KoreAML.freeOf] at hk; exact ih B hk
  | and _ ih | or _ ih =>
    intro B k hk
    rw [KoreAML.freeOf] at hk
    obtain ⟨q, hq, hk⟩ := mem_freeOfList_inv_fg hk
    exact ih q hq B hk
  | implies _ _ ih1 ih2 | equals _ _ ih1 ih2 | inn _ _ ih1 ih2 | rewrites _ _ ih1 ih2 =>
    intro B k hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact ih1 B hk
    · exact ih2 B hk
  | exist _ _ ih | all _ _ ih => intro B k hk; rw [KoreAML.freeOf] at hk; exact ih _ hk
where
  mem_freeOfList_inv_fg {B : List VarKey} {k : VarKey} : ∀ {ps : List Kore.Pattern},
      k ∈ KoreAML.freeOfList B ps → ∃ q ∈ ps, k ∈ KoreAML.freeOf B q
    | [], h => by rw [KoreAML.freeOfList] at h; exact absurd h List.not_mem_nil
    | q :: qs, h => by
      rw [KoreAML.freeOfList] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨q, List.mem_cons_self .., h⟩
      · obtain ⟨q', hq', h'⟩ := mem_freeOfList_inv_fg h
        exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩

/-! ## The rules -/

/-- A premise `⋀ws → φ` holds exactly when `guarded ws φ` does. -/
theorem impConj_iff_fg {N : Type} {J : Interpretation KoreAML.Sym N} {ws : List KoreAML.P} {φ : KoreAML.P} :
    (J ⊧ᴵ (KoreAML.conjList ws ⇒ φ)) ↔ (J ⊧ᴵ KoreAML.guarded ws φ) := by
  cases ws with
  | nil =>
    constructor
    · intro h e m; exact (h e m) (fun hb => hb)
    · intro h e m _; exact h e m
  | cons w ws => exact Iff.rfl

theorem psyms_impConj_fg {ws : List KoreAML.P} {φ : KoreAML.P} {σ : KoreAML.Sym}
    (h : σ ∈ psyms (KoreAML.guarded ws φ)) : σ ∈ psyms (KoreAML.conjList ws ⇒ φ) := by
  cases ws with
  | nil => simp only [psyms, List.mem_append]; exact .inr h
  | cons w ws => exact h

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- **Transfer of the translation of a sentence without sort variables** whose pattern is of the
fragment and has a sort constant as its sort. -/
theorem transfer_trAxiom_fg (hDI : DefOK I) {P : Kore.Pattern} (hP : KFrag P) {C : Kore.SortIdent}
    (hs : KoreAML.sortOf [] P = some (.ctor C [])) {attrs : List Kore.AppPattern} (i : Nat) (md : String)
    (hn : ∀ σ ∈ psyms (KoreAML.trAxiom [] [] ⟨i, md, { sortVars := [], pattern := P, attributes := attrs }⟩).pat, ¬ D σ)
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, md, { sortVars := [], pattern := P, attributes := attrs }⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, md, { sortVars := [], pattern := P, attributes := attrs }⟩).pat := by
  let t := KoreAML.tableOf [] P
  let fr := (KoreAML.freeOf [] P).eraseDups
  let srtK : VarKey → KoreAML.P := fun k => match k with
    | .evar _ s => KoreAML.trSort t s
    | _ => ⊥
  let gs : List (EVar × KoreAML.P) := fr.map fun k => (t.ev k, srtK k)
  have hfr : ∀ k ∈ fr, ∃ n C', k = .evar n (.ctor C' []) := fun k hk =>
    freeOf_kfrag_fg hP [] (List.mem_eraseDups.mp hk)
  have hgs : fr.map (KoreAML.guardOf t) = memGs gs := by
    simp only [memGs, gs, List.map_map]
    refine List.map_congr_left fun k hk => ?_
    obtain ⟨n, C', rfl⟩ := hfr k hk
    rfl
  have hpat : (KoreAML.trAxiom [] [] ⟨i, md, { sortVars := [], pattern := P, attributes := attrs }⟩).pat =
      (KoreAML.conjList (memGs gs) ⇒ (KoreAML.tr ⟨t, []⟩ P ≡ KoreAML.inhOf (KoreAML.trSort t (.ctor C [])))) := by
    unfold KoreAML.trAxiom
    simp only
    rw [hs, ← hgs]
    rfl
  have hsg : ∀ p ∈ gs, Own0 [] [] .ex p.2 := fun p hp => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨n, C', rfl⟩ := hfr k hk
    exact own_trSort_fg t C'
  have hb : Own0 (gs.map (·.1)) [] .pred (KoreAML.tr ⟨t, []⟩ P ≡ KoreAML.inhOf (KoreAML.trSort t (.ctor C []))) :=
    .equal_ex (own_kfrag_fg t hP [] _ nil_sub fun k hk => by
        simp only [gs, List.map_map]
        exact List.mem_map.mpr ⟨k, List.mem_eraseDups.mpr hk, rfl⟩)
      (.inhOf (own_trSort_fg t C))
  rw [hpat] at hn h ⊢
  rw [impConj_iff_fg] at h ⊢
  exact transferG_sg hD hDI hsg hb (.inl rfl) (fun σ hσ => hn σ (psyms_impConj_fg hσ)) h

/-- **The extension satisfies every premise of `ΓRules` that names nothing of `D`**, for a model of
`Γown c D` and names `D` that are sort constants and symbols of the definition. -/
theorem sat_own_rules (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : ΓRules c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inl (.inl (.inl (.inr hφ))), hn⟩
  rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hit
    have hs : KoreAML.sortOf [] (prioRuleK c r) = some (srtOf c topCellSort) := by
      unfold prioRuleK; dsimp only; split <;> rfl
    exact transfer_trAxiom_fg hD hDI (kfrag_prioRuleK_fg c r) hs 0 "kernel" hn hI'
  · exact sat_definedness_sg x

end

/-! ## The step's closure -/

theorem own_disjList_fg {V : List EVar} {W : List SVar} : ∀ {ds : List KoreAML.P}, (∀ d ∈ ds, Own0 V W .ex d) →
    Own0 V W .ex (KoreAML.disjList ds)
  | [], _ => .bot
  | [d], h => h d (List.mem_singleton_self _)
  | d :: d' :: ds, h => .disj_ex (h d (List.mem_cons_self ..))
      (own_disjList_fg (ds := d' :: ds) fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem own_foldrEx_fg (table : VarTable) : ∀ (fr : List (VarKey × Kore.KSort)) (V : List EVar) {body : KoreAML.P},
    (∀ p ∈ fr, ∃ C, p.2 = .ctor C []) → Own0 ((fr.map fun p => table.ev p.1) ++ V) [] .ex body →
    Own0 V [] .ex (fr.foldr (fun x φ => KoreAML.sExists (table.ev x.fst) (KoreAML.trSort table x.snd) φ) body)
  | [], _, _, _, h => h
  | p :: fr, V, body, hs, h => by
    rw [List.foldr_cons]
    obtain ⟨C, hC⟩ := hs p (List.mem_cons_self ..)
    refine .sEx (V' := []) (by rw [hC]; exact own_trSort_fg table C) nil_sub (.inl rfl)
      (own_foldrEx_fg table fr _ (fun q hq => hs q (List.mem_cons_of_mem _ hq)) (h.mono (fun z hz => ?_) fun _ h => h))
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hz ⊢
    rcases hz with rfl | hz | hz
    · exact .inr (.inl rfl)
    · exact .inl hz
    · exact .inr (.inr hz)

/-- **The closure's disjunct of a pattern of the fragment is of the class** at the successor
variable `y`: its free variables are bound at their sort constants. -/
theorem own_closureDisjunct_fg {P : Kore.Pattern} (hP : KFrag P) (off : Nat) (y : EVar) :
    Own0 [y] [] .ex (KoreAML.closureDisjunct [] off y P).2 := by
  unfold KoreAML.closureDisjunct
  dsimp only
  generalize (List.replicate off (KoreAML.VarKey.sortVar "#pad") ++ KoreAML.tableOf [] P : VarTable) = table
  generalize hfr : List.filterMap _ (KoreAML.freeOf [] P).eraseDups = fr
  have hfrS : ∀ p ∈ fr, p.1 ∈ KoreAML.freeOf [] P ∧ ∃ C, p.2 = .ctor C [] := fun p hp => by
    rw [← hfr] at hp
    obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp hp
    obtain ⟨n, C, rfl⟩ := freeOf_kfrag_fg hP [] (List.mem_eraseDups.mp hk)
    simp only [Option.some.injEq] at he
    subst he
    exact ⟨List.mem_eraseDups.mp hk, C, rfl⟩
  have hV : ∀ k ∈ KoreAML.freeOf [] P, KoreAML.VarTable.ev table k ∈ (fr.map fun p => KoreAML.VarTable.ev table p.1) ++ [y] := fun k hk => by
    obtain ⟨n, C, rfl⟩ := freeOf_kfrag_fg hP [] hk
    refine List.mem_append_left _ (List.mem_map.mpr ⟨(.evar n (.ctor C []), .ctor C []), ?_, rfl⟩)
    rw [← hfr]
    exact List.mem_filterMap.mpr ⟨_, List.mem_eraseDups.mpr hk, rfl⟩
  refine own_foldrEx_fg table fr [y] (fun p hp => (hfrS p hp).2) ?_
  have hy : y ∈ (fr.map fun p => KoreAML.VarTable.ev table p.1) ++ [y] := List.mem_append_right _ (List.mem_singleton_self _)
  cases hP with
  | rewrites hl hr =>
    exact .conj_ex_old (own_kfrag_fg table hl [] _ nil_sub fun k hk => hV k (List.mem_append_left _ hk))
      (OwnSorted.member hy (own_kfrag_fg table hr [] _ nil_sub fun k hk => hV k (List.mem_append_right _ hk)).toOld).toOld
  | _ => exact .conj_ex_old .bot (OwnSorted.member hy (OwnSorted.bot).toOld).toOld

theorem foldl_closure_fg (y : EVar) (F : List String × List KoreAML.P × Nat → Kore.Pattern →
      List String × List KoreAML.P × Nat)
    (hF : ∀ acc p, (F acc p).2.1 = acc.2.1 ++ [(KoreAML.closureDisjunct [] acc.2.2 y p).2]) :
    ∀ (pats : List Kore.Pattern) (acc : List String × List KoreAML.P × Nat), (∀ p ∈ pats, KFrag p) →
      (∀ φ ∈ acc.2.1, Own0 [y] [] .ex φ) → ∀ φ ∈ (pats.foldl F acc).2.1, Own0 [y] [] .ex φ
  | [], _, _, h => h
  | p :: pats, acc, hp, h => by
    rw [List.foldl_cons]
    refine foldl_closure_fg y F hF pats _ (fun q hq => hp q (List.mem_cons_of_mem _ hq)) fun φ hφ => ?_
    rw [hF] at hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact h φ hφ
    · rw [mem_one hφ]; exact own_closureDisjunct_fg (hp p (List.mem_cons_self ..)) _ y

theorem psyms_closure_fg {y : EVar} {ψ : KoreAML.P} {σ : KoreAML.Sym}
    (h : σ ∈ psyms (KoreAML.sNext (.evar y)) ∨ σ ∈ psyms ψ) :
    σ ∈ psyms (∀∀ y (KoreAML.sNext (.evar y) ⊆⊆ ψ)) := by
  rcases h with h | h <;>
    simp [psyms, ML.included, ML.total, Pattern.negation, h]

section
variable {c : Semantics} {D : KoreAML.Sym → Prop} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ)
include hD

/-- **Transfer of the closure's shape `∀y. •y ⊆ ψ`**, whose quantifier is unsorted: at an old `y`
the premise is of the class, and at an added `y` it holds because an added element has no
successor (`•y` is empty: next holds only of old elements, and an old element applied to an added
one gives nothing). -/
theorem transfer_closure_fg (hDI : DefOK I) {y : EVar} {ψ : KoreAML.P} (hψ : OwnSorted D [y] [] .old ψ)
    (hnx : ¬ D .next) (h : I ⊧ᴵ ∀∀ y (KoreAML.sNext (.evar y) ⊆⊆ ψ)) :
    extModel c D I ⊧ᴵ ∀∀ y (KoreAML.sNext (.evar y) ⊆⊆ ψ) := by
  have hb : OwnSorted D [y] [] .pred (KoreAML.sNext (.evar y) ⊆⊆ ψ) :=
    .included (.sNext hnx (OwnSorted.evar (List.mem_singleton_self _)).toOld) hψ
  intro e' pt
  simp only [Pattern.universal, interpret_neg, interpret_exists, not_exists, Classical.not_not]
  intro a
  cases a with
  | inl m0 =>
    let e0 : Valuation M := ⟨Function.update (pullVal e').evalEvar y m0, (pullVal e').evalSvar⟩
    have hrel : OwnRel [y] [] e0 ⟨Function.update e'.evalEvar y (.inl m0), e'.evalSvar⟩ :=
      ⟨fun x hx => by rw [List.mem_singleton.mp hx]; simp [e0], nil_sub⟩
    have hinv := transfer_rel (c := c) hD hDI hb e0 _ hrel
    have hI0 : ∀ m, (KoreAML.sNext (.evar y) ⊆⊆ ψ).interpret I e0 m := fun m => by
      have := h (pullVal e') m
      simp only [Pattern.universal, interpret_neg, interpret_exists, not_exists, Classical.not_not] at this
      exact this m0
    cases pt with
    | inl m => exact (hinv.1 m).mpr (hI0 m)
    | inr n => exact (hinv.2.2 n).mpr hI0
  | inr n =>
    rw [KoreAML.interp_included (ext_defOK c D I)]
    intro x hx
    unfold KoreAML.sNext at hx
    obtain ⟨d, b, hd, hb', happ⟩ := interpret_app.mp hx
    rw [KoreAML.interp_evar] at hb'
    simp only [Function.update_same] at hb'
    subst hb'
    rw [KoreAML.interp_sym] at hd
    cases d with
    | inl d0 => exact absurd happ app_inl_inr
    | inr nd => exact absurd hd ((inv_sym (c := c) (I := I) (σ := .next) trivial hnx).2 nd)

/-- **The extension satisfies the step's closure where it names nothing of `D`**, for a model of
`Γown c D` and names `D` that are sort constants and symbols of the definition. -/
theorem sat_own_step (hI : I ⊧ᴵP Γown c D) {φ : KoreAML.P} (hφ : Γstep c φ)
    (hn : ∀ σ ∈ psyms φ, ¬ D σ) : extModel c D I ⊧ᴵ φ := by
  have hDI := defOK_own_sg hD hI
  have hI' : I ⊧ᴵ φ := hI _ ⟨.inr hφ, hn⟩
  rw [hφ] at hn hI' ⊢
  unfold stepClosureItem at hn hI' ⊢
  dsimp only at hn hI' ⊢
  refine transfer_closure_fg hD hDI (ownSorted_clean_sg (own_disjList_fg (foldl_closure_fg _ _ (fun _ _ => rfl)
      _ _ (fun p hp => ?_) (fun φ hφ => absurd hφ List.not_mem_nil))).toOld
    fun σ hσ => hn σ (psyms_closure_fg (.inr hσ))) (hn _ (psyms_closure_fg (.inl (by simp [psyms, KoreAML.sNext, KoreAML.sym])))) hI'
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hp
  exact kfrag_prioRuleK_fg c r

end

end KCore.Cons
