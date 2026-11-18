/-
  The generated equations' conservativity for symbols the semantics does not number, and at the
  model of any choice of instances.

  - **Names no premise of the theory applies (`nameFreeB`).** For a list of symbol names `ns` (a
    name the semantics need not number: a constructor argument's projection `project:c:x`, an own
    sort's projection, `getGeneratedCounterCell`), a decided check that no premise of
    `Γc c ∪ Γstep c` holds the symbol of one of them (`nameFree_of_decided`): no item of the
    theory's lists holds one; the values hold none (no constructor, overloading symbol, parameter
    symbol or collection symbol has one of the names, nor has `inj`); the symbols the theory applies
    at values hold none (no hook, parameter symbol or function has one of the names, nor has `ite`
    where one is sort-parametric). Its conclusion is `model_with_eqns`' `hfree` at the names `ns`.
  - **The model of a choice among instances (`model_with_eqns_choice`).** For a transition `T`
    meeting `has_model_choice`'s three conditions, the value model at `T` with the names' heads
    applied by partial functions on values: a model of the theory, with the equations at values,
    whose steps at configurations are `T`. At `T := Step c`, the semantics' own steps
    (`model_with_eqns_step`).
-/
import KcoreSpec.GenEqsModel
import KcoreSpec.ExChoice

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

namespace NameFree

variable (c : Semantics) (ns : List String)

/-- The symbol is the symbol of one of the names. -/
def isNm : KoreAML.Sym → Bool
  | .symbol n => ns.contains n
  | _ => false

/-- No symbol of the pattern is one of the names. -/
def cleanN (φ : KoreAML.P) : Bool := (psyms φ).all fun σ => !isNm ns σ

/-- The symbol's name is none of the names. -/
def kOKN (f : Sym) : Bool := !ns.contains (c.symName f)

/-- The head `symApp` writes for `f` is none of the names. -/
def appOKN (f : Sym) : Bool :=
  match iteSort? (c.symName f) with
  | some _ => !ns.contains "Lblite"
  | none => kOKN c ns f

/-- The values are built from symbols outside the names: constructors, overloading symbols and
parameter symbols, the injection, and the collections' symbols. -/
def valuesN : Bool :=
  (c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig)).all (fun k => kOKN c ns k.name) &&
  c.allColls.all (fun k => kOKN c ns k.unit && kOKN c ns k.elem && kOKN c ns k.concat) &&
  !ns.contains "inj"

/-- The symbols the theory applies at values are outside the names: the hooks, the parameter
symbols and the functions. -/
def graphsN : Bool :=
  hookSigs.all (fun k => appOKN c ns k.name) && c.params.all (fun k => appOKN c ns k.sig.name) &&
  c.allFns.all (fun f => appOKN c ns f.label)

/-- The parts of the theory that are lists. -/
def listsN : Bool :=
  (sigItems c ++ consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).all (fun it => cleanN ns it.pat) &&
  c.allColls.all (fun k => cleanN ns (collNoJunk c k) && (collAxioms c k).all (cleanN ns)) &&
  cleanN ns (boolClosed c)

end NameFree

open NameFree in
/-- **No premise holds a symbol of the names `ns`, decided**: the theory's lists (`listsN`), the
values (`valuesN`) and the symbols applied at values (`graphsN`). -/
def nameFreeB (c : Semantics) (ns : List String) : Bool :=
  listsN c ns && valuesN c ns && graphsN c ns

namespace NameFree

variable {c : Semantics} {ns : List String}

theorem isNm_symbol {n : String} : isNm ns (.symbol n) = ns.contains n := rfl

@[simp] theorem cleanN_symbol (σ : KoreAML.Sym) : cleanN ns (.symbol σ) = !isNm ns σ := by
  simp [cleanN, psyms]
@[simp] theorem cleanN_app (a b : KoreAML.P) : cleanN ns (a ⬝ b) = (cleanN ns a && cleanN ns b) := by
  simp [cleanN, psyms, List.all_append]
@[simp] theorem cleanN_imp (a b : KoreAML.P) : cleanN ns (a ⇒ b) = (cleanN ns a && cleanN ns b) := by
  simp [cleanN, psyms, List.all_append]
@[simp] theorem cleanN_ex (x : EVar) (a : KoreAML.P) : cleanN ns (.existential x a) = cleanN ns a := by
  simp [cleanN, psyms]
@[simp] theorem cleanN_mu (X : SVar) (a : KoreAML.P) : cleanN ns (.mu X a) = cleanN ns a := by
  simp [cleanN, psyms]
@[simp] theorem cleanN_bot : cleanN ns (⊥ : KoreAML.P) = true := rfl
@[simp] theorem cleanN_evar (x : EVar) : cleanN ns (.evar x : KoreAML.P) = true := rfl
@[simp] theorem cleanN_svar (X : SVar) : cleanN ns (.svar X : KoreAML.P) = true := rfl
@[simp] theorem isNm_defined : isNm ns (HasDefined.defined : KoreAML.Sym) = false := rfl
@[simp] theorem isNm_sort (n : String) : isNm ns (.sort n) = false := rfl

/-- A clean pattern holds no symbol of the names. -/
theorem cleanN_spec {φ : KoreAML.P} (h : cleanN ns φ = true) {n : String} (hn : n ∈ ns) :
    KoreAML.Sym.symbol n ∉ psyms φ := by
  intro hm
  have := List.all_eq_true.mp h _ hm
  simp only [isNm, Bool.not_eq_true'] at this
  rw [List.contains_iff_mem.mpr hn] at this
  cases this

theorem cleanN_appList : ∀ (φs : List KoreAML.P) (h : KoreAML.P),
    cleanN ns (KoreAML.appList h φs) = (cleanN ns h && φs.all (cleanN ns))
  | [], h => by simp [KoreAML.appList]
  | φ :: φs, h => by simp [KoreAML.appList, cleanN_appList φs, Bool.and_assoc]

theorem cleanN_eq (a b : KoreAML.P) : cleanN ns (a ≡ b) = (cleanN ns a && cleanN ns b) := by
  simp only [ML.equal, ML.total, Pattern.equivalence, Pattern.conjunction, Pattern.disjunction, Pattern.negation,
    cleanN_app, cleanN_imp, cleanN_symbol, cleanN_bot, isNm_defined]
  cases cleanN ns a <;> cases cleanN ns b <;> rfl

theorem cleanN_neg (a : KoreAML.P) : cleanN ns (∼a) = cleanN ns a := by
  simp [Pattern.negation]

theorem cleanN_and (a b : KoreAML.P) : cleanN ns (a ⋀ b) = (cleanN ns a && cleanN ns b) := by
  simp only [Pattern.conjunction, Pattern.disjunction, Pattern.negation, cleanN_imp, cleanN_bot]
  cases cleanN ns a <;> cases cleanN ns b <;> rfl

theorem cleanN_sExists (x : EVar) (n : String) (a : KoreAML.P) :
    cleanN ns (KoreAML.sExists x (sortP n) a) = cleanN ns a := by
  simp only [KoreAML.sExists, cleanN_ex, cleanN_and, ML.member, cleanN_app, cleanN_symbol, isNm_defined,
    cleanN_evar, KoreAML.inhOf, KoreAML.sym, sortP]
  simp [isNm]

theorem cleanN_ap (f : String) (ps : List Kore.Pattern) :
    cleanN ns (KoreAML.den (KoreAML.ap f ps)) =
      (!ns.contains f && ps.all fun p => cleanN ns (KoreAML.den p)) := by
  unfold KoreAML.den
  rw [Model.tr_ap, cleanN_appList]
  simp [KoreAML.sym, List.all_map, Function.comp_def, isNm]

theorem cleanN_symApp (f : Sym) (ps : List Kore.Pattern) (hf : appOKN c ns f = true)
    (hps : ∀ p ∈ ps, cleanN ns (KoreAML.den p) = true) :
    cleanN ns (KoreAML.den (symApp c f ps)) = true := by
  unfold symApp
  unfold appOKN at hf
  cases hi : iteSort? (c.symName f) with
  | none =>
    rw [hi] at hf
    exact (cleanN_ap (ns := ns) (c.symName f) ps).trans
      (by rw [show (!ns.contains (c.symName f)) = true from hf, Bool.true_and]
          exact List.all_eq_true.mpr hps)
  | some X =>
    rw [hi] at hf
    show cleanN ns (KoreAML.tr ⟨[], []⟩ (.app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt X] ps)) = true
    rw [KoreAML.tr]
    simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte, KoreAML.trSortApp, KoreAML.srt,
      KoreAML.trSort_const, trArgs_appList, cleanN_appList, cleanN_app, KoreAML.sym, cleanN_symbol,
      Bool.and_eq_true, List.all_map, List.all_eq_true]
    exact ⟨⟨hf, rfl⟩, fun p hp => hps p hp⟩

/-- A collection of elements: clean where its symbols and its elements are. -/
theorem cleanN_elems (k : CollSig) (hu : kOKN c ns k.unit = true) (he : kOKN c ns k.elem = true)
    (hc : kOKN c ns k.concat = true) : ∀ es : List GroundTerm,
    (∀ e ∈ es, cleanN ns (den c e) = true) →
    cleanN ns (KoreAML.den (GroundTerm.koreElems c k es)) = true
  | [], _ => by rw [GroundTerm.koreElems, cleanN_ap]; simpa [kOKN] using hu
  | [e], h => by
    rw [GroundTerm.koreElems, cleanN_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOKN] using he, h e (List.mem_cons_self ..)⟩
  | e :: e' :: es, h => by
    rw [GroundTerm.koreElems, cleanN_ap]
    case x_1 => exact fun h => nomatch h
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨by simpa [kOKN] using hc, ?_, cleanN_elems k hu he hc (e' :: es) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    rw [cleanN_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOKN] using he, h e (List.mem_cons_self ..)⟩

/-- A collection of entries: clean where its symbols and its entries' parts are. -/
theorem cleanN_entries (k : CollSig) (hu : kOKN c ns k.unit = true) (he : kOKN c ns k.elem = true)
    (hc : kOKN c ns k.concat = true) : ∀ es : List (GroundTerm × GroundTerm),
    (∀ e ∈ es, cleanN ns (den c e.1) = true ∧ cleanN ns (den c e.2) = true) →
    cleanN ns (KoreAML.den (GroundTerm.koreEntries c k es)) = true
  | [], _ => by rw [GroundTerm.koreEntries, cleanN_ap]; simpa [kOKN] using hu
  | [(x, v)], h => by
    rw [GroundTerm.koreEntries, GroundTerm.koreEntry, cleanN_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOKN] using he, (h _ (List.mem_cons_self ..)).1, (h _ (List.mem_cons_self ..)).2⟩
  | (x, v) :: e' :: es, h => by
    rw [GroundTerm.koreEntries, GroundTerm.koreEntry, cleanN_ap]
    case x_1 => exact fun h => nomatch h
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨by simpa [kOKN] using hc, ?_,
      cleanN_entries k hu he hc (e' :: es) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    rw [cleanN_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOKN] using he, (h _ (List.mem_cons_self ..)).1, (h _ (List.mem_cons_self ..)).2⟩

section Values

variable (hV : valuesN c ns = true)
include hV

theorem valuesN_sig {k : CtorSig} (hk : k ∈ c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig)) :
    kOKN c ns k.name = true := by
  simp only [valuesN, Bool.and_eq_true, List.all_eq_true] at hV
  exact hV.1.1 k hk

theorem valuesN_coll {k : CollSig} (hk : k ∈ c.allColls) :
    kOKN c ns k.unit = true ∧ kOKN c ns k.elem = true ∧ kOKN c ns k.concat = true := by
  simp only [valuesN, Bool.and_eq_true, List.all_eq_true] at hV
  obtain ⟨⟨h1, h2⟩, h3⟩ := hV.1.2 k hk
  exact ⟨h1, h2, h3⟩

theorem valuesN_inj : ns.contains "inj" = false := by
  simp only [valuesN, Bool.and_eq_true, Bool.not_eq_true'] at hV
  exact hV.2

mutual
/-- **A value holds no symbol of the names.** -/
theorem cleanN_val : ∀ (v : GroundTerm) (s : Srt), c.sortOf v = some s → cleanN ns (den c v) = true
  | .ctor f ts, s, hv => by
    have key : ∀ k : CtorSig, k ∈ c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig) → k.name = f →
        c.sortsOf ts = some k.args → cleanN ns (den c (.ctor f ts)) = true := by
      intro k hk hn hts
      have h1 := valuesN_sig hV hk
      rw [den_ctor, trArgs_appList, cleanN_appList, DetachedB.koreList_map, ← hn]
      simp only [KoreAML.sym, cleanN_symbol, Bool.and_eq_true, List.all_map, List.all_eq_true]
      refine ⟨by simpa [kOKN, isNm] using h1, fun t ht => ?_⟩
      exact cleanN_all ts (fun t ht => by
        obtain ⟨s', -, h'⟩ := DetachedB.sortsOf_mem hts t ht
        exact ⟨s', h'⟩) t ht
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, hts, -⟩ | ⟨-, o, ho, hts, -, -⟩ | ⟨-, -, k, hko, hts, -, -⟩
    · exact key k (List.mem_append_left _ (List.mem_append_left _ (lookupSig_spec hk).1)) (lookupSig_spec hk).2 hts
    · have ho' : c.ovls.find? (·.sig.name == f) = some o := ho
      exact key o.sig (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_of_find?_eq_some ho')))) (by simpa using List.find?_some ho') hts
    · obtain ⟨hm, -, hn, -⟩ := c.lookupOpen_spec hko
      exact key k.sig (List.mem_append_right _ (List.mem_map_of_mem hm)) hn hts
  | .inj a b t, s, hv => by
    obtain ⟨-, -, ht, -⟩ := sortOf_inj.mp hv
    rw [den_inj, cleanN_appList]
    simp only [KoreAML.sym, cleanN_symbol, isNm, valuesN_inj hV, Bool.not_false, Bool.true_and, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simp [KoreAML.Cons.sortP, KoreAML.sym, isNm], by simp [KoreAML.Cons.sortP, KoreAML.sym, isNm],
      cleanN_val t a ht⟩
  | .dv s0 lit, s, hv => by
    obtain ⟨-, rfl⟩ := sortOf_dv.mp hv
    unfold den KoreAML.den
    rw [GroundTerm.kore, KoreAML.tr_dv]
    simp [KoreAML.Cons.sortP, KoreAML.sym, isNm, cleanN, psyms]
  | .map s0 es, s, hv => by
    obtain ⟨k, vs, hco, -, hval, -, hes, rfl⟩ := sortOf_mapS_fwd hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    obtain ⟨hu, he, hc⟩ := valuesN_coll hV hk
    unfold den
    rw [GroundTerm.kore, Semantics.collSig, hco]
    exact cleanN_entries k hu he hc es (cleanN_ents es fun e he' =>
      ⟨⟨k.key, (entriesOK_iff.mp hes e he').1⟩, ⟨vs, (entriesOK_iff.mp hes e he').2⟩⟩)
  | .set s0 es, s, hv => by
    obtain ⟨k, hco, -, -, hes, rfl⟩ := sortOf_setS.mp hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    obtain ⟨hu, he, hc⟩ := valuesN_coll hV hk
    unfold den
    rw [GroundTerm.kore, Semantics.collSig, hco]
    exact cleanN_elems k hu he hc es (cleanN_all es fun e he' => ⟨k.key, hes e he'⟩)
  | .list s0 es, s, hv => by
    obtain ⟨k, hco, -, hes, rfl⟩ := sortOf_listS.mp hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    obtain ⟨hu, he, hc⟩ := valuesN_coll hV hk
    unfold den
    rw [GroundTerm.kore, Semantics.collSig, hco]
    exact cleanN_elems k hu he hc es (cleanN_all es fun e he' => ⟨k.key, hes e he'⟩)
  termination_by structural v => v
theorem cleanN_all : ∀ (vs : List GroundTerm),
    (∀ v ∈ vs, ∃ s, c.sortOf v = some s) → ∀ v ∈ vs, cleanN ns (den c v) = true
  | [], _, v, hv => nomatch hv
  | w :: ws, h, v, hv => by
    rcases List.mem_cons.mp hv with he | hv'
    · obtain ⟨s, h1⟩ := h w (List.mem_cons_self ..)
      rw [he]; exact cleanN_val w s h1
    · exact cleanN_all ws (fun x hx => h x (List.mem_cons_of_mem _ hx)) v hv'
  termination_by structural vs => vs
theorem cleanN_ents : ∀ (es : List (GroundTerm × GroundTerm)),
    (∀ e ∈ es, (∃ s, c.sortOf e.1 = some s) ∧ (∃ s, c.sortOf e.2 = some s)) →
    ∀ e ∈ es, cleanN ns (den c e.1) = true ∧ cleanN ns (den c e.2) = true
  | [], _, e, he => nomatch he
  | e0 :: es, h, e, he => by
    rcases List.mem_cons.mp he with he0 | he'
    · rw [he0]; exact cleanN_ent e0 (h e0 (List.mem_cons_self ..))
    · exact cleanN_ents es (fun x hx => h x (List.mem_cons_of_mem _ hx)) e he'
  termination_by structural es => es
theorem cleanN_ent : ∀ (e : GroundTerm × GroundTerm),
    ((∃ s, c.sortOf e.1 = some s) ∧ (∃ s, c.sortOf e.2 = some s)) →
    cleanN ns (den c e.1) = true ∧ cleanN ns (den c e.2) = true
  | (x, v), h => by
    obtain ⟨⟨s, h1⟩, ⟨s', h1'⟩⟩ := h
    exact ⟨cleanN_val x s h1, cleanN_val v s' h1'⟩
  termination_by structural e => e
end

/-- A graph's premise holds none of the names: the application of a symbol outside the names at
values, equal to a pattern that holds none. -/
theorem cleanN_graph {f : Sym} {vs : List GroundTerm} {ts : List Srt} {ρ : KoreAML.P}
    (hf : appOKN c ns f = true) (hvs : c.sortsOf vs = some ts) (hρ : cleanN ns ρ = true) :
    cleanN ns (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ ρ) = true := by
  rw [cleanN_eq, cleanN_symApp f _ hf (fun p hp => by
    rw [DetachedB.koreList_map] at hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    obtain ⟨s, -, h'⟩ := DetachedB.sortsOf_mem hvs v hv
    exact cleanN_val hV v s h'), Bool.true_and]
  exact hρ

end Values

end NameFree

open NameFree in
/-- **No premise of the theory holds the symbol of a name of `ns`** where `nameFreeB` holds: the
`hfree` premise of `model_with_eqns` at the names `ns`. -/
theorem nameFree_of_decided (c : Semantics) (ns : List String) (h : c.coreOK = true)
    (hd : nameFreeB c ns = true) :
    ∀ n, n ∈ ns → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ := by
  simp only [nameFreeB, Bool.and_eq_true] at hd
  obtain ⟨⟨hL, hV⟩, hG⟩ := hd
  simp only [graphsN, Bool.and_eq_true, List.all_eq_true] at hG
  obtain ⟨⟨hGh, hGp⟩, hGf⟩ := hG
  simp only [listsN, Bool.and_eq_true, List.all_eq_true] at hL
  obtain ⟨⟨hLi, hLc⟩, hLb⟩ := hL
  intro n hn φ hφ
  have hclean : ∀ {ψ : KoreAML.P}, ψ = φ → cleanN ns ψ = true → KoreAML.Sym.symbol n ∉ psyms φ :=
    fun he hc => he ▸ cleanN_spec hc hn
  have hdef : ∀ x : EVar, cleanN ns (@definedness KoreAML.Sym _ x) = true := fun x => by
    simp [definedness, Pattern.universal, Pattern.negation]
  rcases hφ with hφ | hφ
  rotate_left
  · exact hclean hφ.symm (hLi _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  rcases hφ with hφ | hφ
  rotate_left
  · exact hclean hφ.2.2.symm hLb
  rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
  · -- the signature
    rcases hφ with (⟨it, hit, rfl⟩ | ⟨x, rfl⟩) | ⟨lit, rfl⟩
    · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hit)))))
    · exact hclean rfl (hdef x)
    · exact hclean rfl (by
        simp [KoreAML.dvArityItem, KoreAML.guarded, KoreAML.conjList, KoreAML.sortGuard, ML.member, ML.included,
          ML.total, Pattern.negation, Pattern.conjunction, Pattern.disjunction, KoreAML.sortsDomain,
          KoreAML.inhOf, KoreAML.sym, isNm])
  · -- the constructors
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hit)))))
    · exact hclean rfl (hdef x)
  · -- the domains
    rcases hφ with ⟨k, vs, r, hk, hvs, hr, hsil, rfl⟩ | ⟨k, vs, hk, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ |
      ⟨v, w, s, hds, hv, hw, hne, rfl⟩ | ⟨k, hk, rfl⟩
    · refine hclean rfl (cleanN_graph hV (hGh k hk) hvs ?_)
      cases r with
      | none => rfl
      | some v =>
        exact cleanN_val hV v _ (hook_sorted (fun _ => rangeBelow_of_core h) (hookSigs_lookup k hk) hvs hr)
    · refine hclean rfl (cleanN_graph hV (hGp k hk) hvs ?_)
      cases hpv : c.paramVal k.sig.name vs with
      | none => rfl
      | some v =>
        obtain ⟨k', -, hs'⟩ := c.paramVal_sorted hpv
        exact cleanN_val hV v _ hs'
    · refine hclean rfl ?_
      rw [cleanN_sExists, cleanN_eq, cleanN_val hV v s hv]
      simp
    · refine hclean rfl ?_
      rw [cleanN_neg, cleanN_and, cleanN_val hV v s hv, cleanN_val hV w s hw]; rfl
    · exact hclean rfl (hLc k hk).1
  · -- the collections
    obtain ⟨k, hk, hmem⟩ := hφ
    exact hclean rfl ((hLc k hk).2 φ hmem)
  · -- the functions
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hit))))
    · exact hclean rfl (hdef x)
  · -- the rules
    rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
    · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_right _ hit)))
    · exact hclean rfl (hdef x)
  · -- the fallbacks
    rcases hφ with ⟨k, vs, hk, hvs, hr, hsil, rfl⟩ | ⟨fn, vs, hfn, hvs, -, rfl⟩
    · refine hclean rfl (cleanN_graph hV (hGh k hk) hvs ?_)
      cases hfb : c.fallback k.name vs with
      | none => rfl
      | some v => exact cleanN_val hV v _ (c.fallback_sorted (hookSigs_lookup k hk) hfb)
    · refine hclean rfl (cleanN_graph hV (hGf fn hfn) hvs ?_)
      cases hfr : c.fnRest fn vs with
      | none => rfl
      | some v => exact cleanN_val hV v _ (Semantics.fnRest_sorted hfr)

/-! ## The model of a choice among instances -/

open Faithful.Model

/-- **The theory with the equations of symbols it does not name has a model whose steps are any
choice among instances.** For a semantics that `coreOK` accepts under `FnHyp`, names `N` no
premise names that resolve to no constant, partial functions `G n` on values, and a transition `T`
meeting `has_model_choice`'s conditions (it holds only steps of `Step`, every step of a rule
without existential variables, and for each application of a rule with existential variables one
of its instances): an interpretation that satisfies `Γc c` with the step's closure, in which
`n(w) = v` holds wherever `G n w = some v` at values of a sort, and whose steps at configurations
are `T`. -/
theorem model_with_eqns_choice (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (N : String → Prop)
    (G : String → GroundTerm → Option GroundTerm) (hr : rootedListsB c = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ)
    (hsym : ∀ n, N n → spareSymB c n = true)
    (T : Config c → Config c → Prop)
    (hsub : ∀ x y, T x y → Step c x y)
    (hall : ∀ x y r σ, StepBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ x y r σ, StepBy c r σ x y → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepBy c r σ' x y' ∧ T x y') :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ n, N n → ∀ (w v : GroundTerm) (s s' : Srt), c.sortOf w = some s → c.sortOf v = some s' →
        G n w = some v → I ⊧ᴵ (symP n ⬝ den c w ≡ den c v)) ∧
      ∀ x y : Config c, T x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) := by
  have hm := hypModel_of_fnHyp h hf
  have hfd := (fnModel_of_fnHyp h hf).1
  have hrules := Semantics.ruleFactsHeld_of_core h
  have hsr : ∀ r ∈ c.rules, c.ruleSorted r = true := fun r hr => (hrules r hr).1
  have hI : stdI_T c (liftT_ex c T) ⊧ᴵP (Γc c ∪ Γstep c) := by
    refine stdI_T_model_held c h hm (clausePreDecided_of_fnHyp h hf) hf.2.2.2.2.2 hrules (liftT_ex c T) ?_ ?_ ?_
    · intro x y hx hy hT
      obtain ⟨r, σ, hb⟩ := step_iff_by.mp (hsub ⟨x, hx⟩ ⟨y, hy⟩ (hT hx hy))
      exact ⟨r, σ, stepVBy_of_stepBy hfd hb⟩
    · intro r σ x y hb hex hx hy
      exact hall ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb) hex
    · intro r σ x y hb _
      by_cases hx : c.sortOf x = some topCellSort
      · have hy := rhs_sorted_open hm (hrules r hb.1).1 hb.2.1 hb.2.2.2.2.2.1
        obtain ⟨y', σ', hag, hb', hT⟩ :=
          hsome ⟨x, hx⟩ ⟨y, hy⟩ r σ (stepBy_of_stepVBy (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h hfd hf.1 hsr hb)
        exact ⟨y'.val, σ', hag, stepVBy_of_stepBy hfd hb', fun _ _ => hT⟩
      · exact ⟨y, σ, fun _ _ => rfl, hb, fun hx' => absurd hx' hx⟩
  refine ⟨stdPatch c (liftT_ex c T) N (valApp G), stdPatch_model c _ N _ hr hfree hI,
    fun n hN w v s s' hw hv hg => stdPatch_eqn c _ N G hr hfree hI (AtT.denGoal hm) hN (hsym n hN) hw hv hg,
    fun x y => ?_⟩
  rw [stdPatch_step c _ N _ hfree x y]
  exact (liftT_ex_iff T x y).symm.trans (step_iff_stdI_T c hm _ x y)

/-- **At the semantics' own steps**: `model_with_eqns_choice` at `T := Step c`, every instance kept. -/
theorem model_with_eqns_step (c : Semantics) (h : c.coreOK = true) (hf : FnHyp c) (N : String → Prop)
    (G : String → GroundTerm → Option GroundTerm) (hr : rootedListsB c = true)
    (hfree : ∀ n, N n → ∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ)
    (hsym : ∀ n, N n → spareSymB c n = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ n, N n → ∀ (w v : GroundTerm) (s s' : Srt), c.sortOf w = some s → c.sortOf v = some s' →
        G n w = some v → I ⊧ᴵ (symP n ⬝ den c w ≡ den c v)) ∧
      ∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  model_with_eqns_choice c h hf N G hr hfree hsym (Step c) (fun _ _ hs => hs)
    (fun _ _ r σ hb _ => step_iff_by.mpr ⟨r, σ, hb⟩)
    (fun _ y r σ hb => ⟨y, σ, fun _ _ => rfl, hb, step_iff_by.mpr ⟨r, σ, hb⟩⟩)

/-! ## A name no symbol bears -/

/-- A nonempty name that is no registry symbol's and none of the semantics' own is the name of no
numbered symbol. -/
theorem getD_mem_of_ne {l : List String} {i : Nat} {n : String} (h : l.getD i "" = n) (he : n ≠ "") :
    n ∈ l := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hg : l[i]? with
  | none => rw [hg] at h; exact absurd h.symm he
  | some x =>
    rw [hg, Option.getD_some] at h
    subst h
    exact List.mem_of_getElem? hg

theorem symName_ne_of_unnumbered (c : Semantics) {n : String}
    (hn : (regSymNames ++ c.symNames).contains n = false) (he : n ≠ "") (f : Sym) : c.symName f ≠ n := by
  intro h
  have hm : n ∈ regSymNames ++ c.symNames := by
    unfold Semantics.symName at h
    split at h
    · exact List.mem_append_left _ (getD_mem_of_ne h he)
    · exact List.mem_append_right _ (getD_mem_of_ne h he)
  rw [List.contains_iff_mem.mpr hm] at hn
  cases hn

/-- **A name no symbol bears resolves to no constant** (`spareSymB`): it is not `inj`'s, and no
symbol of `kernelSyms` has it. -/
theorem spareSymB_of_unnumbered (c : Semantics) {n : String}
    (hn : (regSymNames ++ c.symNames).contains n = false) (he : n ≠ "") (hi : n ≠ "inj") :
    spareSymB c n = true := by
  have hres : resolve c n [] = none := by
    unfold resolve
    split
    · rename_i h; cases h
    · rw [Option.map_eq_none_iff, List.find?_eq_none]
      intro k _ hk
      exact symName_ne_of_unnumbered c hn he k.name (beq_iff_eq.mp hk)
  simp only [spareSymB, hres, Bool.and_true]
  exact bne_iff_ne.mpr hi

/-- **A constructor argument's projection that the account's arm accepts resolves to no
constant**: a name with the prefix `Lblproject'Coln` that is no registry symbol's and none of the
semantics' own (the conditions `Account.genEqClassOK` checks of it) meets `spareSymB`, the premise
`hsym` of `model_with_eqns_choice` and `model_with_eqns_step`. -/
theorem spareSymB_of_argProj (c : Semantics) {n : String}
    (hp : (KoreAML.Parse.dropPrefix? "Lblproject'Coln" n).isSome = true)
    (hr : regSymNames.contains n = false) (hs : c.symNames.contains n = false) : spareSymB c n = true := by
  refine spareSymB_of_unnumbered c (by rw [List.contains_append, hr, hs]; rfl) ?_ ?_
  · rintro rfl; revert hp; decide
  · rintro rfl; revert hp; decide

end GenEqs

end KCore
