/-
  A decided form of `Detached`: `detachedB c ss ks` for lists of registry sorts `ss` and of
  interpreted hooked symbols `ks`, and `detached_of_decided`: where it is true, the names of `ss`
  and `ks` (`detachedNames`) are detached from `c`.

  The check has two parts. The parts of the theory that are lists (the signature's items, the
  constructor items, the function and rule items, the step's closure, the collections' no-junk
  items and axioms, `boolClosed`) are read item by item: no symbol of an item is a detached name,
  or the item is the sort constant of a sort of `ss`, the arity of a hook of `ks`, or the no-junk
  item of a library collection whose sort is in `ss`. The parts that are stated at every value (the
  graphs, the fallbacks, the value items, distinctness) are covered by the signatures: no symbol
  that builds a value of a sort outside `ss` and no sort such a value holds has a detached name, so
  a value's pattern names none; and a hook outside `ks`, a parameter symbol and a function have no
  detached name and no sort of a detached name in their signature.
-/
import KcoreSpec.RegistryOwn
import KcoreSpec.HypWf
import KcoreSpec.ModelDen

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace DetachedB

variable (c : Semantics) (ss : List Srt) (ks : List Sym)

/-- The names of the sorts `ss` and of the symbols `ks`, as symbols of the theory. -/
def names : KoreAML.Sym → Prop := fun σ =>
  (∃ s ∈ ss, σ = .sort ("Sort" ++ c.sortName s)) ∨ (∃ k ∈ ks, σ = .symbol (c.symName k))

/-- `names`, decided. -/
def isName : KoreAML.Sym → Bool
  | .sort n => ss.any fun s => "Sort" ++ c.sortName s == n
  | .symbol n => ks.any fun k => c.symName k == n
  | _ => false

/-- No symbol of the pattern is one of the names. -/
def clean (φ : KoreAML.P) : Bool := (psyms φ).all fun σ => !isName c ss ks σ

/-- The sort's name is none of the names. -/
def sOK (s : Srt) : Bool := !isName c ss ks (.sort ("Sort" ++ c.sortName s))

/-- The symbol's name is none of the names. -/
def kOK (f : Sym) : Bool := !isName c ss ks (.symbol (c.symName f))

/-- The head `symApp` writes for `f` names none of the names. -/
def appOK (f : Sym) : Bool :=
  match iteSort? (c.symName f) with
  | some X => !isName c ss ks (.symbol "Lblite") && !isName c ss ks (.sort ("Sort" ++ X))
  | none => kOK c ss ks f

/-- The values of a sort outside the names are built from symbols and sorts outside the names:
constructors, overloading symbols and parameter symbols with their argument sorts, both sorts of
a subsort pair, the injection, and the symbols and entry sorts of a collection sort outside the
names. -/
def valuesB : Bool :=
  (c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig)).all (fun k => kOK c ss ks k.name && k.args.all (sOK c ss ks)) &&
  c.subsorts.all (fun p => sOK c ss ks p.1 && sOK c ss ks p.2) &&
  c.allColls.all (fun k => !sOK c ss ks k.sort ||
    (kOK c ss ks k.unit && kOK c ss ks k.elem && kOK c ss ks k.concat && sOK c ss ks k.key &&
      k.val.all (sOK c ss ks))) &&
  !isName c ss ks (.symbol "inj")

/-- The symbols the theory applies at values have no name among the names and no sort of such a
name in their signature: a hook outside `ks`, a parameter symbol, a function; and a hook of `ks`
is an interpreted hooked symbol. -/
def graphsB : Bool :=
  hookSigs.all (fun k => !kOK c ss ks k.name ||
    (appOK c ss ks k.name && (k.result :: k.args).all (sOK c ss ks))) &&
  c.params.all (fun k => appOK c ss ks k.sig.name && (k.sig.result :: k.sig.args).all (sOK c ss ks)) &&
  c.allFns.all (fun f => appOK c ss ks f.label && (f.result :: f.args).all (sOK c ss ks))

/-- A sort with one of the names is a sort of `ss`: every numbered sort outside `ss` has another
name, and so has the empty name, which a sort without a number has. -/
def sortsB : Bool :=
  ss.all (fun s => decide (s < nRegSorts)) &&
  (kernelSorts c).all (fun s => sOK c ss ks s || ss.contains s) &&
  !isName c ss ks (.sort ("Sort" ++ ""))

/-- The item is the sort constant of a sort of `ss` or the arity of a hook of `ks`. -/
def regSig (φ : KoreAML.P) : Bool :=
  ss.any (fun s => φ == (KoreAML.sortConstantItem (sortDeclOf c s)).pat) ||
  hookSigs.any (fun h => ks.contains h.name && φ == (symArityItem c h).pat)

/-- `consItemsK c` with the subsorts `sub`, the order `le` and the common lower bounds `lb` as
arguments: at `c.subsorts`, `c.le` and `c.lowerBounds` it is `consItemsK c`
(`consItemsK_eq_withCdp`). -/
def consItemsKWithCdp (sub : List (Srt × Srt)) (le : Srt → Srt → Bool) (lb : Srt → Srt → List Srt) :
    List KoreAML.Item :=
  let n := c.sortName
  let ovlArgs := fun (g : Gen) => match g with
    | .ctor k => if c.isOvl k.name then (c.lookupOvl k.name).map fun o => (c.ovlOver o).map fun kg => kg.args.map n
      else none
    | .inj _ => none
  let perSort := (consSorts c).flatMap fun N =>
    let gs := c.gens N
    let fr := gs.filter (!c.isOpenGen ·)
    (fr.map fun g =>
      if c.fnOvl g then KoreAML.Cons.funUncItem (n N) (Gen.toK c g) ((ovlArgs g).getD [])
      else KoreAML.Cons.funItem (n N) (Gen.toK c g)) ++
    ((fr.filter fun g => !(Gen.toK c g).argSorts.isEmpty).map fun g =>
      if c.fnOvl g then KoreAML.Cons.injUncItem (n N) (Gen.toK c g) ((ovlArgs g).getD [])
      else KoreAML.Cons.injItem (n N) (Gen.toK c g)) ++
    (pairs fr).flatMap (fun (g, g') => match g, g' with
      | .inj a, .inj b =>
        if le a b || le b a then []
        else match lb a b with
          | [] => [KoreAML.Cons.distItem (n N) (Gen.toK c g) (Gen.toK c g')]
          | lbs => [distLbItem (n N) (n a) (n b) (lbs.map n)]
      | _, _ =>
        if c.distGuarded g g' then
          [KoreAML.Cons.distUncItem (n N) (Gen.toK c g) (Gen.toK c g') (ovlArgs g) (ovlArgs g')]
        else [KoreAML.Cons.distItem (n N) (Gen.toK c g) (Gen.toK c g')]) ++
    (if gs.isEmpty then [] else [KoreAML.Cons.noJunkItem (n N) (gs.map (Gen.toK c))])
  let coh := sub.flatMap fun (a, b) =>
    (sub.filter (·.1 == b)).map fun (_, e) => KoreAML.Cons.cohItem (n a) (n b) (n e)
  let ovlEqs := c.ovls.flatMap fun o => (c.ovlOver o).map fun kg => KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg)
  perSort ++ coh ++ ovlEqs ++ lawItemsK c

theorem consItemsK_eq_withCdp : consItemsK c = consItemsKWithCdp c c.subsorts c.le c.lowerBounds := rfl

/-- `consItemsK c` computed with `c.subsorts`, its first sorts and each sort's supersorts
(`NatMap.group`) built once per call, where `Semantics.le` and `Semantics.lowerBounds` build the
subsorts again at each comparison (`lowerBounds` at each sort it tries). The compiled code computes
`consItemsK` as it (`consItemsK_eq_fastCdp`), so that `listsB` and the code after it here read
`consItemsK` at that cost. -/
def consItemsKFastCdp : List KoreAML.Item :=
  let sub := c.subsorts
  let up := NatMap.group sub
  let cands := (sub.map (·.1)).eraseDups
  consItemsKWithCdp c sub (fun a b => a == b || (NatMap.succs up a).contains b)
    (fun a b => sortBy id (cands.filter fun s => (NatMap.succs up s).contains a && (NatMap.succs up s).contains b))

/-- `consItemsKFastCdp` is `consItemsK`: the supersorts trie holds exactly the subsort pairs
(`NatMap.mem_group`). -/
@[csimp] theorem consItemsK_eq_fastCdp : @consItemsK = @consItemsKFastCdp := by
  funext c
  have hup : ∀ a b, (NatMap.succs (NatMap.group c.subsorts) a).contains b = c.subsorts.contains (a, b) := by
    intro a b
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, NatMap.mem_group]
  have hle : (fun a b => a == b || (NatMap.succs (NatMap.group c.subsorts) a).contains b) = c.le := by
    funext a b; simp only [hup, Semantics.le]
  have hlb : (fun a b => sortBy id (((c.subsorts.map (·.1)).eraseDups).filter fun s =>
      (NatMap.succs (NatMap.group c.subsorts) s).contains a &&
        (NatMap.succs (NatMap.group c.subsorts) s).contains b)) = c.lowerBounds := by
    funext a b; simp only [hup, Semantics.lowerBounds]
  show consItemsK c = consItemsKWithCdp c c.subsorts _ _
  rw [hle, hlb]
  exact consItemsK_eq_withCdp c

/-- The parts of the theory that are lists. -/
def listsB : Bool :=
  (sigItems c).all (fun it => clean c ss ks it.pat || regSig c ss ks it.pat) &&
  (consItemsK c ++ fnItems c ++ ruleItems c ++ [stepClosureItem c]).all (fun it => clean c ss ks it.pat) &&
  c.allColls.all (fun k =>
    if builtinColls.contains k && ss.contains k.sort then (collAxioms c k).isEmpty
    else clean c ss ks (collNoJunk c k) && (collAxioms c k).all (clean c ss ks)) &&
  clean c ss ks (boolClosed c)

end DetachedB

open DetachedB in
/-- **`Detached`, decided**, for registry sorts `ss` and interpreted hooked symbols `ks`: every
symbol of `ks` is an interpreted hooked symbol and every sort with a name of `ss` is a registry
sort of `ss` (`sortsB`); no library collection with axioms has its sort in `ss`; each item of the
theory's lists names none of them or is the registry's own (`listsB`); the values of the other
sorts (`valuesB`) and the symbols applied at values (`graphsB`) name none of them. -/
def detachedB (c : Semantics) (ss : List Srt) (ks : List Sym) : Bool :=
  sortsB c ss ks && ks.all (fun k => hookSigs.any (·.name == k)) &&
  builtinColls.all (fun k => sOK c ss ks k.sort || (collAxioms c k).isEmpty) &&
  listsB c ss ks && valuesB c ss ks && graphsB c ss ks

namespace DetachedB

variable {c : Semantics} {ss : List Srt} {ks : List Sym}

theorem isName_iff {σ : KoreAML.Sym} : isName c ss ks σ = true ↔ names c ss ks σ := by
  unfold names
  cases σ
  case sort n =>
    simp only [isName, List.any_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact .inl ⟨s, hs, rfl⟩
    · rintro (⟨s, hs, he⟩ | ⟨k, hk, he⟩)
      · exact ⟨s, hs, (KoreAML.Sym.sort.inj he).symm⟩
      · cases he
  case symbol n =>
    simp only [isName, List.any_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact .inr ⟨k, hk, rfl⟩
    · rintro (⟨s, hs, he⟩ | ⟨k, hk, he⟩)
      · cases he
      · exact ⟨k, hk, (KoreAML.Sym.symbol.inj he).symm⟩
  all_goals
    exact ⟨fun h => Bool.noConfusion (show false = true from h),
      by rintro (⟨s, hs, he⟩ | ⟨k, hk, he⟩) <;> cases he⟩

/-! ## Patterns without a name -/

@[simp] theorem clean_symbol (σ : KoreAML.Sym) : clean c ss ks (.symbol σ) = !isName c ss ks σ := by
  simp [clean, psyms]
@[simp] theorem clean_app (a b : KoreAML.P) : clean c ss ks (a ⬝ b) = (clean c ss ks a && clean c ss ks b) := by
  simp [clean, psyms, List.all_append]
@[simp] theorem clean_imp (a b : KoreAML.P) : clean c ss ks (a ⇒ b) = (clean c ss ks a && clean c ss ks b) := by
  simp [clean, psyms, List.all_append]
@[simp] theorem clean_ex (x : EVar) (a : KoreAML.P) : clean c ss ks (.existential x a) = clean c ss ks a := by
  simp [clean, psyms]
@[simp] theorem clean_mu (X : SVar) (a : KoreAML.P) : clean c ss ks (.mu X a) = clean c ss ks a := by
  simp [clean, psyms]
@[simp] theorem clean_bot : clean c ss ks (⊥ : KoreAML.P) = true := rfl
@[simp] theorem clean_evar (x : EVar) : clean c ss ks (.evar x : KoreAML.P) = true := rfl
@[simp] theorem clean_svar (X : SVar) : clean c ss ks (.svar X : KoreAML.P) = true := rfl
@[simp] theorem isName_defined : isName c ss ks (HasDefined.defined : KoreAML.Sym) = false := rfl

theorem clean_spec {φ : KoreAML.P} (h : clean c ss ks φ = true) : ¬ ∃ σ ∈ psyms φ, names c ss ks σ := by
  rintro ⟨σ, hσ, hn⟩
  have := List.all_eq_true.mp h σ hσ
  rw [isName_iff.mpr hn] at this
  exact absurd this (by decide)

theorem clean_appList : ∀ (φs : List KoreAML.P) (h : KoreAML.P),
    clean c ss ks (KoreAML.appList h φs) = (clean c ss ks h && φs.all (clean c ss ks))
  | [], h => by simp [KoreAML.appList]
  | φ :: φs, h => by simp [KoreAML.appList, clean_appList φs, Bool.and_assoc]

theorem clean_eq (a b : KoreAML.P) : clean c ss ks (a ≡ b) = (clean c ss ks a && clean c ss ks b) := by
  simp only [ML.equal, ML.total, Pattern.equivalence, Pattern.conjunction, Pattern.disjunction, Pattern.negation,
    clean_app, clean_imp, clean_symbol, clean_bot, isName_defined]
  cases clean c ss ks a <;> cases clean c ss ks b <;> rfl

theorem clean_neg (a : KoreAML.P) : clean c ss ks (∼a) = clean c ss ks a := by
  simp [Pattern.negation]

theorem clean_and (a b : KoreAML.P) : clean c ss ks (a ⋀ b) = (clean c ss ks a && clean c ss ks b) := by
  simp only [Pattern.conjunction, Pattern.disjunction, Pattern.negation, clean_imp, clean_bot]
  cases clean c ss ks a <;> cases clean c ss ks b <;> rfl

theorem clean_sortP (n : String) : clean c ss ks (sortP n) = !isName c ss ks (.sort ("Sort" ++ n)) := by
  simp [sortP, KoreAML.sym]

theorem clean_sExists (x : EVar) (n : String) (a : KoreAML.P) :
    clean c ss ks (KoreAML.sExists x (sortP n) a) = (!isName c ss ks (.sort ("Sort" ++ n)) && clean c ss ks a) := by
  simp only [KoreAML.sExists, clean_ex, clean_and, ML.member, clean_app, clean_symbol, isName_defined,
    clean_evar, KoreAML.inhOf, KoreAML.sym, clean_sortP, isName]
  simp

theorem clean_ap (f : String) (ps : List Kore.Pattern) :
    clean c ss ks (KoreAML.den (KoreAML.ap f ps)) =
      (!isName c ss ks (.symbol f) && ps.all fun p => clean c ss ks (KoreAML.den p)) := by
  unfold KoreAML.den
  rw [Model.tr_ap, clean_appList]
  simp [KoreAML.sym, List.all_map, Function.comp_def]

theorem clean_symApp (f : Sym) (ps : List Kore.Pattern) (hf : appOK c ss ks f = true)
    (hps : ∀ p ∈ ps, clean c ss ks (KoreAML.den p) = true) :
    clean c ss ks (KoreAML.den (symApp c f ps)) = true := by
  unfold symApp
  unfold appOK at hf
  cases hi : iteSort? (c.symName f) with
  | none =>
    rw [hi] at hf
    exact (clean_ap (c := c) (ss := ss) (ks := ks) (c.symName f) ps).trans
      (by rw [show (!isName c ss ks (.symbol (c.symName f))) = true from hf, Bool.true_and]
          exact List.all_eq_true.mpr hps)
  | some X =>
    rw [hi] at hf
    simp only [Bool.and_eq_true] at hf
    show clean c ss ks (KoreAML.tr ⟨[], []⟩ (.app ⟨⟨"Lblite"⟩⟩ [KoreAML.srt X] ps)) = true
    rw [KoreAML.tr]
    simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte, KoreAML.trSortApp, KoreAML.srt,
      KoreAML.trSort_const, trArgs_appList, clean_appList, clean_app, KoreAML.sym, clean_symbol,
      Bool.and_eq_true, List.all_map, List.all_eq_true]
    exact ⟨⟨hf.1, hf.2⟩, fun p hp => hps p hp⟩

/-! ## The values of a sort without a name -/

theorem sortsOf_mem {vs : List GroundTerm} : ∀ {ts : List Srt}, c.sortsOf vs = some ts →
    ∀ v ∈ vs, ∃ s ∈ ts, c.sortOf v = some s := by
  induction vs with
  | nil => intro _ _ v hv; cases hv
  | cons w ws ih =>
    intro ts h v hv
    obtain ⟨s, ss', hw, hws, rfl⟩ := sortsOf_cons.mp h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨s, List.mem_cons_self .., hw⟩
    · obtain ⟨s', hs', h'⟩ := ih hws v hv
      exact ⟨s', List.mem_cons_of_mem _ hs', h'⟩

theorem koreList_map : ∀ vs : List GroundTerm, GroundTerm.koreList c vs = vs.map (GroundTerm.kore c)
  | [] => by rw [GroundTerm.koreList]; rfl
  | v :: vs => by rw [GroundTerm.koreList, koreList_map vs]; rfl

/-- A collection of elements: clean where its symbols and its elements are. -/
theorem clean_elems (k : CollSig) (hu : kOK c ss ks k.unit = true) (he : kOK c ss ks k.elem = true)
    (hc : kOK c ss ks k.concat = true) : ∀ es : List GroundTerm,
    (∀ e ∈ es, clean c ss ks (den c e) = true) →
    clean c ss ks (KoreAML.den (GroundTerm.koreElems c k es)) = true
  | [], _ => by rw [GroundTerm.koreElems, clean_ap]; simpa [kOK] using hu
  | [e], h => by
    rw [GroundTerm.koreElems, clean_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOK] using he, h e (List.mem_cons_self ..)⟩
  | e :: e' :: es, h => by
    rw [GroundTerm.koreElems, clean_ap]
    case x_1 => exact fun h => nomatch h
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨by simpa [kOK] using hc, ?_, clean_elems k hu he hc (e' :: es) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    rw [clean_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOK] using he, h e (List.mem_cons_self ..)⟩

/-- A collection of entries: clean where its symbols and its entries' parts are. -/
theorem clean_entries (k : CollSig) (hu : kOK c ss ks k.unit = true) (he : kOK c ss ks k.elem = true)
    (hc : kOK c ss ks k.concat = true) : ∀ es : List (GroundTerm × GroundTerm),
    (∀ e ∈ es, clean c ss ks (den c e.1) = true ∧ clean c ss ks (den c e.2) = true) →
    clean c ss ks (KoreAML.den (GroundTerm.koreEntries c k es)) = true
  | [], _ => by rw [GroundTerm.koreEntries, clean_ap]; simpa [kOK] using hu
  | [(x, v)], h => by
    rw [GroundTerm.koreEntries, GroundTerm.koreEntry, clean_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOK] using he, (h _ (List.mem_cons_self ..)).1, (h _ (List.mem_cons_self ..)).2⟩
  | (x, v) :: e' :: es, h => by
    rw [GroundTerm.koreEntries, GroundTerm.koreEntry, clean_ap]
    case x_1 => exact fun h => nomatch h
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨by simpa [kOK] using hc, ?_,
      clean_entries k hu he hc (e' :: es) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    rw [clean_ap]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [kOK] using he, (h _ (List.mem_cons_self ..)).1, (h _ (List.mem_cons_self ..)).2⟩

section Values

variable (hV : valuesB c ss ks = true)
include hV

theorem valuesB_sig {k : CtorSig} (hk : k ∈ c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig)) :
    kOK c ss ks k.name = true ∧ ∀ s ∈ k.args, sOK c ss ks s = true := by
  simp only [valuesB, Bool.and_eq_true, List.all_eq_true] at hV
  exact hV.1.1.1 k hk

theorem valuesB_sub {a b : Srt} (h : (a, b) ∈ c.subsorts) : sOK c ss ks a = true ∧ sOK c ss ks b = true := by
  simp only [valuesB, Bool.and_eq_true, List.all_eq_true] at hV
  exact hV.1.1.2 (a, b) h

theorem valuesB_coll {k : CollSig} (hk : k ∈ c.allColls) (hs : sOK c ss ks k.sort = true) :
    kOK c ss ks k.unit = true ∧ kOK c ss ks k.elem = true ∧ kOK c ss ks k.concat = true ∧
      sOK c ss ks k.key = true ∧ ∀ v, k.val = some v → sOK c ss ks v = true := by
  simp only [valuesB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hV
  rcases hV.1.2 k hk with h | h
  · rw [hs] at h; cases h
  · exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, fun v hv => by
      have := h.2; rw [hv] at this; simpa using this⟩

theorem valuesB_inj : isName c ss ks (.symbol "inj") = false := by
  simp only [valuesB, Bool.and_eq_true, Bool.not_eq_true'] at hV
  exact hV.2

mutual
/-- **A value of a sort without a name names none.** -/
theorem clean_val : ∀ (v : GroundTerm) (s : Srt), c.sortOf v = some s → sOK c ss ks s = true →
    clean c ss ks (den c v) = true
  | .ctor f ts, s, hv, _ => by
    have key : ∀ k : CtorSig, k ∈ c.ctorSigs ++ c.ovlSigs ++ c.params.map (·.sig) → k.name = f →
        c.sortsOf ts = some k.args → clean c ss ks (den c (.ctor f ts)) = true := by
      intro k hk hn hts
      obtain ⟨h1, h2⟩ := valuesB_sig hV hk
      rw [den_ctor, trArgs_appList, clean_appList, koreList_map, ← hn]
      simp only [KoreAML.sym, clean_symbol, Bool.and_eq_true, List.all_map, List.all_eq_true]
      refine ⟨by simpa [kOK] using h1, fun t ht => ?_⟩
      exact clean_all ts (fun t ht => by
        obtain ⟨s', hs', h'⟩ := sortsOf_mem hts t ht
        exact ⟨s', h', h2 s' hs'⟩) t ht
    rcases c.sortOf_ctor_iff.mp hv with ⟨k, hk, hts, -⟩ | ⟨-, o, ho, hts, -, -⟩ | ⟨-, -, k, hko, hts, -, -⟩
    · exact key k (List.mem_append_left _ (List.mem_append_left _ (lookupSig_spec hk).1)) (lookupSig_spec hk).2 hts
    · have ho' : c.ovls.find? (·.sig.name == f) = some o := ho
      exact key o.sig (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_of_find?_eq_some ho')))) (by simpa using List.find?_some ho') hts
    · obtain ⟨hm, -, hn, -⟩ := c.lookupOpen_spec hko
      exact key k.sig (List.mem_append_right _ (List.mem_map_of_mem hm)) hn hts
  | .inj a b t, s, hv, _ => by
    obtain ⟨hab, -, ht, -⟩ := sortOf_inj.mp hv
    obtain ⟨ha, hb⟩ := valuesB_sub hV hab
    rw [den_inj, clean_appList]
    simp only [KoreAML.sym, clean_symbol, valuesB_inj hV, Bool.not_false, Bool.true_and, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨by simpa [sOK, KoreAML.Cons.sortP, KoreAML.sym] using ha,
      by simpa [sOK, KoreAML.Cons.sortP, KoreAML.sym] using hb, clean_val t a ht ha⟩
  | .dv s0 lit, s, hv, hs => by
    obtain ⟨-, rfl⟩ := sortOf_dv.mp hv
    unfold den KoreAML.den
    rw [GroundTerm.kore, KoreAML.tr_dv]
    simpa [sOK, KoreAML.Cons.sortP, KoreAML.sym, isName] using hs
  | .map s0 es, s, hv, hs => by
    obtain ⟨k, vs, hco, -, hval, -, hes, rfl⟩ := sortOf_mapS_fwd hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    obtain ⟨hu, he, hc, hkey, hvs⟩ := valuesB_coll hV hk hs
    unfold den
    rw [GroundTerm.kore, Semantics.collSig, hco]
    exact clean_entries k hu he hc es (clean_ents es fun e he' =>
      ⟨⟨k.key, (entriesOK_iff.mp hes e he').1, hkey⟩, ⟨vs, (entriesOK_iff.mp hes e he').2, hvs vs hval⟩⟩)
  | .set s0 es, s, hv, hs => by
    obtain ⟨k, hco, -, -, hes, rfl⟩ := sortOf_setS.mp hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    obtain ⟨hu, he, hc, hkey, -⟩ := valuesB_coll hV hk hs
    unfold den
    rw [GroundTerm.kore, Semantics.collSig, hco]
    exact clean_elems k hu he hc es (clean_all es fun e he' => ⟨k.key, hes e he', hkey⟩)
  | .list s0 es, s, hv, hs => by
    obtain ⟨k, hco, -, hes, rfl⟩ := sortOf_listS.mp hv
    obtain ⟨hk, rfl⟩ := Model.collOf_spec hco
    obtain ⟨hu, he, hc, hkey, -⟩ := valuesB_coll hV hk hs
    unfold den
    rw [GroundTerm.kore, Semantics.collSig, hco]
    exact clean_elems k hu he hc es (clean_all es fun e he' => ⟨k.key, hes e he', hkey⟩)
  termination_by structural v => v
theorem clean_all : ∀ (vs : List GroundTerm),
    (∀ v ∈ vs, ∃ s, c.sortOf v = some s ∧ sOK c ss ks s = true) → ∀ v ∈ vs, clean c ss ks (den c v) = true
  | [], _, v, hv => nomatch hv
  | w :: ws, h, v, hv => by
    rcases List.mem_cons.mp hv with he | hv'
    · obtain ⟨s, h1, h2⟩ := h w (List.mem_cons_self ..)
      rw [he]; exact clean_val w s h1 h2
    · exact clean_all ws (fun x hx => h x (List.mem_cons_of_mem _ hx)) v hv'
  termination_by structural vs => vs
theorem clean_ents : ∀ (es : List (GroundTerm × GroundTerm)),
    (∀ e ∈ es, (∃ s, c.sortOf e.1 = some s ∧ sOK c ss ks s = true) ∧
      (∃ s, c.sortOf e.2 = some s ∧ sOK c ss ks s = true)) →
    ∀ e ∈ es, clean c ss ks (den c e.1) = true ∧ clean c ss ks (den c e.2) = true
  | [], _, e, he => nomatch he
  | e0 :: es, h, e, he => by
    rcases List.mem_cons.mp he with he0 | he'
    · rw [he0]; exact clean_ent e0 (h e0 (List.mem_cons_self ..))
    · exact clean_ents es (fun x hx => h x (List.mem_cons_of_mem _ hx)) e he'
  termination_by structural es => es
theorem clean_ent : ∀ (e : GroundTerm × GroundTerm),
    ((∃ s, c.sortOf e.1 = some s ∧ sOK c ss ks s = true) ∧ (∃ s, c.sortOf e.2 = some s ∧ sOK c ss ks s = true)) →
    clean c ss ks (den c e.1) = true ∧ clean c ss ks (den c e.2) = true
  | (x, v), h => by
    obtain ⟨⟨s, h1, h2⟩, ⟨s', h1', h2'⟩⟩ := h
    exact ⟨clean_val x s h1 h2, clean_val v s' h1' h2'⟩
  termination_by structural e => e
end

/-- The values of sorts without a name, as the arguments of an application. -/
theorem clean_args {vs : List GroundTerm} {ts : List Srt} (h : c.sortsOf vs = some ts)
    (hts : ∀ s ∈ ts, sOK c ss ks s = true) :
    ∀ p ∈ GroundTerm.koreList c vs, clean c ss ks (KoreAML.den p) = true := by
  intro p hp
  rw [koreList_map] at hp
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
  obtain ⟨s, hs, h'⟩ := sortsOf_mem h v hv
  exact clean_val hV v s h' (hts s hs)

/-- A graph's premise names none: the application of a symbol without a name at values of sorts
without a name, equal to a pattern that names none. -/
theorem clean_graph {f : Sym} {vs : List GroundTerm} {ts : List Srt} {ρ : KoreAML.P}
    (hf : appOK c ss ks f = true) (hvs : c.sortsOf vs = some ts) (hts : ∀ s ∈ ts, sOK c ss ks s = true)
    (hρ : clean c ss ks ρ = true) :
    clean c ss ks (KoreAML.den (symApp c f (GroundTerm.koreList c vs)) ≡ ρ) = true := by
  rw [clean_eq, clean_symApp f _ hf (clean_args hV hvs hts), Bool.true_and]
  exact hρ

end Values

end DetachedB

open DetachedB in
/-- **The decided check gives `Detached`** at the names of `ss` and `ks`. -/
theorem detached_of_decided (c : Semantics) (ss : List Srt) (ks : List Sym) (h : c.coreOK = true)
    (hd : detachedB c ss ks = true) : Detached c (DetachedB.names c ss ks) := by
  simp only [detachedB, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨⟨hS, hK⟩, hB⟩, hL⟩, hV⟩, hG⟩ := hd
  simp only [sortsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hS
  obtain ⟨⟨hreg, hnum⟩, hempty⟩ := hS
  simp only [graphsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hG
  obtain ⟨⟨hGh, hGp⟩, hGf⟩ := hG
  simp only [listsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hL
  obtain ⟨⟨⟨hLs, hLi⟩, hLc⟩, hLb⟩ := hL
  -- a sort with a name is a registry sort of `ss`
  have hsort : ∀ s, sOK c ss ks s = false → s < nRegSorts ∧ names c ss ks (.sort ("Sort" ++ c.sortName s)) := by
    intro s hs
    have hn : names c ss ks (.sort ("Sort" ++ c.sortName s)) :=
      isName_iff.mp (by simpa [sOK] using hs)
    by_cases hlt : s < nRegSorts + c.sortNames.length
    · rcases hnum s (List.mem_range.mpr hlt) with h' | h'
      · rw [hs] at h'; cases h'
      · exact ⟨hreg s (List.contains_iff_mem.mp h'), hn⟩
    · exfalso
      have hlt' : ¬ s < nRegSorts := fun h' => hlt (Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _))
      have hge : c.sortNames.length ≤ s - nRegSorts :=
        Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.le_of_not_lt hlt)
      have he : c.sortName s = "" := by
        unfold Semantics.sortName
        simp only [hlt', ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
      unfold sOK at hs
      rw [he, hempty] at hs
      exact absurd hs (by decide)
  have hhook : ∀ k ∈ hookSigs, kOK c ss ks k.name = false →
      k ∈ hookSigs ∧ names c ss ks (.symbol (c.symName k.name)) := fun k hk hn =>
    ⟨hk, isName_iff.mp (by simpa [kOK] using hn)⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro σ (⟨s, hs, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact .inl ⟨s, hreg s hs, rfl⟩
    · obtain ⟨g, hg, hgk⟩ := List.any_eq_true.mp (List.all_eq_true.mp hK k hk)
      exact .inr ⟨g, hg, by rw [beq_iff_eq.mp hgk]⟩
  · intro k hk hn
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hB k hk) with h' | h'
    · have := isName_iff.mpr hn
      simp only [sOK, Bool.not_eq_true'] at h'
      rw [h'] at this; cases this
    · exact List.isEmpty_iff.mp h'
  · intro φ hφ hname
    have hclean : ∀ {ψ : KoreAML.P}, ψ = φ → clean c ss ks ψ = true → RegistryItem c (names c ss ks) φ :=
      fun he hc => absurd (he ▸ hname) (clean_spec hc)
    rcases hφ with hφ | hφ
    rotate_left
    · -- the step's closure
      exact hclean hφ.symm (hLi _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    rcases hφ with hφ | hφ
    rotate_left
    · -- the closure of Bool
      exact hclean hφ.2.2.symm hLb
    rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · -- the signature
      rcases hφ with (⟨it, hit, rfl⟩ | ⟨x, rfl⟩) | ⟨lit, rfl⟩
      · rcases hLs it hit with h' | h'
        · exact hclean rfl h'
        · simp only [regSig, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at h'
          rcases h' with ⟨s, hs, he⟩ | ⟨g, hg, hgk, he⟩
          · exact .inl ⟨s, ⟨hreg s hs, .inl ⟨s, hs, rfl⟩⟩, he⟩
          · exact .inr (.inl ⟨g, ⟨hg, .inr ⟨g.name, List.contains_iff_mem.mp hgk, rfl⟩⟩, he⟩)
      · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
      · exact hclean rfl (by
          simp [KoreAML.dvArityItem, KoreAML.guarded, KoreAML.conjList, KoreAML.sortGuard, ML.member, ML.included,
            ML.total, Pattern.negation, Pattern.conjunction, Pattern.disjunction, KoreAML.sortsDomain,
            KoreAML.inhOf, KoreAML.sym, isName])
    · -- the constructors
      rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
      · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hit))))
      · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
    · -- the domains
      rcases hφ with ⟨k, vs, r, hk, hvs, hr, hsil, rfl⟩ | ⟨k, vs, hk, hvs, rfl⟩ | ⟨v, s, hv, rfl⟩ |
        ⟨v, w, s, hds, hv, hw, hne, rfl⟩ | ⟨k, hk, rfl⟩
      · cases hn : kOK c ss ks k.name with
        | false => exact .inr (.inr (.inl ⟨k, vs, r, hhook k hk hn, hvs, hr, hsil, rfl⟩))
        | true =>
          rcases hGh k hk with h' | h'
          · rw [hn] at h'; cases h'
          · refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
            cases r with
            | none => rfl
            | some v =>
              exact clean_val hV v _ (hook_sorted (fun _ => rangeBelow_of_core h) (hookSigs_lookup k hk) hvs hr)
                (h'.2 _ (List.mem_cons_self ..))
      · have h' := hGp k hk
        refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
        cases hpv : c.paramVal k.sig.name vs with
        | none => rfl
        | some v =>
          obtain ⟨k', hk', hs'⟩ := c.paramVal_sorted hpv
          rw [c.lookupParam_eq] at hk'
          exact clean_val hV v _ hs' ((hGp k' (List.mem_of_find?_eq_some hk')).2 _ (List.mem_cons_self ..))
      · cases hs : sOK c ss ks s with
        | false => exact .inr (.inr (.inr (.inr (.inl ⟨v, s, hsort s hs, hv, rfl⟩))))
        | true =>
          refine hclean rfl ?_
          rw [clean_sExists, clean_eq, clean_val hV v s hv hs]
          simpa [sOK] using hs
      · cases hs : sOK c ss ks s with
        | false => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨v, w, s, hsort s hs, hds, hv, hw, hne, rfl⟩)))))
        | true =>
          refine hclean rfl ?_
          rw [clean_neg, clean_and, clean_val hV v s hv hs, clean_val hV w s hw hs]; rfl
      · have h' := hLc k hk
        by_cases hb : builtinColls.contains k = true ∧ ss.contains k.sort = true
        · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨k, List.contains_iff_mem.mp hb.1,
            ⟨hreg _ (List.contains_iff_mem.mp hb.2), .inl ⟨_, List.contains_iff_mem.mp hb.2, rfl⟩⟩, .inl rfl⟩)))))
        · simp only [hb, ↓reduceIte] at h'
          exact hclean rfl (Bool.and_eq_true_iff.mp h').1
    · -- the collections
      obtain ⟨k, hk, hmem⟩ := hφ
      have h' := hLc k hk
      by_cases hb : builtinColls.contains k = true ∧ ss.contains k.sort = true
      · simp only [hb, and_self, ↓reduceIte, List.isEmpty_iff] at h'
        rw [h'] at hmem; cases hmem
      · simp only [hb, ↓reduceIte] at h'
        exact hclean rfl (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h').2 φ hmem)
    · -- the functions
      rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
      · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hit))))
      · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
    · -- the rules
      rcases hφ with ⟨it, hit, rfl⟩ | ⟨x, rfl⟩
      · exact hclean rfl (hLi it (List.mem_append_left _ (List.mem_append_right _ hit)))
      · exact hclean rfl (by simp [definedness, Pattern.universal, Pattern.negation])
    · -- the fallbacks
      rcases hφ with ⟨k, vs, hk, hvs, hr, hsil, rfl⟩ | ⟨fn, vs, hfn, hvs, -, rfl⟩
      · cases hn : kOK c ss ks k.name with
        | false => exact .inr (.inr (.inr (.inl ⟨k, vs, hhook k hk hn, hvs, hr, hsil, rfl⟩)))
        | true =>
          rcases hGh k hk with h' | h'
          · rw [hn] at h'; cases h'
          · refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
            cases hfb : c.fallback k.name vs with
            | none => rfl
            | some v =>
              exact clean_val hV v _ (c.fallback_sorted (hookSigs_lookup k hk) hfb) (h'.2 _ (List.mem_cons_self ..))
      · have h' := hGf fn hfn
        refine hclean rfl (clean_graph hV h'.1 hvs (fun s hs => h'.2 s (List.mem_cons_of_mem _ hs)) ?_)
        cases hfr : c.fnRest fn vs with
        | none => rfl
        | some v => exact clean_val hV v _ (Semantics.fnRest_sorted hfr) (h'.2 _ (List.mem_cons_self ..))

namespace GenEqs

open DetachedB in
/-- **No premise names the symbols `ks`, decided**: the item lists name none of them (`listsB` at
no sort; the signature's items without the registry's exception, since no hook has such a name),
the values and the symbols applied at values name none (`valuesB`, `graphsB`), and no interpreted
hooked symbol has the name of one. -/
def freeB (c : Semantics) (ks : List Sym) : Bool :=
  listsB c [] ks && valuesB c [] ks && graphsB c [] ks && hookSigs.all (fun k => kOK c [] ks k.name)

end GenEqs

end KCore
