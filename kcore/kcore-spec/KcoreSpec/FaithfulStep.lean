/-
  KCore. Step soundness for the first stage, continued: evaluation (L3) and a rule's step (L4).
  The axioms of `Γ` are read at valuations built from a variable table: each variable of the axiom
  gets the element of its value.
-/
import KcoreSpec.FaithfulStage1
import KcoreSpec.OvlLawsFn
import Std.Data.String.ToNat

set_option autoImplicit false

namespace KCore

namespace Faithful

open ML
open KoreAML (DefOK Inh IsSort Closed KGround VarKey VarTable)

/-! ## Valuations from a variable table -/

/-- The valuation that gives the variable at each index of `tbl` the element `val` gives its key. -/
def valOf {M : Type} [Inhabited M] (tbl : VarTable) (val : VarKey → M) : Valuation M :=
  ⟨fun x => match tbl[x.val - 1]? with
    | some k => val k
    | none => default, fun _ _ => False⟩

theorem valOf_ev {M : Type} [Inhabited M] {tbl : VarTable} {val : VarKey → M} {k : VarKey} (h : k ∈ tbl) :
    (valOf tbl val).evalEvar (tbl.ev k) = val k := by
  have hlt := List.idxOf_lt_length_of_mem h
  simp only [valOf, VarTable.ev, VarTable.index, Nat.add_sub_cancel]
  rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]

theorem ev_ne_top {tbl : VarTable} {k : VarKey} : tbl.ev k ≠ KoreAML.topVar := by
  simp [VarTable.ev, VarTable.index, KoreAML.topVar]

/-! ## Canonical names are apart -/

theorem toString_inj {i j : Nat} (h : toString i = toString j) : i = j := Nat.repr_injective h

theorem append_cancel {a b c : String} (h : a ++ b = a ++ c) : b = c := by
  rw [← String.toList_inj, String.toList_append, String.toList_append] at h
  exact String.toList_inj.mp (List.append_cancel_left h)

theorem varName_inj {i j : Nat} (h : "Var" ++ ("V" ++ toString i) = "Var" ++ ("V" ++ toString j)) : i = j :=
  toString_inj (append_cancel (append_cancel h))

theorem xName_inj {i j : Nat} (h : "X" ++ toString i = "X" ++ toString j) : i = j :=
  toString_inj (append_cancel h)

theorem x_ne_var {a b : String} : "X" ++ a ≠ "Var" ++ b := by
  intro h
  have := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at this
  simp at this

/-- The index of the canonical variable a name is, among the first `n`. -/
def varIdx (n : Nat) (name : String) : Option Nat :=
  (List.range n).find? fun i => name == "Var" ++ ("V" ++ toString i)

theorem varIdx_eq {n i : Nat} (h : i < n) : varIdx n ("Var" ++ ("V" ++ toString i)) = some i := by
  unfold varIdx
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simp, (List.range i), (List.range' (i + 1) (n - i - 1)), ?_, ?_⟩
  · rw [List.range_eq_range', List.range_eq_range']
    have : n = i + (1 + (n - i - 1)) := by omega
    conv => lhs; rw [this]
    rw [← List.range'_append, ← List.range'_append]
    simp
  · intro j hj
    have hji : j < i := List.mem_range.mp hj
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    intro he
    exact absurd (varName_inj he) (by omega)

/-- The index of the formal argument a name is, among the first `n`. -/
def xIdx (n : Nat) (name : String) : Option Nat :=
  (List.range n).find? fun i => name == "X" ++ toString i

theorem xIdx_eq {n i : Nat} (h : i < n) : xIdx n ("X" ++ toString i) = some i := by
  unfold xIdx
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simp, (List.range i), (List.range' (i + 1) (n - i - 1)), ?_, ?_⟩
  · rw [List.range_eq_range', List.range_eq_range']
    have : n = i + (1 + (n - i - 1)) := by omega
    conv => lhs; rw [this]
    rw [← List.range'_append, ← List.range'_append]
    simp
  · intro j hj
    have hji : j < i := List.mem_range.mp hj
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    intro he
    exact absurd (xName_inj he) (by omega)

theorem xIdx_var {n : Nat} {b : String} : xIdx n ("Var" ++ b) = none := by
  unfold xIdx
  rw [List.find?_eq_none]
  intro j _ h
  exact x_ne_var (beq_iff_eq.mp h).symm

/-! ## Canonical variables -/

theorem varList_getD : ∀ (ss ns : List String) (i : Nat), i < ss.length → i < ns.length →
    (KoreAML.varList ss ns).getD i default = ⟨ns.getD i default, ss.getD i default⟩
  | [], _, _, h, _ => absurd h (by simp)
  | s :: ss, n :: ns, 0, _, _ => by simp [KoreAML.varList, KoreAML.withPres]
  | s :: ss, n :: ns, i + 1, h1, h2 => by
    have := varList_getD ss ns i (by simpa using h1) (by simpa using h2)
    simpa [KoreAML.varList, KoreAML.withPres] using this
  | _ :: _, [], _, _, h => absurd h (by simp)

theorem varList_length : ∀ (ss ns : List String), (KoreAML.varList ss ns).length = ss.length
  | [], _ => rfl
  | _ :: ss, ns => by
    have := varList_length ss ns.tail
    simp only [KoreAML.varList, KoreAML.withPres, List.map_cons, List.length_cons] at this ⊢
    rw [this]

theorem canonVars_length (c : Semantics) (vars : List Srt) : (canonVars c vars).length = vars.length := by
  simp [canonVars, varList_length]

theorem canonVars_getD (c : Semantics) {vars : List Srt} {i : Nat} (h : i < vars.length) :
    (canonVars c vars).getD i default = ⟨"V" ++ toString i, c.sortName (vars.getD i 0)⟩ := by
  unfold canonVars
  rw [varList_getD _ _ i (by simpa using h) (by simpa [canonNames] using h)]
  simp [canonNames, List.getD_eq_getElem?_getD, List.getElem?_map, h]

/-- The key of the canonical variable `i` of sorts `vars`. -/
def canonKey (c : Semantics) (vars : List Srt) (i : Nat) : VarKey :=
  KoreAML.evarKey ((canonVars c vars).getD i default).kore

theorem canonKey_eq (c : Semantics) {vars : List Srt} {i : Nat} (h : i < vars.length) :
    canonKey c vars i = .evar ("Var" ++ ("V" ++ toString i)) (KoreAML.srt (c.sortName (vars.getD i 0))) := by
  unfold canonKey
  rw [canonVars_getD c h]
  rfl

/-! ## The variables of a translated term -/

theorem kore_app (c : Semantics) (vs : List KoreAML.Var) (f : Sym) (ts : List Term) :
    Term.kore c vs (.app f ts) = symApp c f (Term.koreList c vs ts) := by
  rw [Term.kore]; unfold symApp; rfl

theorem symApp_cases (c : Semantics) (f : Sym) (ps : List Kore.Pattern) :
    ∃ h ss, symApp c f ps = .app h ss ps ∧ ∀ s ∈ ss, ∃ C, s = .ctor C [] := by
  unfold symApp
  split
  · exact ⟨_, _, rfl, fun s hs => by rw [mem_one hs]; exact ⟨_, rfl⟩⟩
  · exact ⟨_, _, rfl, nil_consts⟩

mutual
  theorem freeOf_kore (c : Semantics) (vs : List KoreAML.Var) : ∀ (t : Term) {bound : List VarKey} {k : VarKey},
      k ∈ KoreAML.freeOf bound (Term.kore c vs t) → ∃ i ∈ varOccs t, k = KoreAML.evarKey (vs.getD i default).kore
    | .var i, bound, k, h => by
      rw [Term.kore] at h; unfold KoreAML.varAt at h; rw [KoreAML.freeOf] at h
      split at h
      · cases h
      · exact ⟨i, by simp [varOccs], mem_one h⟩
    | .app f ts, bound, k, h => by
      rw [kore_app] at h
      obtain ⟨hd, ss, he, _⟩ := symApp_cases c f (Term.koreList c vs ts)
      rw [he, KoreAML.freeOf] at h
      obtain ⟨i, hi, rfl⟩ := freeOf_koreList c vs ts h
      exact ⟨i, by rw [varOccs]; exact hi, rfl⟩
    | .inj a b t, bound, k, h => by
      rw [Term.kore] at h; unfold KoreAML.injP at h; rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList] at h
      simp only [List.append_nil] at h
      obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t h
      exact ⟨i, by rw [varOccs]; exact hi, rfl⟩
    | .as t j, bound, k, h => by
      rw [Term.kore] at h
      rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at h
      simp only [List.append_nil, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t h
        exact ⟨i, by rw [varOccs]; exact List.mem_append_left _ hi, rfl⟩
      · unfold KoreAML.varAt at h; rw [KoreAML.freeOf] at h
        split at h
        · cases h
        · exact ⟨j, by rw [varOccs]; exact List.mem_append_right _ (List.mem_singleton_self _), mem_one h⟩
    | .dv s lit, bound, k, h => by
      rw [Term.kore, KoreAML.freeOf] at h; cases h
  theorem freeOf_koreList (c : Semantics) (vs : List KoreAML.Var) : ∀ (ts : List Term) {bound : List VarKey} {k : VarKey},
      k ∈ KoreAML.freeOfList bound (Term.koreList c vs ts) → ∃ i ∈ varOccsList ts, k = KoreAML.evarKey (vs.getD i default).kore
    | [], bound, k, h => by rw [Term.koreList, KoreAML.freeOfList] at h; cases h
    | t :: ts, bound, k, h => by
      rw [Term.koreList, KoreAML.freeOfList] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t h
        exact ⟨i, by rw [varOccsList]; exact List.mem_append_left _ hi, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := freeOf_koreList c vs ts h
        exact ⟨i, by rw [varOccsList]; exact List.mem_append_right _ hi, rfl⟩
end

mutual
  theorem varsOf_kore (c : Semantics) (vs : List KoreAML.Var) : ∀ (t : Term) {i : Nat}, i ∈ varOccs t →
      KoreAML.evarKey (vs.getD i default).kore ∈ KoreAML.varsOf (Term.kore c vs t)
    | .var j, i, h => by
      rw [varOccs] at h
      rw [mem_one h, Term.kore]; unfold KoreAML.varAt; rw [KoreAML.varsOf]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    | .app f ts, i, h => by
      rw [varOccs] at h
      rw [kore_app]
      obtain ⟨hd, ss, he, _⟩ := symApp_cases c f (Term.koreList c vs ts)
      rw [he, KoreAML.varsOf]
      exact List.mem_append_right _ (varsOf_koreList c vs ts h)
    | .inj a b t, i, h => by
      rw [varOccs] at h
      rw [Term.kore]; unfold KoreAML.injP; rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
      exact List.mem_append_right _ (List.mem_append_left _ (varsOf_kore c vs t h))
    | .as t j, i, h => by
      rw [varOccs] at h
      rw [Term.kore, KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_right _ (List.mem_append_left _ (varsOf_kore c vs t h))
      · rw [mem_one h]
        unfold KoreAML.varAt; rw [KoreAML.varsOf]
        exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_singleton_self _))))
    | .dv s lit, i, h => by rw [varOccs] at h; cases h
  theorem varsOf_koreList (c : Semantics) (vs : List KoreAML.Var) : ∀ (ts : List Term) {i : Nat}, i ∈ varOccsList ts →
      KoreAML.evarKey (vs.getD i default).kore ∈ KoreAML.varsOfList (Term.koreList c vs ts)
    | [], i, h => by rw [varOccsList] at h; cases h
    | t :: ts, i, h => by
      rw [varOccsList] at h
      rw [Term.koreList, KoreAML.varsOfList]
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (varsOf_kore c vs t h)
      · exact List.mem_append_right _ (varsOf_koreList c vs ts h)
end

mutual
  theorem varOccs_lt {x : TermCtx} {vars : List Srt} : ∀ (t : Term) {s : Srt}, sortOfTerm x vars t = some s →
      ∀ i ∈ varOccs t, i < vars.length
    | .var j, s, h, i, hi => by
      rw [varOccs] at hi; rw [mem_one hi]
      exact (List.getElem?_eq_some_iff.mp (sortOfTerm_var.mp h)).1
    | .app f ts, s, h, i, hi => by
      rw [varOccs] at hi
      obtain ⟨k, _, hk, _⟩ := sortOfTerm_app.mp h
      exact varOccsList_lt ts hk i hi
    | .inj a b t, s, h, i, hi => by
      rw [varOccs] at hi
      obtain ⟨_, h', _⟩ := sortOfTerm_inj.mp h
      exact varOccs_lt t h' i hi
    | .as t j, s, h, i, hi => by
      rw [varOccs] at hi
      obtain ⟨hv, h'⟩ := Exec.sortOfTerm_as h
      rcases List.mem_append.mp hi with hi | hi
      · exact varOccs_lt t h' i hi
      · rw [mem_one hi]; exact (List.getElem?_eq_some_iff.mp hv).1
    | .dv s' lit, s, h, i, hi => by rw [varOccs] at hi; cases hi
  theorem varOccsList_lt {x : TermCtx} {vars : List Srt} : ∀ (ts : List Term) {ss : List Srt},
      sortsOfTerms x vars ts = some ss → ∀ i ∈ varOccsList ts, i < vars.length
    | [], ss, h, i, hi => by rw [varOccsList] at hi; cases hi
    | t :: ts, ss, h, i, hi => by
      rw [varOccsList] at hi
      obtain ⟨s, ss', h1, h2, _⟩ := sortsOfTerms_cons.mp h
      rcases List.mem_append.mp hi with hi | hi
      · exact varOccs_lt t h1 i hi
      · exact varOccsList_lt ts h2 i hi
end

/-! ## The first stage -/

/-- `f` may be called in the first stage: if it is a function of the definition, its clauses have
no competitor (no clause of a smaller priority, `lowerClauses`) and it has a defined result at every
argument list of its sorts. -/
def Callable (c : Semantics) (f : Sym) : Prop :=
  ∀ fn, c.lookupFn f = some fn → (∀ cl ∈ fn.clauses, lowerClauses fn cl = []) ∧
    ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c f vs (some v)

/-- `P` holds of every function an application of `f` may call: of `f`, and of each function among
the symbols `f` overloads where `f` is an overloading symbol (at arguments such a function covers,
the application has that function's value, `EvalTerm.ovlFn`). -/
def CallsAll (c : Semantics) (P : Sym → Prop) (f : Sym) : Prop :=
  P f ∧ ∀ o, c.lookupOvl f = some o → ∀ kg ∈ c.ovlOver o, c.ovlByFn kg = true → P kg.name

/-- **The first stage's restrictions.** No rule has a rule of a smaller priority to compete
with; every rule's left-hand side and every clause's patterns are plain (constructors,
injections, aliases, variables and domain values: no map or collection pattern symbol); and every
symbol a rule's or a clause's right-hand side, `requires` or `ensures` applies is `Callable`, and
so is each function among the symbols it overloads (`CallsAll`): every function it reaches is total
and has ordinary clauses only. -/
def Stage1 (c : Semantics) : Prop :=
  (∀ r ∈ c.rules, ∀ r' ∈ c.rules, ¬ r'.prio < r.prio) ∧
  (∀ r ∈ c.rules, plainPat c r.lhs = true ∧
    ∀ f ∈ Term.heads r.rhs ++ (r.req.map Term.heads).getD [] ++ (r.ens.map Term.heads).getD [],
      CallsAll c (Callable c) f) ∧
  (∀ fn ∈ c.allFns, ∀ cl ∈ fn.clauses, plainPats c cl.pats = true ∧
    ∀ f ∈ Term.heads cl.rhs ++ (cl.req.map Term.heads).getD [] ++ (cl.ens.map Term.heads).getD [],
      CallsAll c (Callable c) f)

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The set a result denotes: its value's element, or nothing where it is undefined. -/
def Res (c : Semantics) (I : Interpretation KoreAML.Sym M) (e : Valuation M) : Option GroundTerm → M → Prop
  | some v, m => (den c v).interpret I e m
  | none, _ => False

theorem Res_closed (r : Option GroundTerm) (e e' : Valuation M) (m : M) : Res c I e r m ↔ Res c I e' r m := by
  cases r with
  | none => exact Iff.rfl
  | some v => exact (den_closed c v).interp e e' m

/-- **A function's rest, in a model.** At values of a function's argument sorts where every clause
fails, its application denotes what its rest (`fnRest`) denotes, through `ΓFallback`. -/
theorem rest_den [Inhabited M] (hI : I ⊧ᴵP Γ c) {fn : Fn} {vs : List GroundTerm} (hfn : fn ∈ c.allFns)
    (hvs : c.sortsOf vs = some fn.args) (hnone : ∀ cl ∈ fn.clauses, Fails c vs cl) (e : Valuation M) (m : M) :
    (KoreAML.den (symApp c fn.label (GroundTerm.koreList c vs))).interpret I e m ↔ Res c I e (c.fnRest fn vs) m := by
  rw [(KoreAML.interp_equal (defOK hI)).mp (sat_rest hI hfn hvs hnone e default) m]
  cases c.fnRest fn vs with
  | none => simp [Res, Pattern.interpret]
  | some v => rfl

/-- The element a value denotes. -/
noncomputable def elemOf [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (v : GroundTerm) : M :=
  Classical.epsilon fun a => ∀ m, (den c v).interpret I ⟨fun _ => default, fun _ _ => False⟩ m ↔ m = a

theorem elemOf_spec [Inhabited M] (hI : I ⊧ᴵP Γ c) {v : GroundTerm} {s : Srt} (h : c.sortOf v = some s)
    (e : Valuation M) :
    (∀ m, (den c v).interpret I e m ↔ m = elemOf c I v) ∧
      (KoreAML.inhOf (sortP (c.sortName s))).interpret I e (elemOf c I v) := by
  obtain ⟨a, ha, has⟩ := den_single hI h ⟨fun _ => default, fun _ _ => False⟩
  have hs := Classical.epsilon_spec (p := fun a => ∀ m, (den c v).interpret I ⟨fun _ => default, fun _ _ => False⟩ m ↔ m = a) ⟨a, ha⟩
  have heq : elemOf c I v = a := ((ha _).mp ((hs _).mpr rfl))
  refine ⟨fun m => ?_, ?_⟩
  · rw [(den_closed c v).interp e ⟨fun _ => default, fun _ _ => False⟩ m, heq]; exact ha m
  · rw [heq]; exact (((Closed.sym _).app (Closed.sym _)).interp _ _ a).mp has

/-- The head `symApp` applies, as the translation writes it. -/
def symHead (c : Semantics) (f : Sym) : KoreAML.P :=
  match iteSort? (c.symName f) with
  | some X => KoreAML.sym (.symbol "Lblite") ⬝ KoreAML.sym (.sort ("Sort" ++ X))
  | none => KoreAML.sym (.symbol (c.symName f))

theorem symHead_closed (f : Sym) : Closed (symHead c f) := by
  unfold symHead; split
  · exact (Closed.sym _).app (Closed.sym _)
  · exact Closed.sym _

theorem tr_symApp {t : VarTable} (f : Sym) (ps : List Kore.Pattern) :
    KoreAML.tr ⟨t, []⟩ (symApp c f ps) = KoreAML.trArgs ⟨t, []⟩ (symHead c f) ps := by
  unfold symApp symHead
  cases h : iteSort? (c.symName f) with
  | some X =>
    dsimp only
    rw [KoreAML.tr]; simp [KoreAML.trSortApp, KoreAML.srt, KoreAML.trSort_const]
  | none =>
    dsimp only
    exact KoreAML.tr_app0 _ _

theorem trArgs_empty {ctx : KoreAML.Ctx} {acc : KoreAML.P} {e : Valuation M} (h : ∀ m, ¬ acc.interpret I e m) :
    ∀ (ps : List Kore.Pattern) m, ¬ (KoreAML.trArgs ctx acc ps).interpret I e m
  | [] => by rw [KoreAML.trArgs_nil]; exact h
  | p :: ps => by
    rw [KoreAML.trArgs_cons]
    exact trArgs_empty (fun m hm => by
      obtain ⟨a, _, ha, _, _⟩ := KoreAML.interp_app.mp hm
      exact h a ha) ps

theorem sig_sortConst {s : Srt} (hs : s < nRegSorts + c.sortNames.length) :
    KoreAML.sortConstantItem (sortDeclOf c s) ∈ sigItems c := by
  unfold sigItems
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  exact List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)

theorem sig_arity {k : CtorSig} (hk : k ∈ kernelSyms c) : symArityItem c k ∈ sigItems c := by
  unfold sigItems
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

theorem sig_ceilDef : KoreAML.ceilDefItem ∈ sigItems c := by
  unfold sigItems
  exact List.mem_append_right _ (by simp)

/-- A numbered sort denotes one sort. -/
theorem sortSing [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] {s : Srt} (hs : s < nRegSorts + c.sortNames.length) :
    ∃ σ, (∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName s)) a ↔ a = σ) ∧ IsSort I σ :=
  KoreAML.sortConst_of (defOK hI) (sat_sigItem hI (sig_sortConst hs))

theorem call_congr {tbl : VarTable} {e0 e' : Valuation M} :
    ∀ (ss : List String) (ws : List GroundTerm) (j : Nat) (acc acc' : KoreAML.P), ws.length = ss.length →
      (∀ k s w, ss[k]? = some s → ws[k]? = some w → ∀ m, (den c w).interpret I e0 m ↔
        m = e'.evalEvar (tbl.ev (.evar ("X" ++ toString (j + k)) (KoreAML.srt s)))) →
      (∀ m, acc.interpret I e0 m ↔ acc'.interpret I e' m) →
      ∀ m, (KoreAML.trArgs ⟨[], []⟩ acc (GroundTerm.koreList c ws)).interpret I e0 m ↔
        (KoreAML.trArgs ⟨tbl, []⟩ acc' (KoreAML.vars (KoreAML.numbered "X" j ss))).interpret I e' m
  | [], [], _, _, _, _, _, hacc, m => by
    rw [GroundTerm.koreList]
    simp only [KoreAML.numbered, KoreAML.vars, List.map_nil, KoreAML.trArgs_nil]
    exact hacc m
  | s :: ss, w :: ws, j, acc, acc', hl, hk, hacc, m => by
    rw [GroundTerm.koreList]
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp, KoreAML.trArgs_cons]
    refine call_congr ss ws (j + 1) _ _ (by simpa using hl) (fun k s' w' h1 h2 m => ?_)
      (KoreAML.interp_app_congr hacc (fun m => ?_)) m
    · have := hk (k + 1) s' w' (by simpa using h1) (by simpa using h2) m
      rw [this, show j + (k + 1) = j + 1 + k by omega]
    · have := hk 0 s w rfl rfl m
      rw [Nat.add_zero] at this
      show (den c w).interpret I e0 m ↔ _
      rw [this, KoreAML.tr]; exact Iff.rfl
  | [], _ :: _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl

theorem call_arity {tbl : VarTable} {e' : Valuation M} :
    ∀ (ss : List String) (j : Nat) (acc acc' : KoreAML.P) (m : M),
      (KoreAML.trArgs ⟨tbl, []⟩ acc (KoreAML.vars (KoreAML.numbered "X" j ss))).interpret I e' m →
      (∀ k s, ss[k]? = some s → (KoreAML.inhOf (KoreAML.Cons.sortP s)).interpret I e'
        (e'.evalEvar (tbl.ev (.evar ("X" ++ toString (j + k)) (KoreAML.srt s))))) →
      (∀ m, acc.interpret I e' m → acc'.interpret I e' m) →
      (KoreAML.appList acc' (ss.map fun s => KoreAML.inhOf (KoreAML.trSort [] (KoreAML.srt s)))).interpret I e' m
  | [], _, _, _, m, h, _, hacc => by
    simp only [KoreAML.numbered, KoreAML.vars, List.map_nil, KoreAML.trArgs_nil] at h
    exact hacc m h
  | s :: ss, j, acc, acc', m, h, hk, hacc => by
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp, KoreAML.trArgs_cons] at h
    simp only [List.map_cons, KoreAML.appList]
    refine call_arity ss (j + 1) _ _ m h (fun k s' h1 => ?_) (fun m hm => ?_)
    · have := hk (k + 1) s' (by simpa using h1)
      rwa [show j + (k + 1) = j + 1 + k by omega] at this
    · obtain ⟨a, b, ha, hb, happ⟩ := KoreAML.interp_app.mp hm
      rw [KoreAML.tr] at hb
      have hb' : b = e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) := hb
      have := hk 0 s rfl
      rw [Nat.add_zero, ← hb'] at this
      exact KoreAML.interp_app.mpr ⟨a, b, hacc a ha, by unfold KoreAML.srt; rw [KoreAML.trSort_const]; exact this, happ⟩

/-! ## Symbols looked up in a right-hand side's context -/

theorem rhs_lookup_ctor {L : List CtorSig} {f : Sym} {k k0 : CtorSig} (h0 : lookupSig c.ctorSigs f = some k0)
    (h : lookupSig (c.rhsCtx L).heads f = some k) : k = k0 := by
  simp only [Semantics.rhsCtx, List.append_assoc] at h
  rw [lookupSig_append_of_some h0] at h
  exact (Option.some.inj h).symm

theorem rhs_lookup_hook {L : List CtorSig} {f : Sym} {k : CtorSig} (hc : c.isCtor f = false) (hh : isHook f = true)
    (h : lookupSig (c.rhsCtx L).heads f = some k) : k ∈ hookSigs ∧ k.name = f := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  obtain ⟨k₀, hk₀⟩ := lookupSig_hookSigs_of_isHook hh
  simp only [Semantics.rhsCtx, List.append_assoc] at h
  rw [lookupSig_append_of_none hnc, lookupSig_append_of_some hk₀] at h
  cases h
  exact lookupSig_spec hk₀

theorem rhs_lookup_param {L : List CtorSig} {f : Sym} {k : CtorSig} (hc : c.isCtor f = false) (hh : isHook f = false)
    (hp : c.isParam f = true) (h : lookupSig (c.rhsCtx L).heads f = some k) :
    ∃ kp ∈ c.params, kp.sig = k ∧ kp.sig.name = f := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  obtain ⟨kp, hkp⟩ := Option.isSome_iff_exists.mp (by simpa [Semantics.isParam] using hp)
  simp only [Semantics.rhsCtx, List.append_assoc] at h
  rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hh),
    lookupSig_append_of_some (l' := c.sortPreds.map Fn.sig ++ (L ++ c.ovlSigs)) (k := kp.sig)
      (by rw [c.lookupSig_params, hkp]; rfl)] at h
  cases h
  rw [Semantics.lookupParam_eq] at hkp
  exact ⟨kp, List.mem_of_find?_eq_some hkp, rfl, by simpa using List.find?_some hkp⟩

theorem rhs_lookup_call (hc0 : SortCtx c) {L : List CtorSig} (hL : HeadsOK c L) {f : Sym} {k : CtorSig}
    (hc : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = false) (hfn0 : c.lookupFn f ≠ none)
    (h : lookupSig (c.rhsCtx L).heads f = some k) :
    ∃ fn ∈ c.allFns, fn.sig = k ∧ c.lookupFn f = some fn := by
  have hnc : lookupSig c.ctorSigs f = none :=
    Option.not_isSome_iff_eq_none.mp (by simpa [Semantics.isCtor] using hc)
  simp only [Semantics.rhsCtx, List.append_assoc] at h
  rw [lookupSig_append_of_none hnc, lookupSig_append_of_none (lookupSig_hookSigs_of_not_isHook hh),
    lookupSig_append_of_none (c.lookupSig_params_of_not hp)] at h
  obtain ⟨fn0, hfn0'⟩ := Option.ne_none_iff_exists'.mp hfn0
  obtain ⟨hkL, hkn⟩ := lookupSig_spec (rhs_lookup_fn hc0 hfn0' h)
  obtain ⟨fn, hfn, rfl⟩ := headsOK_preds hL k hkL
  refine ⟨fn, hfn, rfl, ?_⟩
  rw [← hkn, Semantics.lookupFn_eq]; exact find?_label hc0.nodupFns hfn

theorem trSort_R {tbl : VarTable} : KoreAML.trSort tbl KoreAML.R = .evar (tbl.ev (.sortVar "R")) := rfl

theorem trSort_srt {tbl : VarTable} (n : String) : KoreAML.trSort tbl (KoreAML.srt n) = KoreAML.sym (.sort ("Sort" ++ n)) := by
  unfold KoreAML.srt; rw [KoreAML.trSort_const]

/-- The head `symApp` applies denotes the same under every valuation. -/
theorem symHead_congr {e e' : Valuation M} (f : Sym) (m : M) :
    (symHead c f).interpret I e m ↔ (symHead c f).interpret I e' m :=
  (symHead_closed f).interp e e' m

/-- **A symbol's arity at the head `symApp` applies**: the head applied to elements of the argument
sorts gives elements of the result sort only (`symArityItem`, whichever head the symbol's name
gives it). -/
theorem symArity_at [Inhabited M] (hI : I ⊧ᴵP Γ c) {k : CtorSig} (hk : k ∈ kernelSyms c) (e : Valuation M)
    (a : M)
    (ha : (KoreAML.appList (symHead c k.name)
      ((k.args.map c.sortName).map fun s => KoreAML.inhOf (KoreAML.trSort [] (KoreAML.srt s)))).interpret I e a) :
    (KoreAML.inhOf (KoreAML.sym (.sort ("Sort" ++ c.sortName k.result)))).interpret I e a := by
  have hit := sat_sigItem hI (sig_arity hk)
  unfold symArityItem at hit
  unfold symHead at ha
  cases hn : iteSort? (c.symName k.name) with
  | some X =>
    rw [hn] at hit ha
    simp only [List.map_map, Function.comp_def, trSort_srt] at ha
    exact (KoreAML.interp_included (defOK hI)).mp (hit e default) a ha
  | none =>
    rw [hn] at hit ha
    dsimp only at hit ha
    unfold KoreAML.arityItem at hit
    dsimp only [KoreAML.paramTable, List.map_nil, KoreAML.appList] at hit
    have hinc := (KoreAML.interp_included (defOK hI)).mp (hit e default) a
    unfold srtOf at hinc
    rw [trSort_srt] at hinc
    apply hinc
    rw [List.map_map] at ha ⊢
    exact ha

/-- The free variables of an application `symApp` writes are its arguments'. -/
theorem freeOf_symApp (b : List VarKey) (f : Sym) (ps : List Kore.Pattern) :
    KoreAML.freeOf b (symApp c f ps) = KoreAML.freeOfList b ps := by
  unfold symApp; split <;> rw [KoreAML.freeOf]

/-- A function that covers an overloading symbol at some arguments is not named like `ite` at a
sort (`NamesNumbered`: it is one of the symbols an overloading symbol overloads). -/
theorem namesNumbered_cover (hnn : NamesNumbered c) {f : Sym} {o : OvlSig} {ws : List GroundTerm} {kg : CtorSig}
    (hlo : c.lookupOvl f = some o) (hcov : c.fnCover f ws = some kg) : iteSort? (c.symName kg.name) = none := by
  obtain ⟨o', ho', hkg, -, -⟩ := OvlLaws.fnCover_some_parts hcov
  rw [hlo] at ho'; cases ho'
  obtain ⟨-, i, hi, he, -⟩ := OvlLaws.lookupOvl_spec hlo
  exact hnn.2.1 o (he ▸ List.getElem_mem hi) kg.name (OvlLaws.mem_ovlOver hkg)

theorem isFree_R {tbl : VarTable} : (KoreAML.trSort tbl KoreAML.R).isFreeEvar KoreAML.topVar = false := by
  rw [trSort_R]
  simp only [Pattern.isFreeEvar]
  have := (ev_ne_top (tbl := tbl) (k := .sortVar "R")).symm
  simp [this]

theorem tr_and2 {ctx : KoreAML.Ctx} (S : Kore.KSort) (p q : Kore.Pattern) :
    KoreAML.tr ctx (.and S [p, q]) = KoreAML.sAnd (KoreAML.tr ctx p) (KoreAML.tr ctx q) := by
  rw [KoreAML.tr]; simp only [KoreAML.trAndList]

theorem tr_and3 {ctx : KoreAML.Ctx} (S : Kore.KSort) (p q r : Kore.Pattern) :
    KoreAML.tr ctx (.and S [p, q, r]) =
      KoreAML.sAnd (KoreAML.tr ctx p) (KoreAML.sAnd (KoreAML.tr ctx q) (KoreAML.tr ctx r)) := by
  rw [KoreAML.tr]; simp only [KoreAML.trAndList]

theorem tr_and4 {ctx : KoreAML.Ctx} (S : Kore.KSort) (p q r t : Kore.Pattern) :
    KoreAML.tr ctx (.and S [p, q, r, t]) = KoreAML.sAnd (KoreAML.tr ctx p)
      (KoreAML.sAnd (KoreAML.tr ctx q) (KoreAML.sAnd (KoreAML.tr ctx r) (KoreAML.tr ctx t))) := by
  rw [KoreAML.tr]; simp only [KoreAML.trAndList]

section
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnm : NamesPlain c)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  {σ' : Subst} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e' : Valuation M}
  (hσ' : c.WellSorted vars σ') (hvs : vs.length = vars.length) (hag : Agrees c I tbl vs σ' e')
  {σres m0 : M} (hR : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e' a ↔ a = σres)
  (hσres : IsSort I σres) (hm0 : Inh I σres m0)
include hI hnm htr hσ' hvs hag hR hσres hm0

/-- The argument part of a clause's premise, `⋀ⱼ Xⱼ ∈ pⱼ`, holds at a valuation that gives each
`Xⱼ` the element of the argument the pattern `pⱼ` denotes. -/
theorem argsConj_den : ∀ {ps : List Term} {ws : List GroundTerm}, PatVals c σ' ps ws → ∀ (ss : List Srt) (j : Nat),
    plainPats c ps = true → sortsOfTerms c.patCtxAll vars ps = some ss →
    (∀ s ∈ ss, s < nRegSorts + c.sortNames.length) →
    (∀ k s w, ss[k]? = some s → ws[k]? = some w → ∀ m,
      m = e'.evalEvar (tbl.ev (.evar ("X" ++ toString (j + k)) (KoreAML.srt (c.sortName s)))) ↔ (den c w).interpret I e' m) →
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.argsConj j ((ss.map c.sortName).zip (Term.koreList c vs ps)))).interpret I e' m0
  | _, _, .nil, ss, j, _, ht, _, _ => by
    rw [sortsOfTerms_nil.mp ht, Term.koreList]
    simp only [List.map_nil, List.zip_nil_left, KoreAML.argsConj]
    rw [KoreAML.tr, KoreAML.interp_sTop (defOK hI) isFree_R, KoreAML.interp_inhOf_of hR]
    exact hm0
  | _, _, .cons (p := p) (ps := ps) (v := w) (vs := ws) h hs, ss, j, hp, ht, hnum, hX => by
    obtain ⟨s, ss', h1, h2, rfl⟩ := sortsOfTerms_cons.mp ht
    rw [plainPats] at hp
    simp only [Bool.and_eq_true] at hp
    have hD := defOK hI
    have hc := sat_sigItem hI (sig_ceilDef (c := c))
    have hl2 := patVal_den hI hnm htr hσ' hvs hag h hp.1 h1
    obtain ⟨σs, hσs1, hσs2⟩ := sortSing hI (hnum s (List.mem_cons_self ..))
    rw [Term.koreList]
    simp only [List.map_cons, List.zip_cons_cons, KoreAML.argsConj]
    rw [tr_and2, KoreAML.interp_sAnd]
    have hX0 := hX 0 s w rfl rfl
    simp only [Nat.add_zero] at hX0
    have hwx := (hX0 _).mp rfl
    obtain ⟨x, hx, hxs⟩ := den_single hI hl2.1 e'
    have hex : e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt (c.sortName s)))) = x := (hx _).mp hwx
    refine ⟨?_, argsConj_den hs ss' (j + 1) hp.2 h2 (fun s' hs' => hnum s' (List.mem_cons_of_mem _ hs'))
      (fun k s' w' hk1 hk2 m => ?_)⟩
    · rw [KoreAML.tr]
      rw [KoreAML.interp_sIn hD hc (S := KoreAML.trSort tbl (KoreAML.srt (c.sortName s))) (by rw [trSort_srt]; exact hσs1)
        hR hσs2 hσres (fun a ha => ?_) m0]
      · refine ⟨⟨x, ?_, ?_⟩, hm0⟩
        · unfold KoreAML.ev; rw [KoreAML.tr]; exact hex.symm
        · exact (hl2.2 x).mpr ((hx x).mpr rfl)
      · unfold KoreAML.ev at ha; rw [KoreAML.tr] at ha
        have ha' : a = x := by rw [← hex]; exact ha
        rw [ha']
        exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσs1).mp hxs
    · have := hX (k + 1) s' w' (by simpa using hk1) (by simpa using hk2) m
      rwa [show j + (k + 1) = j + 1 + k by omega] at this

end

/-! ## The variables of an equation's pattern -/

theorem mem_freeOfList {b : List VarKey} {p : Kore.Pattern} :
    ∀ {ps : List Kore.Pattern} {k : VarKey}, p ∈ ps → k ∈ KoreAML.freeOf b p → k ∈ KoreAML.freeOfList b ps
  | [], _, h, _ => absurd h List.not_mem_nil
  | q :: qs, k, h, hk => by
    rw [KoreAML.freeOfList]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ hk
    · exact List.mem_append_right _ (mem_freeOfList h hk)

theorem mem_varsOfList {p : Kore.Pattern} :
    ∀ {ps : List Kore.Pattern} {k : VarKey}, p ∈ ps → k ∈ KoreAML.varsOf p → k ∈ KoreAML.varsOfList ps
  | [], _, h, _ => absurd h List.not_mem_nil
  | q :: qs, k, h, hk => by
    rw [KoreAML.varsOfList]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ hk
    · exact List.mem_append_right _ (mem_varsOfList h hk)

theorem freeOf_argsConj : ∀ (l : List (String × Kore.Pattern)) (j : Nat) {b : List VarKey} {k : VarKey},
    k ∈ KoreAML.freeOf b (KoreAML.argsConj j l) →
      (∃ n s p, l[n]? = some (s, p) ∧ k = .evar ("X" ++ toString (j + n)) (KoreAML.srt s)) ∨
        ∃ q ∈ l, k ∈ KoreAML.freeOf b q.2
  | [], j, b, k, h => by
    simp only [KoreAML.argsConj] at h; rw [KoreAML.freeOf] at h; cases h
  | (s, p) :: l, j, b, k, h => by
    simp only [KoreAML.argsConj] at h
    rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOf] at h
    simp only [List.append_nil, List.mem_append] at h
    rcases h with (h | h) | h
    · unfold KoreAML.ev at h; rw [KoreAML.freeOf] at h
      split at h
      · cases h
      · exact Or.inl ⟨0, s, p, rfl, by rw [mem_one h, Nat.add_zero]; rfl⟩
    · exact Or.inr ⟨(s, p), List.mem_cons_self .., h⟩
    · rcases freeOf_argsConj l (j + 1) h with ⟨n, s', p', hn, rfl⟩ | ⟨q, hq, hk⟩
      · exact Or.inl ⟨n + 1, s', p', by simpa using hn, by rw [show j + (n + 1) = j + 1 + n by omega]⟩
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hk⟩

theorem varsOf_argsConj_X : ∀ (l : List (String × Kore.Pattern)) (j n : Nat) (s : String) (p : Kore.Pattern),
    l[n]? = some (s, p) → VarKey.evar ("X" ++ toString (j + n)) (KoreAML.srt s) ∈ KoreAML.varsOf (KoreAML.argsConj j l)
  | [], _, _, _, _, h => by simp at h
  | (s', p') :: l, j, 0, s, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [KoreAML.argsConj]
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOf]
    unfold KoreAML.ev; rw [KoreAML.varsOf]
    refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))
    rw [Nat.add_zero]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  | (s', p') :: l, j, n + 1, s, p, h => by
    simp only [List.getElem?_cons_succ] at h
    have := varsOf_argsConj_X l (j + 1) n s p h
    simp only [KoreAML.argsConj]
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
    rw [show j + (n + 1) = j + 1 + n by omega]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ this))

theorem varsOf_argsConj_pat : ∀ (l : List (String × Kore.Pattern)) (j : Nat) {q : String × Kore.Pattern} {k : VarKey},
    q ∈ l → k ∈ KoreAML.varsOf q.2 → k ∈ KoreAML.varsOf (KoreAML.argsConj j l)
  | [], _, _, _, h, _ => absurd h List.not_mem_nil
  | (s, p) :: l, j, q, k, h, hk => by
    simp only [KoreAML.argsConj]
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList]
    rcases List.mem_cons.mp h with rfl | h
    · rw [KoreAML.varsOf]
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hk))
    · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (varsOf_argsConj_pat l (j + 1) h hk)))

theorem freeOf_callX : ∀ (ss : List String) (j : Nat) {b : List VarKey} {k : VarKey},
    k ∈ KoreAML.freeOfList b (KoreAML.vars (KoreAML.numbered "X" j ss)) →
      ∃ n s, ss[n]? = some s ∧ k = .evar ("X" ++ toString (j + n)) (KoreAML.srt s)
  | [], j, b, k, h => by
    simp only [KoreAML.numbered, KoreAML.vars, List.map_nil] at h; rw [KoreAML.freeOfList] at h; cases h
  | s :: ss, j, b, k, h => by
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp] at h
    rw [KoreAML.freeOfList, KoreAML.freeOf] at h
    rcases List.mem_append.mp h with h | h
    · split at h
      · cases h
      · exact ⟨0, s, rfl, by rw [mem_one h, Nat.add_zero]; rfl⟩
    · obtain ⟨n, s', hn, rfl⟩ := freeOf_callX ss (j + 1) h
      exact ⟨n + 1, s', by simpa using hn, by rw [show j + (n + 1) = j + 1 + n by omega]⟩

theorem varsOfList_mem : ∀ {ps : List Kore.Pattern} {k : VarKey}, k ∈ KoreAML.varsOfList ps → ∃ p ∈ ps, k ∈ KoreAML.varsOf p
  | [], _, h => by rw [KoreAML.varsOfList] at h; cases h
  | p :: ps, k, h => by
    rw [KoreAML.varsOfList] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨p, List.mem_cons_self .., h⟩
    · obtain ⟨q, hq, hk⟩ := varsOfList_mem h
      exact ⟨q, List.mem_cons_of_mem _ hq, hk⟩

theorem koreList_length (vs : List KoreAML.Var) : ∀ ts : List Term, (Term.koreList c vs ts).length = ts.length
  | [] => by rw [Term.koreList]; rfl
  | t :: ts => by rw [Term.koreList, List.length_cons, List.length_cons, koreList_length vs ts]

theorem sortName_bool : c.sortName Srt.bool = "Bool" := by
  unfold Semantics.sortName; simp only [show Srt.bool < nRegSorts from by decide, ↓reduceIte]; rfl

theorem bool_numbered : Srt.bool < nRegSorts + c.sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

/-- The premise of a clause's equation. -/
def clausePrem (c : Semantics) (fn : Fn) (cl : Clause) : Kore.Pattern :=
  premise (fn.args.map c.sortName) (cl.req.map (Term.kore c (canonVars c cl.vars)))
    (Term.koreList c (canonVars c cl.vars) cl.pats)

/-- The right side of a clause's equation: `rhs ∧ ens`, `ens` being `⌈E = true⌉` for an `ensures`
E and `⊤` without one. -/
def clauseRight (c : Semantics) (fn : Fn) (cl : Clause) : Kore.Pattern :=
  .and (srtOf c fn.result) [Term.kore c (canonVars c cl.vars) cl.rhs,
    reqPat (srtOf c fn.result) (cl.ens.map (Term.kore c (canonVars c cl.vars)))]

/-- The conclusion of a clause's equation: `f(X̄) = rhs ∧ ens`. -/
def clauseConcl (c : Semantics) (fn : Fn) (cl : Clause) : Kore.Pattern :=
  .equals (KoreAML.srt (c.sortName fn.result)) KoreAML.R
    (symApp c fn.label (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))
    (clauseRight c fn cl)

/-- The axiom of a clause's equation, as `clauseEquation` writes it. -/
def clauseAxiom (c : Semantics) (fn : Fn) (cl : Clause) : Kore.Axiom :=
  { sortVars := [KoreAML.Rv], pattern := .implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl), attributes := [] }

theorem clause_item_mem {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl = []) (hpre : cl.pre = .top) (hexs : cl.exs = []) :
    KoreAML.trAxiom [] [] ⟨0, "kernel", clauseAxiom c fn cl⟩ ∈ fnItems c := by
  unfold fnItems
  refine List.mem_flatMap.mpr ⟨fn, hfn, ?_⟩
  unfold kernelItems
  refine List.mem_filterMap.mpr ⟨clauseEquation c fn cl, ?_, by rw [clauseEquation_top hpre hexs]; rfl⟩
  unfold fnEquationsK
  exact List.mem_map.mpr ⟨cl, hcl, by simp [prioEquation, hlow]⟩

theorem fn_sig_mem {fn : Fn} (hfn : fn ∈ c.allFns) : fn.sig ∈ kernelSyms c := by
  unfold kernelSyms
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨fn, hfn, rfl⟩))))

theorem sortsOf_length : ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss → ws.length = ss.length
  | [], ss, h => by rw [sortsOf_nil] at h; cases h; rfl
  | w :: ws, ss, h => by
    obtain ⟨s, ss', _, h2, rfl⟩ := sortsOf_cons.mp h
    simp [sortsOf_length h2]

theorem sortsOfTerms_length {x : TermCtx} {vars : List Srt} :
    ∀ {ts : List Term} {ss : List Srt}, sortsOfTerms x vars ts = some ss → ts.length = ss.length
  | [], ss, h => by rw [sortsOfTerms_nil.mp h]; rfl
  | t :: ts, ss, h => by
    obtain ⟨s, ss', _, h2, rfl⟩ := sortsOfTerms_cons.mp h
    simp [sortsOfTerms_length h2]

/-- The value the valuation of a clause's equation gives a key: the sort `σr` to the sort
variable `R`, the argument's element to `Xⱼ`, the value's element to the clause's variable `i`. -/
noncomputable def clauseVal [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (σr : M)
    (nargs nvars : Nat) (ws : List GroundTerm) (σ' : Subst) : VarKey → M
  | .sortVar _ => σr
  | .evar n _ => match xIdx nargs n with
    | some j => elemOf c I (ws.getD j default)
    | none => match varIdx nvars n with
      | some i => match σ'.lookup i with
        | some v => elemOf c I v
        | none => default
      | none => default
  | .svar _ _ => default

/-- A free variable of a clause equation's conclusion side `rhs ∧ ens` is one of the
right-hand side's or the `ensures`'. -/
theorem freeOf_clauseConclRight {fn : Fn} {cl : Clause} {k : VarKey}
    (hk : k ∈ KoreAML.freeOf [] (clauseRight c fn cl)) :
    ∃ i, (i ∈ varOccs cl.rhs ∨ ∃ t, cl.ens = some t ∧ i ∈ varOccs t) ∧
      k = KoreAML.evarKey ((canonVars c cl.vars).getD i default).kore := by
  unfold clauseRight at hk
  rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
  simp only [List.append_nil, List.mem_append] at hk
  rcases hk with hk | hk
  · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ cl.rhs hk
    exact ⟨i, .inl hi, rfl⟩
  · cases hq : cl.ens with
    | none =>
      rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
        exact ⟨i, .inr ⟨t, rfl, hi⟩, rfl⟩
      · rw [KoreAML.freeOf] at hk; cases hk

/-- **A clause's equation, read in a model.** At arguments of `f`'s sorts that the clause's
patterns match under a well-sorted σ', where its `requires` holds, `f` applied to the arguments'
elements is what the right-hand side denotes under σ'. The results for the `requires` and the
right-hand side are taken as hypotheses (`ihreq`, `ihrhs`), at every valuation that agrees with σ'. -/
theorem clause_eq [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
    (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
    {f : Sym} {fn : Fn} (hfn : c.lookupFn f = some fn) {cl : Clause} (hcl : cl ∈ fn.clauses)
    (hlow : lowerClauses fn cl = []) (hpre : cl.pre = .top) (hexs : cl.exs = [])
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    {σ' : Subst} (hσ' : c.WellSorted cl.vars σ') (hmatch : PatVals c σ' cl.pats ws)
    (hplain : plainPats c cl.pats = true) (hpats : sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args)
    (hbinds : ∀ i < cl.vars.length, i ∈ varOccsList cl.pats)
    (hreqv : ∀ t, cl.req = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    (hrhsv : ∀ i ∈ varOccs cl.rhs, i < cl.vars.length)
    (hensv : ∀ t, cl.ens = some t → ∀ i ∈ varOccs t, i < cl.vars.length)
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihreq : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ t, cl.req = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
        (den c (bool true)).interpret I e m)
    (ihrhs : ∀ (tbl : VarTable) (e : Valuation M), Agrees c I tbl (canonVars c cl.vars) σ' e →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m)
    (e0 : Valuation M) (m : M) :
    (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e0 m ↔ Res c I e0 r m := by
  obtain ⟨hfnm, hlab⟩ := lookupFn_spec hfn
  subst hlab
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  have hnum := hnn.2.2 fn hfnm
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnum fn.result (List.mem_cons_self ..))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hlen : ws.length = fn.args.length := sortsOf_length hws
  have hplen : (Term.koreList c (canonVars c cl.vars) cl.pats).length = (fn.args.map c.sortName).length := by
    rw [koreList_length, List.length_map]; exact sortsOfTerms_length hpats
  let vs := canonVars c cl.vars
  let l := (fn.args.map c.sortName).zip (Term.koreList c vs cl.pats)
  let tbl : VarTable := KoreAML.tableOf (clauseAxiom c fn cl).sortVars (clauseAxiom c fn cl).pattern
  let e' : Valuation M := valOf tbl (clauseVal c I σr fn.args.length cl.vars.length ws σ')
  have hvarsP : ∀ k, k ∈ KoreAML.varsOf (KoreAML.argsConj 0 l) → k ∈ tbl := fun k hk => by
    refine List.mem_eraseDups.mpr (List.mem_append_right _ ?_)
    unfold clauseAxiom; dsimp only
    rw [KoreAML.varsOf]; unfold clausePrem premise
    rw [KoreAML.varsOf, KoreAML.varsOfList, KoreAML.varsOfList, KoreAML.varsOfList]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hk))))
  have hRmem : VarKey.sortVar "R" ∈ tbl :=
    List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hXmem : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      VarKey.evar ("X" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => by
    have hjl : j < (Term.koreList c vs cl.pats).length := by
      rw [hplen]; exact (List.getElem?_eq_some_iff.mp hj).1
    have hl : l[j]? = some (s, (Term.koreList c vs cl.pats)[j]) :=
      List.getElem?_zip_eq_some.mpr ⟨hj, List.getElem?_eq_getElem hjl⟩
    have := varsOf_argsConj_X l 0 j s _ hl
    rw [Nat.zero_add] at this
    exact hvarsP _ this
  have hVmem : ∀ i, i < cl.vars.length → canonKey c cl.vars i ∈ tbl := fun i hi => by
    have h1 := varsOf_koreList c vs cl.pats (hbinds i hi)
    obtain ⟨p', hp', hk⟩ := varsOfList_mem h1
    have hp'' : p' ∈ l.map Prod.snd := by
      rw [List.map_snd_zip (Nat.le_of_eq hplen)]; exact hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp''
    exact hvarsP _ (varsOf_argsConj_pat l 0 hq hk)
  have hRv : ∀ a, (KoreAML.trSort tbl KoreAML.R).interpret I e' a ↔ a = σr := fun a => by
    rw [trSort_R, KoreAML.interp_evar, valOf_ev hRmem]; rfl
  have hXv : ∀ j s w, (fn.args.map c.sortName)[j]? = some s → ws[j]? = some w →
      e'.evalEvar (tbl.ev (.evar ("X" ++ toString j) (KoreAML.srt s))) = elemOf c I w := fun j s w hj hw => by
    have hjn : j < fn.args.length := by simpa using (List.getElem?_eq_some_iff.mp hj).1
    rw [valOf_ev (hXmem j s hj)]
    simp only [clauseVal]
    rw [xIdx_eq hjn]
    dsimp only
    rw [List.getD_eq_getElem?_getD, hw]; rfl
  have hVv : ∀ i, i < cl.vars.length → e'.evalEvar (tbl.ev (canonKey c cl.vars i)) =
      (match σ'.lookup i with | some v => elemOf c I v | none => default) := fun i hi => by
    rw [valOf_ev (hVmem i hi), canonKey_eq c hi]
    simp only [clauseVal]
    rw [xIdx_var, varIdx_eq hi]
  have hvsort : ∀ i, i < cl.vars.length → ∃ v, σ'.lookup i = some v ∧ c.sortOf v = some (cl.vars.getD i 0) :=
    fun i hi => hσ' i _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl)
  have hag : Agrees c I tbl vs σ' e' := fun i v hi hl m => by
    rw [canonVars_length] at hi
    show m = e'.evalEvar (tbl.ev (canonKey c cl.vars i)) ↔ _
    rw [hVv i hi, hl]
    obtain ⟨w, hw, hsw⟩ := hvsort i hi
    rw [hl] at hw; cases hw
    exact ((elemOf_spec hI hsw e').1 m).symm
  have hargsort : ∀ j s w, (fn.args.map c.sortName)[j]? = some s → ws[j]? = some w →
      ∃ a, s = c.sortName a ∧ c.sortOf w = some a := fun j s w hj hw => by
    rw [List.getElem?_map] at hj
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hj
    obtain ⟨w', hw', hsw'⟩ := sortsOf_get hws ha
    rw [hw] at hw'; cases hw'
    exact ⟨a, rfl, hsw'⟩
  have hfree : ∀ k, k ∈ KoreAML.freeOf [] (clauseAxiom c fn cl).pattern →
      (∃ j s, (fn.args.map c.sortName)[j]? = some s ∧ k = .evar ("X" ++ toString j) (KoreAML.srt s)) ∨
        ∃ i, i < cl.vars.length ∧ k = canonKey c cl.vars i := fun k hk => by
    unfold clauseAxiom at hk; dsimp only at hk
    rw [KoreAML.freeOf] at hk
    rcases List.mem_append.mp hk with hk | hk
    · unfold clausePrem premise at hk
      rw [KoreAML.freeOf, KoreAML.freeOfList, KoreAML.freeOfList, KoreAML.freeOfList] at hk
      simp only [List.append_nil, List.mem_append] at hk
      rcases hk with hk | hk
      · cases hq : cl.req with
        | none =>
          rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
        | some t =>
          rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
          rw [KoreAML.freeOf] at hk
          rcases List.mem_append.mp hk with hk | hk
          · obtain ⟨i, hi, rfl⟩ := freeOf_kore c vs t hk
            exact Or.inr ⟨i, hreqv t hq i hi, rfl⟩
          · rw [KoreAML.freeOf] at hk; cases hk
      · rcases freeOf_argsConj l 0 hk with ⟨n, s, p, hn, rfl⟩ | ⟨q, hq, hk⟩
        · exact Or.inl ⟨n, s, (List.getElem?_zip_eq_some.mp hn).1, by rw [Nat.zero_add]⟩
        · have hq2 := (List.of_mem_zip (a := q.1) (b := q.2) hq).2
          obtain ⟨i, hi, rfl⟩ := freeOf_koreList c vs cl.pats (mem_freeOfList hq2 hk)
          exact Or.inr ⟨i, varOccsList_lt cl.pats hpats i hi, rfl⟩
    · unfold clauseConcl at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · rw [freeOf_symApp] at hk
        obtain ⟨n, s, hn, rfl⟩ := freeOf_callX _ 0 hk
        exact Or.inl ⟨n, s, hn, by rw [Nat.zero_add]⟩
      · obtain ⟨i, hi, rfl⟩ := freeOf_clauseConclRight hk
        exact Or.inr ⟨i, hi.elim (hrhsv i) fun ⟨t, ht, hi⟩ => hensv t ht i hi, rfl⟩
  have hg : ∀ k ∈ ((clauseAxiom c fn cl).sortVars.map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (clauseAxiom c fn cl).pattern).eraseDups, ∀ m,
      (KoreAML.guardOf tbl k).interpret I e' m := by
    intro k hk m'
    rcases List.mem_append.mp (List.mem_eraseDups.mp hk) with hk | hk
    · obtain ⟨_, h1, rfl⟩ := List.mem_map.mp hk
      rw [mem_one h1]
      show (KoreAML.guardOf tbl (.sortVar "R")).interpret I e' m'
      rw [KoreAML.interp_guard_sortVar hD, valOf_ev hRmem]
      exact hσr2
    · rcases hfree k hk with ⟨j, s, hj, rfl⟩ | ⟨i, hi, rfl⟩
      · rw [KoreAML.interp_guard_evar hD, trSort_srt]
        obtain ⟨w, hw, -⟩ : ∃ w, ws[j]? = some w ∧ True := by
          have hjn : j < ws.length := by rw [hlen]; simpa using (List.getElem?_eq_some_iff.mp hj).1
          exact ⟨_, List.getElem?_eq_getElem hjn, trivial⟩
        obtain ⟨a, rfl, hsw⟩ := hargsort j s w hj hw
        rw [hXv j _ w hj hw]
        exact (elemOf_spec hI hsw e').2
      · obtain ⟨w, hw, hsw⟩ := hvsort i hi
        have hk := canonKey_eq c hi
        rw [hk, KoreAML.interp_guard_evar hD, trSort_srt, ← hk, hVv i hi, hw]
        exact (elemOf_spec hI hsw e').2
  have hall' : ∀ a, Inh I σr a →
      ((KoreAML.tr ⟨tbl, []⟩ (symApp c fn.label
        (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' a ↔
        (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e' a) := fun m0 hm0 => by
    have hax := sat_fns hI (Or.inl ⟨_, clause_item_mem hfnm hcl hlow hpre hexs, rfl⟩)
    have hP := (KoreAML.trAxiom_at hD hax e' hg m0).mpr (by
      show (KoreAML.inhOf (KoreAML.trSort tbl KoreAML.R)).interpret I e' m0
      rw [KoreAML.interp_inhOf_of hRv]; exact hm0)
    have hP' : (KoreAML.tr ⟨tbl, []⟩ (.implies KoreAML.R (clausePrem c fn cl) (clauseConcl c fn cl))).interpret I e' m0 := hP
    rw [KoreAML.tr, KoreAML.interp_sImp] at hP'
    obtain ⟨-, himp⟩ := hP'
    have hprem := himp (by
      unfold clausePrem premise
      rw [tr_and2, KoreAML.interp_sAnd]
      refine ⟨?_, argsConj_den hI hnn.1 htr hσ' (canonVars_length c cl.vars) hag hRv hσr2 hm0 hmatch fn.args 0
        hplain hpats (fun s hs => hnum s (List.mem_cons_of_mem _ hs)) ?_⟩
      · cases hq : cl.req with
        | none =>
          simp only [Option.map_none, reqPat]
          rw [KoreAML.tr, KoreAML.interp_sTop hD isFree_R, KoreAML.interp_inhOf_of hRv]
          exact hm0
        | some t =>
          simp only [Option.map_some, reqPat]
          rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hRv hσB2 hσr2]
          refine ⟨hm0, fun a _ => ?_⟩
          rw [ihreq tbl e' hag t hq a, KoreAML.tr_dv]
          unfold den KoreAML.den bool
          rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
          exact Iff.rfl
      · intro k s w hk hw m'
        rw [Nat.zero_add]
        obtain ⟨w', hw', hsw⟩ := sortsOf_get hws hk
        rw [hw] at hw'; cases hw'
        rw [hXv k (c.sortName s) w (by rw [List.getElem?_map, hk]; rfl) hw]
        exact ((elemOf_spec hI hsw e').1 m').symm)
    unfold clauseConcl at hprem
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσr1) hRv hσr2 hσr2] at hprem
    obtain ⟨-, hall⟩ := hprem
    exact hall m0 hm0
  have hcall : ∀ m, (KoreAML.den (symApp c fn.label (GroundTerm.koreList c ws))).interpret I e0 m ↔
      (KoreAML.tr ⟨tbl, []⟩ (symApp c fn.label
        (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' m := by
    intro m
    unfold KoreAML.den
    rw [tr_symApp, tr_symApp]
    refine call_congr (e0 := e0) (e' := e') (fn.args.map c.sortName) ws 0 _ _ (by rw [List.length_map]; exact hlen)
      (fun k s w hk hw m => ?_) (fun m => symHead_congr (e := e0) (e' := e') _ m) m
    rw [Nat.zero_add, hXv k s w hk hw]
    obtain ⟨a, -, hsw⟩ := hargsort k s w hk hw
    exact (elemOf_spec hI hsw e0).1 m
  have harity : ∀ a, (KoreAML.tr ⟨tbl, []⟩ (symApp c fn.label
      (KoreAML.vars (KoreAML.numbered "X" 0 (fn.args.map c.sortName))))).interpret I e' a → Inh I σr a := by
    intro a ha
    refine (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσr1).mp (symArity_at hI (fn_sig_mem hfnm) e' a ?_)
    rw [tr_symApp] at ha
    have := call_arity (fn.args.map c.sortName) 0 _ (symHead c fn.label) a ha
      (fun k s hk => ?_) (fun _ h => h)
    · exact this
    · rw [Nat.zero_add]
      obtain ⟨w, hw, -⟩ : ∃ w, ws[k]? = some w ∧ True := by
        have hjn : k < ws.length := by rw [hlen]; simpa using (List.getElem?_eq_some_iff.mp hk).1
        exact ⟨_, List.getElem?_eq_getElem hjn, trivial⟩
      obtain ⟨b, rfl, hsw⟩ := hargsort k s w hk hw
      rw [hXv k _ w hk hw]
      exact (elemOf_spec hI hsw e').2
  constructor
  · intro hm
    have h1 := (hcall m).mp hm
    have h2 := (hall' m (harity m h1)).mp h1
    exact (Res_closed r e' e0 m).mp ((ihrhs tbl e' hag m).mp h2)
  · intro hm
    have hm' := (Res_closed r e0 e' m).mp hm
    have hin : Inh I σr m := by
      cases r with
      | none => exact hm.elim
      | some v =>
        have hsv := hr v rfl
        have hs := elemOf_spec hI hsv e'
        rw [(hs.1 m).mp hm']
        exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσr1).mp hs.2
    exact (hcall m).mpr ((hall' m hin).mpr ((ihrhs tbl e' hag m).mpr hm'))

section
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c)
include hI hnn

/-- **A clause's right side `rhs ∧ ens`, read in a model**, where its `ensures` denotes `true` (or
it has none): what the right-hand side denotes, a value of the result sort or nothing. -/
theorem right_iff {fn : Fn} (hfnm : fn ∈ c.allFns) {cl : Clause} {tbl : VarTable} {e : Valuation M}
    {r : Option GroundTerm} (hr : ∀ v, r = some v → c.sortOf v = some fn.result)
    (ihrhs : ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) cl.rhs)).interpret I e m ↔
      Res c I e r m)
    (ihens : ∀ t, cl.ens = some t → ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c cl.vars) t)).interpret I e m ↔
      (den c (bool true)).interpret I e m) :
    ∀ m, (KoreAML.tr ⟨tbl, []⟩ (clauseRight c fn cl)).interpret I e m ↔ Res c I e r m := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σr, hσr1, hσr2⟩ := sortSing hI (hnn.2.2 fn hfnm fn.result (List.mem_cons_self ..))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hS : ∀ b, (KoreAML.trSort tbl (srtOf c fn.result)).interpret I e b ↔ b = σr := by
    unfold srtOf; rw [trSort_srt]; exact hσr1
  intro m
  unfold clauseRight
  rw [tr_and2, KoreAML.interp_sAnd, ihrhs m]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have hin : Inh I σr m := by
    cases r with
    | none => exact h.elim
    | some v =>
      have hs := elemOf_spec hI (hr v rfl) e
      rw [(hs.1 m).mp h]
      exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσr1).mp hs.2
  cases hq : cl.ens with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hS]
    exact hin
  | some t =>
    simp only [Option.map_some, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hS hσB2 hσr2]
    refine ⟨hin, fun b _ => ?_⟩
    rw [ihens t hq b, KoreAML.tr_dv]
    show (den c (bool true)).interpret I e b ↔ _
    unfold den KoreAML.den bool
    rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
    exact Iff.rfl

end

/-- What `sortedOK` says of a clause of a function of the semantics (the user's or a sort
predicate's): its patterns have the argument sorts, each of its variables occurs in it (its
patterns, its conditions, its right-hand side, its `ensures` or its right side's predicate), its
`requires` is a Bool, its right-hand side has the result sort and its `ensures` is a Bool, over
some functions' signatures `L`. -/
theorem clause_ctxOccE (hok : c.sortedOK = true) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧
      (∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
        (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) ∧
      ∃ L, HeadsOK c L ∧ (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧
        sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
        (∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) := by
  rcases List.mem_append.mp hfn with hu | hp
  · replace hok := Semantics.sortedOK_sorted hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    have h2 := hok.1.2 fn hu cl hcl
    simp only [Semantics.clauseSorted, Bool.and_eq_true, beq_iff_eq] at h2
    replace h2 := h2.1
    obtain ⟨⟨⟨⟨⟨hpats, hb⟩, hreq⟩, hrhs⟩, hens⟩, -⟩ := h2
    refine ⟨sortsOfTerms_all_of_nf hpats, fun i hi => ?_, c.fns.map Fn.sig, fun k hk => ?_, fun t ht => ?_, hrhs, fun t ht => ?_⟩
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      exact hb i hi
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
    · rw [ht] at hreq
      simpa [reqOK] using hreq
    · rw [ht] at hens
      simpa [reqOK] using hens
  · obtain ⟨hpats, -, hb, hreq, hrhs, hens⟩ := sortPreds_ctx hp cl hcl
    refine ⟨sortsOfTerms_heads c.patCtx (c.collPatSigs ++ c.ovlSigs) cl.vars cl.pats hpats, fun i hi => ?_, [],
      fun k hk => absurd hk List.not_mem_nil, fun t ht => ?_, hrhs, fun t ht => ?_⟩
    · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (hb i hi))))
    · rw [ht] at hreq
      simpa [reqOK] using hreq
    · rw [ht] at hens
      simpa [reqOK] using hens

/-- `clause_ctxOccE` where every clause's patterns bind every variable (`hbc`): its patterns have
the argument sorts and bind every variable, its `requires` is a Bool, its right-hand side has the
result sort and its `ensures` is a Bool, over some functions' signatures `L`. -/
theorem clause_ctxE (hok : c.sortedOK = true)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true)
    {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ (∀ i < cl.vars.length, i ∈ varOccsList cl.pats) ∧
      ∃ L, HeadsOK c L ∧ (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧
        sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result ∧
        (∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) := by
  obtain ⟨h1, -, L, h3, h4, h5, h6⟩ := clause_ctxOccE hok hfn hcl
  refine ⟨h1, fun i hi => ?_, L, h3, h4, h5, h6⟩
  rcases List.mem_append.mp hfn with hu | hp
  · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hbc
    exact hbc fn hu cl hcl i hi
  · obtain ⟨-, -, hb, -⟩ := sortPreds_ctx hp cl hcl
    simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
    exact hb i hi

/-- A clause of a function of a semantics whose clauses' predicates are `\top` (`clausesPreTop`)
has the premise predicate `\top`: the user's by the check, the generated sort predicates' by their
text. -/
theorem clause_preTop (hpreTop : c.clausesPreTop = true) (_hok : c.sortedOK = true) {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause}
    (hcl : cl ∈ fn.clauses) : cl.pre = .top :=
  Semantics.allFns_preTop hpreTop fn hfn cl hcl

/-- A clause of a function of a semantics `sortedOK` accepts, whose clauses' patterns bind every
variable, has no existential variable: the user's because an existential variable is outside the
left side (`clauseExOK`), the generated sort predicates' by their text. -/
theorem clause_exsNil (hok : c.sortedOK = true)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true)
    {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) : cl.exs = [] := by
  rcases List.mem_append.mp hfn with hu | hp
  · exact Semantics.exs_nil_of_patBinds (Semantics.sortedOK_clauseEx hok hu hcl).1 (hbc fn hu cl hcl)
  · exact Semantics.sortPreds_exs hp cl hcl

/-- `clause_ctxE` without the `ensures`. -/
theorem clause_ctx (hok : c.sortedOK = true)
    (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true)
    {fn : Fn} (hfn : fn ∈ c.allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    sortsOfTerms c.patCtxAll cl.vars cl.pats = some fn.args ∧ (∀ i < cl.vars.length, i ∈ varOccsList cl.pats) ∧
      ∃ L, HeadsOK c L ∧ (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx L) cl.vars t = some Srt.bool) ∧
        sortOfTerm (c.rhsCtx L) cl.vars cl.rhs = some fn.result :=
  let ⟨h1, h2, L, h3, h4, h5, _⟩ := clause_ctxE hok hbc hfn hcl
  ⟨h1, h2, L, h3, h4, h5⟩

/-- A semantics `okM` accepts has clauses whose patterns bind every variable (`clauseOK`). -/
theorem _root_.KCore.Semantics.okM_clauseBinds {c : Semantics} (h : c.okM = true) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true := by
  intro fn hfn cl hcl
  simp only [Semantics.okM, Bool.and_eq_true] at h
  have hf := h.1.1.2
  simp only [Semantics.fnsOK, Semantics.fnOK, Bool.and_eq_true, List.all_eq_true] at hf
  have h2 := (hf fn hfn).1 cl hcl
  simp only [Semantics.clauseOK, Bool.and_eq_true] at h2
  exact h2.1.1.1.2

/-- A semantics `ok` accepts has clauses whose patterns bind every variable (`clauseOK`). -/
theorem _root_.KCore.Semantics.ok_clauseBinds {c : Semantics} (h : c.ok = true) :
    ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true :=
  Semantics.okM_clauseBinds (Semantics.okM_of_ok h)

/-- The sort predicates' right-hand sides are domain values. -/
theorem sortPreds_rhs {fn : Fn} (hfn : fn ∈ c.sortPreds) : ∀ cl ∈ fn.clauses, ∃ s lit, cl.rhs = .dv s lit := by
  simp only [Semantics.sortPreds, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_filterMap, Option.map_eq_some_iff] at hfn
  rcases hfn with rfl | rfl | ⟨X, _, _, _, rfl⟩ <;> intro cl hcl <;>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcl
  · subst hcl; exact ⟨_, _, rfl⟩
  · rcases hcl with rfl | rfl <;> exact ⟨_, _, rfl⟩
  · rcases hcl with rfl | rfl <;> exact ⟨_, _, rfl⟩

/-- Every function's clauses are match independent: `Hyp` says so of the user's, and a sort
predicate's right-hand side has no variable. -/
theorem MatchIndependentAll_of (hy : HypCore c) : MatchIndependentAll c := by
  intro f fn hfn cl hcl
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · exact hy.2.2.2.2.2.1 fn hu cl hcl
  · refine ⟨fun vs σ σ' _ _ _ _ _ _ _ => ?_, fun hne => absurd (Semantics.sortPreds_exs hp cl hcl) hne⟩
    refine Or.inl ⟨Semantics.sortPreds_exs hp cl hcl, Semantics.sortPreds_exs hp cl hcl, rfl, rfl,
      fun i hi => absurd hi ?_, fun t ht => ?_⟩
    · obtain ⟨s', lit, hr⟩ := sortPreds_rhs hp cl hcl
      rw [hr, varOccs]
      exact List.not_mem_nil
    · rw [sortPreds_ens hp cl hcl] at ht; cases ht

/-- The clauses of one priority are coherent: `Hyp` says each user function's equations agree and
its clauses are match independent; a sort predicate's two clauses are of different priorities. -/
theorem CoherentAll_of (hy : HypCore c) : CoherentAll c :=
  coherentAll_of_parts (MatchIndependentAll_of hy) fun f fn hfn => by
    obtain ⟨hmem, -⟩ := lookupFn_spec hfn
    rcases List.mem_append.mp hmem with hu | hp
    · exact hy.2.2.2.2.1 fn hu
    · exact sortPreds_agree hp

/-- **Every function has at most one result where its equations agree and its clauses are match
independent**: the user's functions by the
hypotheses, a sort predicate's because its right-hand sides have no variable and its clauses
agree. Nothing else of the semantics is read. -/
theorem fnDet_of_agree {c : Semantics} (h3 : ∀ fn ∈ c.fns, ClausesAgree c fn)
    (h4 : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, MatchIndependent c cl) : FnDet c :=
  fnDet_of_coherent (coherentAll_of_parts (fun f fn hfn cl hcl => by
      obtain ⟨hmem, -⟩ := lookupFn_spec hfn
      rcases List.mem_append.mp hmem with hu | hp
      · exact h4 fn hu cl hcl
      · refine ⟨fun vs σ σ' _ _ _ _ _ _ _ => ?_, fun hne => absurd (Semantics.sortPreds_exs hp cl hcl) hne⟩
        refine Or.inl ⟨Semantics.sortPreds_exs hp cl hcl, Semantics.sortPreds_exs hp cl hcl, rfl, rfl,
          fun i hi => absurd hi ?_, fun t ht => ?_⟩
        · obtain ⟨s', lit, hr⟩ := sortPreds_rhs hp cl hcl
          rw [hr, varOccs]
          exact List.not_mem_nil
        · rw [sortPreds_ens hp cl hcl] at ht; cases ht)
    fun f fn hfn => by
      obtain ⟨hmem, -⟩ := lookupFn_spec hfn
      rcases List.mem_append.mp hmem with hu | hp
      · exact h3 fn hu
      · exact sortPreds_agree hp)

/-- **Where every function has at most one result, a clause is `Witnessed` exactly where some
values satisfy its conditions**: the second half of `Witnessed`'s `requires` conjunct (no result
but `true`) is then the functionality of `EvalTerm`. -/
theorem _root_.KCore.Clause.witnessedDet_iff_of_fnDet {c : Semantics} (hd : FnDet c) (cl : Clause) :
    cl.Witnessed c ↔
      ∃ σ, c.WellSortedAt cl.vars cl.condVars σ ∧
        (∀ t, cl.req = some t → EvalTerm c σ t (some (bool true))) ∧ Holds c cl.vars.length σ cl.pre true :=
  ⟨fun ⟨σ, h1, h2, h3⟩ => ⟨σ, h1, fun t ht => (h2 t ht).1, h3⟩,
   fun ⟨σ, h1, h2, h3⟩ =>
    ⟨σ, h1, fun t ht => ⟨h2 t ht, fun _ hr => EvalTerm.functional_of_fnDet hd hr (h2 t ht)⟩, h3⟩⟩

theorem heads_app {f : Sym} {ts : List Term} {P : Sym → Prop} (h : ∀ g ∈ Term.heads (.app f ts), P g) :
    P f ∧ ∀ g ∈ Term.headsList ts, P g := by
  rw [Term.heads] at h
  exact ⟨h f (List.mem_cons_self ..), fun g hg => h g (List.mem_cons_of_mem _ hg)⟩

theorem kore_app_plain (hnm : NamesPlain c) {vs : List KoreAML.Var} {f : Sym} {k0 : CtorSig}
    (h0 : lookupSig c.ctorSigs f = some k0) (ts : List Term) {t : VarTable} :
    KoreAML.tr ⟨t, []⟩ (Term.kore c vs (.app f ts)) =
      KoreAML.trArgs ⟨t, []⟩ (KoreAML.sym (.symbol (c.symName f))) (Term.koreList c vs ts) := by
  rw [kore_app, tr_symApp]; unfold symHead; rw [iteSort_ctor hnm h0]

theorem injApp_empty {e : Valuation M} {A B : String} {φ : KoreAML.P} (h : ∀ m, ¬ φ.interpret I e m) (m : M) :
    ¬ (KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ]).interpret I e m := by
  simp only [KoreAML.appList]
  intro hm
  obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm
  exact h b hb

/-- In the model `I`, an overloading symbol applied to the elements of values of its argument sorts
is: where no function overload covers them, the element of their normal form (`norm`); where the
function overload `kg` covers them, what `kg`'s application to the elements of the stripped
arguments is, lifted to the symbol's result sort (nothing where that application denotes nothing).
Every model of `Γ` has it (`normDen_of`, FaithfulNeg.lean). -/
def NormDen [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) : Prop :=
  (∀ {f : Sym} {o : OvlSig} {ws : List GroundTerm}, c.lookupOvl f = some o → c.sortsOf ws = some o.sig.args →
    c.fnCover f ws = none → ∀ (e : Valuation M) m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔
      (den c (c.norm f ws)).interpret I e m) ∧
  ∀ {f : Sym} {o : OvlSig} {ws : List GroundTerm} {kg : CtorSig} {r : Option GroundTerm},
    c.lookupOvl f = some o → c.sortsOf ws = some o.sig.args → c.fnCover f ws = some kg →
    iteSort? (c.symName kg.name) = none → (∀ v, r = some v → c.sortOf v = some kg.result) →
    ∀ (e : Valuation M),
      (∀ m, (KoreAML.den (symApp c kg.name (GroundTerm.koreList c (stripAll kg.args o.sig.args ws)))).interpret I e m ↔
        Res c I e r m) →
      ∀ m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔
        Res c I e (r.map (lift kg.result o.sig.result)) m

section
variable [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (hnn : NamesNumbered c) (hsc : SortCtx c) (hst : Stage1 c)
  (hok : c.sortedOK = true) (hbc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, binds cl.vars.length (varOccsList cl.pats) = true) (hmi : CoherentAll c) (hnd : NormDen c I)
include hI hnn hsc hst hok hbc hmi hnd

mutual
  /-- **L3, functions.** A function of the semantics that is callable in the first stage, at
  arguments of its sorts, applied to their elements, is what its result denotes. -/
  theorem eval_den (hpreTop : c.clausesPreTop = true) : ∀ {f : Sym} {ws : List GroundTerm} {r : Option GroundTerm}, Eval c f ws r →
      ∀ {fn : Fn}, c.lookupFn f = some fn → c.sortsOf ws = some fn.args → Callable c f →
      ∀ (e : Valuation M) m, (KoreAML.den (symApp c f (GroundTerm.koreList c ws))).interpret I e m ↔ Res c I e r m
    | _, _, _, .clause (fn := fn') (cl := cl) (σ := σ') hfn' hcl hσ' hmatch hreq _ _ _ hrhs hens _, fn, hfn, hws, hcall, e, m => by
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hlows, -⟩ := hcall fn' hfn
      have hol := hlows cl hcl
      have hmem := (lookupFn_spec hfn).1
      obtain ⟨hpats, hbinds, L, hL, hreqs, hrhss, henss⟩ := clause_ctxE hok hbc hmem hcl
      obtain ⟨hplain, hcalls⟩ := hst.2.2 fn' hmem cl hcl
      have hr : ∀ v, _ = some v → c.sortOf v = some fn'.result := fun v hv => EvalTerm.sorted hsc hrhs hL hσ' hrhss hv
      exact clause_eq hI hnn hsc.trans hfn hcl hol (clause_preTop (hpreTop := hpreTop) hok hmem hcl) (clause_exsNil hok hbc hmem hcl) hws hσ' hmatch hplain hpats hbinds
        (fun t ht => varOccs_lt t (hreqs t ht)) (varOccs_lt _ hrhss) (fun t ht => varOccs_lt t (henss t ht)) hr
        (fun tbl e' hag t ht m' => evalTerm_den (hpreTop := hpreTop) (hreq t ht) hL hσ' (canonVars_length c cl.vars) hag (hreqs t ht)
          (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_right _ (by rw [ht]; exact hg)))) m')
        (fun tbl e' hag => right_iff hI hnn hmem hr
          (fun m' => evalTerm_den (hpreTop := hpreTop) hrhs hL hσ' (canonVars_length c cl.vars) hag hrhss
            (fun g hg => hcalls g (List.mem_append_left _ (List.mem_append_left _ hg))) m')
          (fun t ht m' => evalTerm_den (hpreTop := hpreTop) (hens t ht) hL hσ' (canonVars_length c cl.vars) hag (henss t ht)
            (fun g hg => hcalls g (List.mem_append_right _ (by rw [ht]; exact hg))) m'))
        e m
    | _, _, _, .rest (fn := fn') hfn' hnone, fn, hfn, hws, _, e, m => by
      rw [hfn] at hfn'; cases hfn'
      obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
      have h := rest_den hI hmem hws hnone e m
      rwa [hlab] at h
    | _, _, _, h@(.ensFails ..), fn, hfn, hws, hcall, e, m => by
      -- a callable function has a value at every argument list of its sorts, so none is its result
      obtain ⟨v, hv⟩ := (hcall fn hfn).2 _ hws
      exact absurd (Eval.functional hmi h hv) (by simp)
    | _, _, _, .clauseEx (fn := fn') hfn' hcl _ _ _ _ _ hne _ _ _ _, fn, hfn, _, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok hbc (lookupFn_spec hfn).1 hcl) hne
    | _, _, _, .exNone (fn := fn') hfn' hcl hne _ _ _ _ _ _ _, fn, hfn, _, _, _, _ => by
      rw [hfn] at hfn'; cases hfn'
      exact absurd (clause_exsNil hok hbc (lookupFn_spec hfn).1 hcl) hne
  termination_by structural _ _ _ h => h
  /-- **L3, terms.** A well-sorted right-hand side or `requires` whose symbols are callable in the
  first stage, at a valuation that agrees with a well-sorted σ, translates to what its result
  under σ denotes: the value's element, or nothing where it is undefined. -/
  theorem evalTerm_den (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {t : Term} {r : Option GroundTerm}, EvalTerm c σ t r →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {s : Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortOfTerm (c.rhsCtx L) vars t = some s → (∀ f ∈ Term.heads t, CallsAll c (Callable c) f) →
      ∀ m, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e m ↔ Res c I e r m
    | _, _, _, .var (i := i), L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, _, m => by
      have hi := sortOfTerm_var.mp ht
      have hlt : i < vs.length := by rw [hvs]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨v, hv, -⟩ := hσ i s hi
      rw [hv, tr_var]
      exact hag i v hlt hv m
    | _, _, _, .dv (s := s') (lit := lit), _, _, vs, tbl, e, _, _, _, _, _, _, _, m => by
      show _ ↔ (den c (.dv s' lit)).interpret I e m
      rw [Term.kore]; unfold den KoreAML.den; rw [GroundTerm.kore]; unfold srtOf
      rw [KoreAML.tr_dv, KoreAML.tr_dv]
    | _, _, _, .inj (a := a) (b := b) (t := t) (r := r) h', L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨hab, ht', -⟩ := sortOfTerm_inj.mp ht
      rw [Term.heads] at hcall
      have ih := evalTerm_den (hpreTop := hpreTop) h' hL hσ hvs hag ht' hcall
      rw [Term.kore, KoreAML.tr_injP]
      cases r with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact injApp_empty (fun m h => ((ih m).mp h)) m
      | some w =>
        have hw := EvalTerm.sorted hsc h' hL hσ ht' rfl
        simp only [Option.map_some, Res]
        rcases injNormal_cases a b w with ⟨a', a'', w', rfl, hn⟩ | hn
        · rw [hn]
          obtain ⟨h1, -, h3, rfl⟩ := sortOf_inj.mp hw
          obtain ⟨x, hx, hxs⟩ := den_single hI h3 e
          rw [injApp_congr ih m]
          show (KoreAML.appList _ [_, _, den c (.inj a' a w')]).interpret I e m ↔ _
          rw [den_inj, den_inj]
          exact coh_at hI h1 hab hx hxs m
        · rw [hn, den_inj]
          exact injApp_congr ih m
    | _, _, _, .ctor (f := f) (ts := ts) (rs := rs) hk hts, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨k0, hk0⟩ := Option.isSome_iff_exists.mp hk
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app_plain hnn.1 hk0]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        simp only [Option.map_some, Res]
        rw [den_ctor]
        exact ih.1 ws hall _ _ (fun _ => Iff.rfl) m
    | _, _, _, .hook (f := f) (rs := rs) (r := r) hk hhk hts hh hund, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨hks, hkn⟩ := rhs_lookup_hook hk hhk hk'
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hund hall]
        simp only [Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hv := hh ws hall
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_hookRes hI hks hws (by rw [hkn]; exact hv)
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr]
        cases r with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .param (f := f) (rs := rs) (r := r) hk hhk hp hts hr, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨kp, hkp, rfl, hkn⟩ := rhs_lookup_param hk hhk hp hk'
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        rw [hr, hall]
        simp only [Option.bind_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        have hax := sat_dom hI (Or.inr (Or.inl ⟨kp, ws, hkp, hws, rfl⟩))
        have hgr := (KoreAML.interp_equal (defOK hI)).mp (hax e default) m
        rw [hkn] at hgr
        unfold KoreAML.den at hgr
        rw [tr_symApp] at hgr
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m, hgr, hr, hall]
        simp only [Option.bind_some]
        cases c.paramVal f ws with
        | none => simp [Res, Pattern.interpret]
        | some v => rfl
    | _, _, _, .call (f := f) (rs := rs) (vs := ws) hk hh hts hvs' hf hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨fn, hfnm, rfl, hlook⟩ := rhs_lookup_call hsc hL hk hh hp (Eval.lookupFn_ne hf) hk'
      obtain ⟨hcf, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := eval_den (hpreTop := hpreTop) hf hlook hws hcf.1 e m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .callUndef (f := f) (rs := rs) hk hh hts hvs' hp, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      simp only [Res, iff_false]
      exact ih.2 hvs' _ m
    | _, _, _, .ovlFn (f := f) (rs := rs) (vs := ws) (o := o) (kg := kg) (r := r) hk ho hts hvs' hlo hcov hf,
        L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o', hlo', rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      rw [hlo] at hlo'; cases hlo'
      obtain ⟨hcf, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      have hws := EvalTerms.sorted hsc hts hL hσ hargs hvs'
      obtain ⟨fn, hfn, hlook, hsig, hkg, hb, -, hus⟩ :=
        OvlLaws.fnCover_fn_ovlF ((inferInstance : OvlOK c).hyp hsc.trans).fnFacts hlo hws hcov
      have hname : kg.name = fn.label := by rw [hsig]
      have hres : kg.result = fn.result := by rw [hsig]
      have hgd := eval_den (hpreTop := hpreTop) hf hlook hus (hcf.2 o hlo kg hkg hb) e
      rw [kore_app, tr_symApp, ih.1 ws hvs' _ _ (fun _ => Iff.rfl) m]
      have := hnd.2 hlo hws hcov (namesNumbered_cover hnn hlo hcov)
        (fun v hv => by rw [hres]; exact Eval.sorted hsc hf hlook hus hv) e hgd m
      unfold KoreAML.den at this
      rw [tr_symApp] at this
      exact this
    | _, _, _, .ovl (f := f) (rs := rs) hk ho hts hnf, L, vars, vs, tbl, e, s, hL, hσ, hvs, hag, ht, hcall, m => by
      obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp ht
      obtain ⟨o, hlo, rfl⟩ := rhs_lookup_ovl hsc hL hk' ho
      obtain ⟨-, hcalls⟩ := heads_app hcall
      have ih := evalTerms_den (hpreTop := hpreTop) hts hL hσ hvs hag hargs hcalls
      rw [kore_app, tr_symApp]
      cases hall : allSome rs with
      | none =>
        simp only [Option.map_none, Res, iff_false]
        exact ih.2 hall _ m
      | some ws =>
        have hws := EvalTerms.sorted hsc hts hL hσ hargs hall
        simp only [Option.map_some, Res]
        rw [ih.1 ws hall _ _ (fun _ => Iff.rfl) m]
        have := hnd.1 hlo hws (hnf ws hall) e m
        unfold KoreAML.den at this
        rw [tr_symApp] at this
        exact this
  termination_by structural _ _ _ h => h
  theorem evalTerms_den (hpreTop : c.clausesPreTop = true) : ∀ {σ : Subst} {ts : List Term} {rs : List (Option GroundTerm)}, EvalTerms c σ ts rs →
      ∀ {L : List CtorSig} {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M} {ss : List Srt},
      HeadsOK c L → c.WellSorted vars σ → vs.length = vars.length → Agrees c I tbl vs σ e →
      sortsOfTerms (c.rhsCtx L) vars ts = some ss → (∀ f ∈ Term.headsList ts, CallsAll c (Callable c) f) →
      (∀ ws, allSome rs = some ws → ∀ (acc acc' : KoreAML.P), (∀ m, acc.interpret I e m ↔ acc'.interpret I e m) →
        ∀ m, (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m ↔
          (KoreAML.trArgs ⟨[], []⟩ acc' (GroundTerm.koreList c ws)).interpret I e m) ∧
      (allSome rs = none → ∀ (acc : KoreAML.P) m, ¬ (KoreAML.trArgs ⟨tbl, []⟩ acc (Term.koreList c vs ts)).interpret I e m)
    | _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => by
      refine ⟨fun ws hws acc acc' hacc m => ?_, fun h => by simp [allSome] at h⟩
      simp only [allSome, Option.some.injEq] at hws
      subst hws
      rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_nil, KoreAML.trArgs_nil]
      exact hacc m
    | _, _, _, .cons (t := t) (ts := ts) (r := r) (rs := rs) h hs, L, vars, vs, tbl, e, ss, hL, hσ, hvs, hag, ht, hcall => by
      obtain ⟨s, ss', h1, h2, -⟩ := sortsOfTerms_cons.mp ht
      rw [Term.headsList] at hcall
      have ih1 := evalTerm_den (hpreTop := hpreTop) h hL hσ hvs hag h1 (fun g hg => hcall g (List.mem_append_left _ hg))
      have ih2 := evalTerms_den (hpreTop := hpreTop) hs hL hσ hvs hag h2 (fun g hg => hcall g (List.mem_append_right _ hg))
      constructor
      · intro ws hws acc acc' hacc m
        simp only [allSome, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hws
        obtain ⟨w, rfl, ws', hws', rfl⟩ := hws
        rw [Term.koreList, GroundTerm.koreList, KoreAML.trArgs_cons, KoreAML.trArgs_cons]
        exact ih2.1 ws' hws' _ _ (KoreAML.interp_app_congr hacc ih1) m
      · intro hn acc m
        rw [Term.koreList, KoreAML.trArgs_cons]
        cases r with
        | none =>
          exact trArgs_empty (fun m' hm' => by
            obtain ⟨_, b, _, hb, _⟩ := KoreAML.interp_app.mp hm'
            exact (ih1 b).mp hb) _ m
        | some w =>
          cases hrs : allSome rs with
          | none => exact ih2.2 hrs _ m
          | some ws' => simp [allSome, hrs] at hn
  termination_by structural _ _ _ h => h
end

end

end

/-! ## L4. A rule's step -/

section
variable {c : Semantics} {M : Type} {I : Interpretation KoreAML.Sym M}

/-- The valuation of a rule's axiom gives the rule's variable `i` its value's element. -/
noncomputable def ruleVal [Inhabited M] (c : Semantics) (I : Interpretation KoreAML.Sym M) (nvars : Nat)
    (σ : Subst) : VarKey → M
  | .evar n _ => match varIdx nvars n with
    | some i => match σ.lookup i with
      | some v => elemOf c I v
      | none => default
    | none => default
  | _ => default

/-- What `sortedOK` says of a rule. -/
theorem rule_ctx (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) :
    sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort ∧
      (∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort := by
  replace hok := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have h := hok.2 r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, hreq⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hrhs⟩ := h
  replace hl := sortOfTerm_all_of_nf hl
  refine ⟨hl, fun t ht => ?_, hrhs⟩
  · rw [ht] at hreq
    simpa [reqOK] using hreq

/-- What `sortedOK` says of a rule's `ensures`: a Bool. -/
theorem rule_ctx_ens (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) :
    ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
  replace hok := Semantics.sortedOK_sorted hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have h := hok.2 r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at h
  intro t ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hens⟩, -⟩, -⟩, -⟩, -⟩ := h
  rw [ht] at hens
  simpa [reqOK] using hens

theorem fns_headsOK : HeadsOK c (c.fns.map Fn.sig) := fun k hk => by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
  exact ⟨g, List.mem_append_left _ hg, rfl⟩

theorem top_numbered : topCellSort < nRegSorts + c.sortNames.length :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)

/-- The axiom of a rule without competitors (`prioRuleK` with no rule of a smaller priority). -/
def ruleAxiom (c : Semantics) (r : Rule) : Kore.Axiom :=
  let C := srtOf c topCellSort
  let vs := canonVars c r.vars
  let right : Kore.Pattern := .and C [Term.kore c vs r.rhs, reqPat C (r.ens.map (Term.kore c vs))]
  { sortVars := [],
    pattern := .rewrites C (.and C [Term.kore c vs r.lhs, reqPat C (r.req.map (Term.kore c vs)),
      .ceil C C right]) right,
    attributes := [] }

/-- A configuration's element is in the configuration sort, as a rule's axiom writes it. -/
theorem elemOf_top [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] (x : Config c) (tbl : VarTable) (e : Valuation M) :
    (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e (elemOf c I x.val) := by
  unfold srtOf; rw [trSort_srt]; exact (elemOf_spec hI x.property e).2

/-- `⌈rhs⌉` at the configuration sort holds of every element of that sort where `rhs` denotes a
configuration's element: the premise of a rule's axiom that its right-hand side is defined. -/
theorem ceil_rhs_at [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] {tbl : VarTable} {e : Valuation M} {φ : Kore.Pattern}
    {y : Config c} (hφ : ∀ b, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e b ↔ (den c y.val).interpret I e b)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a) :
    (KoreAML.tr ⟨tbl, []⟩ (.ceil (srtOf c topCellSort) (srtOf c topCellSort) φ)).interpret I e a := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  obtain ⟨b, hb, hbs⟩ := den_single hI y.property e
  have hφs : ∀ b', (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e b' → Inh I σC b' := fun b' hb' => by
    rw [(hb b').mp ((hφ b').mp hb')]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) hσC1).mp hbs
  rw [KoreAML.tr, KoreAML.interp_sCeil hD hc hSC hSC hσC2 hσC2 hφs]
  exact ⟨⟨b, (hφ b).mpr ((hb b).mpr rfl)⟩, (KoreAML.interp_inhOf_of hSC).mp ha⟩

/-- A `requires` or an `ensures` that evaluates to `true` holds of every element of the
configuration sort: `reqPat` is `⊤` without one and `⌈t = true⌉` with one. -/
theorem reqPat_holds [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] {tbl : VarTable} {e : Valuation M}
    {vs : List KoreAML.Var} {q : Option Term}
    (hq : ∀ t, q = some t → ∀ b, (KoreAML.tr ⟨tbl, []⟩ (Term.kore c vs t)).interpret I e b ↔
      (den c (bool true)).interpret I e b)
    {a : M} (ha : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a) :
    (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c topCellSort) (q.map (Term.kore c vs)))).interpret I e a := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σC, hσC1, hσC2⟩ := sortSing hI (top_numbered (c := c))
  obtain ⟨σB, hσB1, hσB2⟩ := sortSing hI (bool_numbered (c := c))
  rw [sortName_bool] at hσB1
  have hSC : ∀ b, (KoreAML.trSort tbl (srtOf c topCellSort)).interpret I e b ↔ b = σC := by
    unfold srtOf; rw [trSort_srt]; exact hσC1
  have haC : Inh I σC a := (KoreAML.interp_inhOf_of hSC).mp ha
  cases hqq : q with
  | none =>
    simp only [Option.map_none, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of hSC]
    exact haC
  | some t =>
    simp only [Option.map_some, reqPat]
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (by rw [trSort_srt]; exact hσB1) hSC hσB2 hσC2]
    refine ⟨haC, fun b _ => ?_⟩
    rw [hq t hqq b, KoreAML.tr_dv]
    show (den c (bool true)).interpret I e b ↔ _
    unfold den KoreAML.den bool
    rw [GroundTerm.kore, sortName_bool, KoreAML.tr_dv]
    exact Iff.rfl

/-- A rule's right side `rhs ∧ ens` denotes the configuration the right-hand side denotes, where
`ens` holds of every element of the configuration sort. -/
theorem right_den [Inhabited M] (hI : I ⊧ᴵP Γ c) [OvlOK c] {tbl : VarTable} {e : Valuation M}
    {φ ψ : Kore.Pattern} {y : Config c}
    (hφ : ∀ b, (KoreAML.tr ⟨tbl, []⟩ φ).interpret I e b ↔ (den c y.val).interpret I e b)
    (hψ : ∀ a, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c topCellSort))).interpret I e a →
      (KoreAML.tr ⟨tbl, []⟩ ψ).interpret I e a) :
    ∀ b, (KoreAML.tr ⟨tbl, []⟩ (.and (srtOf c topCellSort) [φ, ψ])).interpret I e b ↔
      (den c y.val).interpret I e b := by
  intro b
  rw [tr_and2, KoreAML.interp_sAnd]
  refine ⟨fun h => (hφ b).mp h.1, fun h => ⟨(hφ b).mpr h, hψ b ?_⟩⟩
  obtain ⟨b0, hb0, hbs⟩ := den_single hI y.property e
  rw [(hb0 b).mp h]
  unfold srtOf; rw [trSort_srt]; exact hbs

/-- The free variables of a rule's left-hand side, `requires`, right-hand side and `ensures` are
its own. -/
theorem freeOf_rule_parts (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) {k : VarKey}
    (hk : k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.lhs) ∨
      k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.req.map (Term.kore c (canonVars c r.vars)))) ∨
      k ∈ KoreAML.freeOf [] (Term.kore c (canonVars c r.vars) r.rhs) ∨
      k ∈ KoreAML.freeOf [] (reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars))))) :
    ∃ i < r.vars.length, k = canonKey c r.vars i := by
  obtain ⟨hlhs, hreqs, hrhss⟩ := rule_ctx hok hr
  have hens := rule_ctx_ens hok hr
  rcases hk with hk | hk | hk | hk
  · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.lhs hk
    exact ⟨i, varOccs_lt r.lhs hlhs i hi, rfl⟩
  · cases hq : r.req with
    | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
        exact ⟨i, varOccs_lt t (hreqs t hq) i hi, rfl⟩
      · rw [KoreAML.freeOf] at hk; cases hk
  · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ r.rhs hk
    exact ⟨i, varOccs_lt r.rhs hrhss i hi, rfl⟩
  · cases hq : r.ens with
    | none => rw [hq] at hk; simp only [Option.map_none, reqPat] at hk; rw [KoreAML.freeOf] at hk; cases hk
    | some t =>
      rw [hq] at hk; simp only [Option.map_some, reqPat] at hk
      rw [KoreAML.freeOf] at hk
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨i, hi, rfl⟩ := freeOf_kore c _ t hk
        exact ⟨i, varOccs_lt t (hens t hq) i hi, rfl⟩
      · rw [KoreAML.freeOf] at hk; cases hk

/-- The free variables of a rule's right side `rhs ∧ ens` are its own. -/
theorem freeOf_right (hok : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) {k : VarKey}
    (hk : k ∈ KoreAML.freeOf [] (.and (srtOf c topCellSort) [Term.kore c (canonVars c r.vars) r.rhs,
      reqPat (srtOf c topCellSort) (r.ens.map (Term.kore c (canonVars c r.vars)))])) :
    ∃ i < r.vars.length, k = canonKey c r.vars i := by
  simp only [KoreAML.freeOf, KoreAML.freeOfList, List.append_nil, List.mem_append] at hk
  exact freeOf_rule_parts hok hr (Or.inr (Or.inr hk))

end

end Faithful

end KCore
