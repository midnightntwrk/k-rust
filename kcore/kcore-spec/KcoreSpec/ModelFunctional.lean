/-
  KCore. The value model satisfies the functional axiom of every `[total]` function.

  `Γ` has no axiom `∃y. f(x̄) = y` for a function declared `total`: totality enters the
  statements only as the second conjunct of `FnHyp`. This module shows that the model that
  `sound_hyp` builds for the model conjunct of `SoundC` (the value model `stdI`, `has_model_core`)
  satisfies that axiom, in the form `emit` writes it for a `total` function (`functionalAx`, the
  sentence `∃Val:s. Val = f(K0, …, Kn)` over the sort variable `R`, translated as `Γ`'s axioms are),
  for every function of `c.fns` declared `total`, at every valuation: `trAxiom`'s guards put each
  `Kj` in its argument sort, which in the value model holds exactly the values of that sort, and
  there `FnHyp` gives `f` a value, of the result sort (subject reduction), and only that one
  (coherence).

  So `Γ c ∪ Γstep c` together with the functional axioms of the `total` functions (`ΓTotal`) has a
  model whenever `coreOK` and `FnHyp` hold (`has_model_total`): the model conjunct of `SoundC`
  holds for the theory with the text's totality axioms as well. Adding axioms keeps every theorem,
  so `SoundC`'s step conjunct and `CompleteC` hold of the larger theory too (`sound_total`,
  `complete_total`).

  The functional axiom reads no step, so it holds in the value model at every transition
  (`AtT.sat_functional`, `AtT.sat_total`). For rules with `ruleSorted` and `rulePlainHeldH` over
  any set of symbols (the conjunct is carried, not read), whose axioms the value model satisfies at
  a transition between `StepV` steps (`stdI_T_model_heldCEx`), the theory with the totality axioms has
  that model (`has_model_total_core_held`, `sound_total_held`); under `FnHyp` every condition has a
  truth value, `StepV` is `StepM` (`stepV_iff_stepM`), and the model is `stdI`
  (`has_model_total_held`).
-/
import KcoreSpec.ModelChoiceHeld
import KcoreSpec.Sound

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

open ML

variable {c : Semantics}

/-! ## The functional axiom of a function -/

/-- The functional axiom of `fn` as `emit` writes it for a `[total]` function:
`∃Val:s. Val =_{s,R} f(K0, …)` over the sort variable `R` (`functionalAx`). -/
def functionalAxiom (c : Semantics) (fn : Fn) : Kore.Axiom :=
  { sortVars := [KoreAML.Rv]
    pattern := .exist KoreAML.R (KoreAML.evar "Val" (KoreAML.srt (c.sortName fn.result)))
      (.equals (KoreAML.srt (c.sortName fn.result)) KoreAML.R
        (.var (.evar (KoreAML.evar "Val" (KoreAML.srt (c.sortName fn.result)))))
        (KoreAML.ap (c.symName fn.label) (KoreAML.vars (KoreAML.numbered "K" 0 (fn.args.map c.sortName)))))
    attributes := [KoreAML.attr "functional"] }

/-- It is the sentence `functionalAx` builds. -/
theorem functionalAx_eq (fn : Fn) :
    KoreAML.functionalAx (c.symName fn.label) (fn.args.map c.sortName) (c.sortName fn.result) =
      .axiom (functionalAxiom c fn) := rfl

/-- The functional axiom of `fn`, translated as `Γ`'s axioms are (`kernelItems`). -/
def functionalItem (c : Semantics) (fn : Fn) : KoreAML.Item :=
  KoreAML.trAxiom [] [] ⟨0, "kernel", functionalAxiom c fn⟩

theorem kernelItems_functionalAx (fn : Fn) :
    kernelItems [KoreAML.functionalAx (c.symName fn.label) (fn.args.map c.sortName) (c.sortName fn.result)] =
      [functionalItem c fn] := rfl

/-- **The totality axioms**: the functional axiom of each function of `c` declared `total`. -/
def ΓTotal (c : Semantics) : Premises KoreAML.Sym :=
  KoreAML.itemsPremises ((c.fns.filter (·.total)).map (functionalItem c))

/-! ## Variables named `pre0, pre1, …` -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

theorem numbered_read (pre : String) {tbl : KoreAML.VarTable} {e : Valuation Elem} :
    ∀ (ss : List String) (ws : List GroundTerm) (j : Nat), ss.length = ws.length →
    (∀ (n : Nat) (w : GroundTerm) (s : String), ws[n]? = some w → ss[n]? = some s →
      e.evalEvar (tbl.ev (.evar (pre ++ toString (j + n)) (KoreAML.srt s))) = .val w) →
    All2 (fun φ x => ∀ m, φ.interpret (stdI_T c T) e m ↔ m = x)
      ((KoreAML.vars (KoreAML.numbered pre j ss)).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map Elem.val)
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | s :: ss, w :: ws, j, hl, hX => by
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    refine .cons (fun m => ?_) ?_
    · rw [KoreAML.tr, KoreAML.interp_evar]
      have := hX 0 w s rfl rfl
      rw [Nat.add_zero] at this
      exact Iff.of_eq (congrArg (m = ·) this)
    · have := numbered_read pre ss ws (j + 1) (by simpa using hl)
        (fun n w' s' h1 h2 => by
          have := hX (n + 1) w' s' (by simpa using h1) (by simpa using h2)
          rwa [show j + (n + 1) = j + 1 + n by omega] at this)
      simpa [KoreAML.vars] using this

end AtT

theorem numbered_read (pre : String) {tbl : KoreAML.VarTable} {e : Valuation Elem} :
    ∀ (ss : List String) (ws : List GroundTerm) (j : Nat), ss.length = ws.length →
    (∀ (n : Nat) (w : GroundTerm) (s : String), ws[n]? = some w → ss[n]? = some s →
      e.evalEvar (tbl.ev (.evar (pre ++ toString (j + n)) (KoreAML.srt s))) = .val w) →
    All2 (fun φ x => ∀ m, φ.interpret (stdI c) e m ↔ m = x)
      ((KoreAML.vars (KoreAML.numbered pre j ss)).map (KoreAML.tr ⟨tbl, []⟩)) (ws.map Elem.val) :=
  AtT.numbered_read (c := c) (T := StepM c) pre (tbl := tbl) (e := e)

theorem numbered_mem_free (pre : String) (b : List KoreAML.VarKey)
    (hb : ∀ (n : Nat) (s : String), KoreAML.VarKey.evar (pre ++ toString n) (KoreAML.srt s) ∉ b) :
    ∀ (ss : List String) (j n : Nat) (s : String), ss[n]? = some s →
    KoreAML.VarKey.evar (pre ++ toString (j + n)) (KoreAML.srt s) ∈
      KoreAML.freeOfList b (KoreAML.vars (KoreAML.numbered pre j ss))
  | [], _, _, _, h => by simp at h
  | s' :: ss, j, 0, s, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.freeOfList, KoreAML.freeOf]
    have : b.contains (KoreAML.evarKey (KoreAML.evar (pre ++ toString j) (KoreAML.srt s'))) = false := by
      show b.contains (KoreAML.VarKey.evar (pre ++ toString j) (KoreAML.srt s')) = false
      simpa using hb j s'
    rw [this, Nat.add_zero]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  | s' :: ss, j, n + 1, s, h => by
    simp only [List.getElem?_cons_succ] at h
    have := numbered_mem_free pre b hb ss (j + 1) n s h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.freeOfList]
    rw [show j + (n + 1) = j + 1 + n by omega]
    exact List.mem_append_right _ (by simpa [KoreAML.vars] using this)

theorem numbered_mem_vars (pre : String) : ∀ (ss : List String) (j n : Nat) (s : String), ss[n]? = some s →
    KoreAML.VarKey.evar (pre ++ toString (j + n)) (KoreAML.srt s) ∈
      KoreAML.varsOfList (KoreAML.vars (KoreAML.numbered pre j ss))
  | [], _, _, _, h => by simp at h
  | s' :: ss, j, 0, s, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.varsOfList, KoreAML.varsOf, Nat.add_zero]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  | s' :: ss, j, n + 1, s, h => by
    simp only [List.getElem?_cons_succ] at h
    have := numbered_mem_vars pre ss (j + 1) n s h
    simp only [KoreAML.numbered, KoreAML.vars, List.map_cons, Function.comp]
    rw [KoreAML.varsOfList]
    rw [show j + (n + 1) = j + 1 + n by omega]
    exact List.mem_append_right _ (by simpa [KoreAML.vars] using this)

/-- The arguments `pre0, pre1, …` in the inhabitants of the argument sorts are values. -/
theorem argsP_of (pre : String) {tbl : KoreAML.VarTable} {e : Valuation Elem} {args : List Srt}
    (hin : ∀ (j : Nat) (hj : j < args.length),
      InSort c (args[j]'hj) (e.evalEvar (tbl.ev (.evar (pre ++ toString j) (KoreAML.srt (c.sortName (args[j]'hj))))))) :
    ∃ ws, c.sortsOf ws = some args ∧ ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w →
      (args.map c.sortName)[j]? = some s → e.evalEvar (tbl.ev (.evar (pre ++ toString j) (KoreAML.srt s))) = .val w := by
  let ws := (List.range args.length).map fun j => toVal (e.evalEvar (tbl.ev (.evar (pre ++ toString j)
    (KoreAML.srt (c.sortName (args.getD j 0))))))
  have hget : ∀ j (hj : j < args.length), ws[j]? = some (toVal (e.evalEvar (tbl.ev (.evar (pre ++ toString j)
      (KoreAML.srt (c.sortName (args[j]'hj))))))) := fun j hj => by
    simp [ws, List.getElem?_map, List.getElem?_range hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hval : ∀ j (hj : j < args.length), ∃ v, e.evalEvar (tbl.ev (.evar (pre ++ toString j)
      (KoreAML.srt (c.sortName (args[j]'hj))))) = .val v ∧ c.sortOf v = some (args[j]'hj) :=
    fun j hj => inSort_val (hin j hj)
  have hlen : ws.length = args.length := by simp [ws]
  refine ⟨ws, ?_, fun j w s hw hs => ?_⟩
  · have : ∀ (l : List Srt) (wl : List GroundTerm), wl.length = l.length →
        (∀ j (hj : j < l.length) w, wl[j]? = some w → c.sortOf w = some (l[j]'hj)) → c.sortsOf wl = some l := by
      intro l
      induction l with
      | nil => intro wl hl _; rw [List.length_eq_zero_iff.mp hl]; exact sortsOf_nil
      | cons a l ih =>
        intro wl hl hs
        cases wl with
        | nil => simp at hl
        | cons w wl =>
          exact sortsOf_cons.mpr ⟨a, l, hs 0 (by simp) w rfl, ih wl (by simpa using hl)
            (fun j hj w' hw' => hs (j + 1) (by simpa using hj) w' (by simpa using hw')), rfl⟩
    refine this args ws hlen fun j hj w hw => ?_
    rw [hget j hj] at hw
    obtain ⟨v, hv, hsv⟩ := hval j hj
    rw [hv] at hw
    cases hw
    exact hsv
  · have hj : j < args.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hw).1
    rw [hget j hj] at hw
    rw [List.getElem?_map, List.getElem?_eq_getElem hj] at hs
    cases hs
    obtain ⟨v, hv, -⟩ := hval j hj
    rw [hv] at hw ⊢
    cases hw
    rfl

theorem val_ne_K (j : Nat) : "Val" ≠ "K" ++ toString j := by
  intro h
  have := congrArg String.toList h
  rw [String.toList_append] at this
  simp at this

/-! ## The functional axiom holds in the value model -/

namespace AtT

variable {T : GroundTerm → GroundTerm → Prop}

/-- **The call `f(K0, …)`** in the value model at a transition, at a valuation giving the variables the arguments' values: the values
`Eval` gives. -/
theorem callK_read (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {tbl : KoreAML.VarTable} {e : Valuation Elem}
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hK : ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("K" ++ toString j) (KoreAML.srt s))) = .val w) (b : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
      (KoreAML.vars (KoreAML.numbered "K" 0 (fn.args.map c.sortName))))).interpret (stdI_T c T) e b ↔
      ∃ v, b = .val v ∧ Eval c fn.label ws (some v) := by
  obtain ⟨hc, hh, hp⟩ := h.fnApart hfn
  have hl : ws.length = fn.args.length := sortsOf_len hws
  rw [tr_ap_tbl, interp_symList _ _ (ws.map Elem.val)
    (numbered_read "K" _ ws 0 (by simp [hl]) (fun n w s h1 h2 => by rw [Nat.zero_add]; exact hK n w s h1 h2)) b]
  rw [show c.symName fn.label = c.symName fn.sig.name from rfl,
    symE_vals h.namesK (fn_sig_mem hfn) (by rw [hl]; rfl) b]
  exact result_fn (k := fn.sig) hc hh hp (c.isOvl_of_lookupFn (h.lookupFn hfn)) b

/-- **The value model at a transition satisfies the functional axiom of every `[total]` function** whose totality
`hv` gives (`FnHyp`'s second conjunct). -/
theorem sat_functional (h : HypModelCore c)
    (hv : ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v))
    {fn : Fn} (hfn : fn ∈ c.fns) (ht : fn.total = true) :
    stdI_T c T ⊧ᴵ (functionalItem c fn).pat := by
  have hn := h.namesK
  have hfnA : fn ∈ c.allFns := List.mem_append_left _ hfn
  have hfs := h.fnSorts hfnA
  have hres := hfs fn.result (List.mem_cons_self ..)
  have hmi := h.det
  intro e m
  unfold functionalItem KoreAML.trAxiom
  dsimp only
  generalize hP : (functionalAxiom c fn).pattern = P
  have hsortP : KoreAML.sortOf [] P = some KoreAML.R := by rw [← hP]; rfl
  simp only [hsortP]
  rw [interpret_impl]
  intro hgs
  have hsv : (functionalAxiom c fn).sortVars = [KoreAML.Rv] := rfl
  rw [hsv] at hgs ⊢
  generalize htb : KoreAML.tableOf [KoreAML.Rv] P = tbl at hgs ⊢
  have hvarsP : ∀ k ∈ KoreAML.varsOf P, k ∈ tbl := fun k hk => by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hguard : ∀ k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups,
      (KoreAML.guardOf tbl k).interpret (stdI_T c T) e m := fun k hk =>
    conjList_elim hgs _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  have hfreeP : ∀ k ∈ KoreAML.freeOf [] P, k ∈ (([KoreAML.Rv].map KoreAML.sortVarKey) ++ KoreAML.freeOf [] P).eraseDups :=
    fun k hk => List.mem_eraseDups.mpr (List.mem_append_right _ hk)
  have hRmem : KoreAML.VarKey.sortVar "R" ∈ tbl := by
    rw [← htb]; exact List.mem_eraseDups.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩))
  have hRs : KoreAML.IsSort (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) := by
    have := hguard (.sortVar "R") (List.mem_eraseDups.mpr (List.mem_append_left _
      (List.mem_map.mpr ⟨KoreAML.Rv, List.mem_singleton_self _, rfl⟩)))
    obtain ⟨s, hs, he⟩ := sortGuard_iff.mp this
    rw [he]; exact (isSort_iff _).mpr ⟨s, hs, rfl⟩
  -- the names of the pattern
  let S := KoreAML.srt (c.sortName fn.result)
  let kV : KoreAML.VarKey := .evar "Val" S
  let call := KoreAML.ap (c.symName fn.label) (KoreAML.vars (KoreAML.numbered "K" 0 (fn.args.map c.sortName)))
  have hPeq : P = .exist KoreAML.R (KoreAML.evar "Val" S)
      (.equals S KoreAML.R (.var (.evar (KoreAML.evar "Val" S))) call) := by rw [← hP]; rfl
  have hcallF : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("K" ++ toString j) (KoreAML.srt s) ∈ KoreAML.freeOf [] P := fun j s hj => by
    rw [hPeq, KoreAML.freeOf, KoreAML.freeOf]
    refine List.mem_append_right _ ?_
    show _ ∈ KoreAML.freeOf _ (KoreAML.ap _ _)
    unfold KoreAML.ap
    rw [KoreAML.freeOf]
    have h1 := numbered_mem_free "K" [kV] (fun n s' he => by
      rw [List.mem_singleton] at he
      injection he with he
      exact val_ne_K n he.symm) _ 0 j s hj
    rwa [Nat.zero_add] at h1
  have hKk : ∀ j s, (fn.args.map c.sortName)[j]? = some s →
      KoreAML.VarKey.evar ("K" ++ toString j) (KoreAML.srt s) ∈ tbl := fun j s hj => by
    refine hvarsP _ ?_
    rw [hPeq, KoreAML.varsOf, KoreAML.varsOf]
    refine List.mem_append_right _ (List.mem_append_right _ ?_)
    show _ ∈ KoreAML.varsOf (KoreAML.ap _ _)
    unfold KoreAML.ap
    rw [KoreAML.varsOf]
    refine List.mem_append_right _ ?_
    have := numbered_mem_vars "K" _ 0 j s hj
    rwa [Nat.zero_add] at this
  have hVk : kV ∈ tbl := by
    refine hvarsP _ ?_
    rw [hPeq, KoreAML.varsOf]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨ws, hws, hwsK⟩ := argsP_of "K" (tbl := tbl) (e := e) (args := fn.args) (fun j hj => by
    have hs : (fn.args.map c.sortName)[j]? = some (c.sortName (fn.args[j]'hj)) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hg := hguard _ (hfreeP _ (hcallF j _ hs))
    rw [KoreAML.interp_guard_evar defOK_std, trSort_srt] at hg
    exact (inhOf_sort hn (hfs _ (List.mem_cons_of_mem _ (List.getElem_mem hj))) e _).mp hg)
  have hSres : ∀ (e' : Valuation Elem) b, (KoreAML.trSort tbl S).interpret (stdI_T c T) e' b ↔
      b = .srt fn.result := fun e' b => by rw [trSort_srt]; exact sort_den hn hres e' b
  have hresS : KoreAML.IsSort (stdI_T c T) (.srt fn.result) := (isSort_iff _).mpr ⟨fn.result, List.mem_range.mpr hres, rfl⟩
  -- the valuation with `Val` at x keeps `R` and the arguments
  let eV : Elem → Valuation Elem := fun x => ⟨Function.update e.evalEvar (tbl.ev kV) x, e.evalSvar⟩
  have hoff : ∀ x (k : KoreAML.VarKey), k ∈ tbl → k ≠ kV → (eV x).evalEvar (tbl.ev k) = e.evalEvar (tbl.ev k) :=
    fun x k hk hne => Function.update_noteq (fun he => hne (ev_inj hk hVk he)) _ _
  have heR : ∀ x, (eV x).evalEvar (tbl.ev (.sortVar "R")) = e.evalEvar (tbl.ev (.sortVar "R")) :=
    fun x => hoff x _ hRmem (fun he => KoreAML.VarKey.noConfusion he)
  have heK : ∀ x, ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      (eV x).evalEvar (tbl.ev (.evar ("K" ++ toString j) (KoreAML.srt s))) = .val w := fun x j w s hw hs => by
    rw [hoff x _ (hKk j s hs) (by intro he; injection he with he; exact val_ne_K j he.symm)]
    exact hwsK j w s hw hs
  have heV : ∀ x, (eV x).evalEvar (tbl.ev kV) = x := fun x => Function.update_same _ _ _
  rw [KoreAML.interp_equal defOK_std]
  intro a
  rw [hPeq, KoreAML.tr, KoreAML.interp_inhOf_of (R_read e)]
  show (KoreAML.sExists (tbl.ev kV) (KoreAML.trSort tbl S)
    (KoreAML.tr ⟨tbl, []⟩ (.equals S KoreAML.R (.var (.evar (KoreAML.evar "Val" S))) call))).interpret (stdI_T c T) e a ↔ _
  rw [KoreAML.interp_sExists]
  have hbody : ∀ x, (KoreAML.tr ⟨tbl, []⟩ (.equals S KoreAML.R (.var (.evar (KoreAML.evar "Val" S))) call)).interpret
      (stdI_T c T) (eV x) a ↔ KoreAML.Inh (stdI_T c T) (e.evalEvar (tbl.ev (.sortVar "R"))) a ∧
        ∀ b, InSort c fn.result b → (b = x ↔ ∃ v, b = .val v ∧ Eval c fn.label ws (some v)) := fun x => by
    rw [KoreAML.tr, KoreAML.interp_sEquals defOK_std sat_ceilDef (hSres (eV x)) (R_read (eV x)) hresS
      (by rw [heR]; exact hRs), heR]
    refine and_congr Iff.rfl (forall_congr' fun b => ?_)
    rw [inh_srt]
    refine imp_congr Iff.rfl ?_
    have hx : (eV x).evalEvar (({ vars := tbl, aliases := [] } : KoreAML.Ctx).vars.ev
        (KoreAML.evarKey (KoreAML.evar "Val" S))) = x := heV x
    rw [KoreAML.tr, KoreAML.interp_evar, callK_read h hfnA hws (heK x) b, hx]
  constructor
  · rintro ⟨x, -, hx⟩
    exact ((hbody x).mp hx).1
  · intro ha
    obtain ⟨v, hv⟩ := hv fn hfn ht ws hws
    have hsv : c.sortOf v = some fn.result :=
      Eval.sorted (sortCtx_of_allClEx h.hyp.1 h.hyp.2.1 h.ovlCase) hv (h.lookupFn hfnA) hws rfl
    refine ⟨.val v, ?_, (hbody (.val v)).mpr ⟨ha, fun b _ => ?_⟩⟩
    · rw [KoreAML.interp_member defOK_std, heV, trSort_srt]
      exact (inhOf_sort hn hres _ _).mpr hsv
    · constructor
      · rintro rfl; exact ⟨v, rfl, hv⟩
      · rintro ⟨v', rfl, hv'⟩
        have := hmi _ _ _ _ hv' hv
        cases this
        rfl

/-- The totality axioms hold in the value model at a transition. -/
theorem sat_total (h : HypModelCore c)
    (hv : ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) :
    stdI_T c T ⊧ᴵP ΓTotal c := by
  refine sat_itemsPremises c fun it hit => ?_
  obtain ⟨fn, hfn, rfl⟩ := List.mem_map.mp hit
  obtain ⟨hfn, ht⟩ := List.mem_filter.mp hfn
  exact sat_functional h hv hfn ht

end AtT

/-- **The call `f(K0, …)`**, at a valuation giving the variables the arguments' values: the values
`Eval` gives. -/
theorem callK_read (h : HypModelCore c) {fn : Fn} (hfn : fn ∈ c.allFns) {tbl : KoreAML.VarTable} {e : Valuation Elem}
    {ws : List GroundTerm} (hws : c.sortsOf ws = some fn.args)
    (hK : ∀ (j : Nat) (w : GroundTerm) (s : String), ws[j]? = some w → (fn.args.map c.sortName)[j]? = some s →
      e.evalEvar (tbl.ev (.evar ("K" ++ toString j) (KoreAML.srt s))) = .val w) (b : Elem) :
    (KoreAML.tr ⟨tbl, []⟩ (KoreAML.ap (c.symName fn.label)
      (KoreAML.vars (KoreAML.numbered "K" 0 (fn.args.map c.sortName))))).interpret (stdI c) e b ↔
      ∃ v, b = .val v ∧ Eval c fn.label ws (some v) :=
  AtT.callK_read (T := StepM c) h hfn hws hK b

/-- **The value model satisfies the functional axiom of every `[total]` function** whose totality
`hv` gives (`FnHyp`'s second conjunct). -/
theorem sat_functional (h : HypModelCore c)
    (hv : ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v))
    {fn : Fn} (hfn : fn ∈ c.fns) (ht : fn.total = true) :
    stdI c ⊧ᴵ (functionalItem c fn).pat :=
  AtT.sat_functional (T := StepM c) h hv hfn ht

/-- The totality axioms hold in the value model. -/
theorem sat_total (h : HypModelCore c)
    (hv : ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v)) :
    stdI c ⊧ᴵP ΓTotal c :=
  AtT.sat_total (T := StepM c) h hv

variable {H : Sym → Bool}

/-- **`Γ` with the step's closure and the totality axioms has a model** under `HypModelCore`, for
rules with `ruleSorted` and `rulePlainHeldH`: the value model at a transition `T` that holds only steps
of `StepV` between configurations, every `StepVBy` step of a rule without existential variables,
and for each `StepVBy` step of a rule with existential variables one of its instances. -/
theorem has_model_total_core_held (h : HypModelCore c) (hp : ClausePreDecided c) (hq : ClausePostDecided c)
    (hl : OpenLaws c)
    (hv : ∀ fn ∈ c.fns, fn.total = true → ∀ vs, c.sortsOf vs = some fn.args → ∃ v, Eval c fn.label vs (some v))
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true)
    (T : GroundTerm → GroundTerm → Prop)
    (hsub : ∀ x y, c.sortOf x = some topCellSort → c.sortOf y = some topCellSort → T x y → StepV c x y)
    (hall : ∀ r σ x y, StepVBy c r σ x y → r.exs = [] → T x y)
    (hsome : ∀ r σ x y, StepVBy c r σ x y → r.exs ≠ [] → ∃ y' σ',
       (∀ i, ¬ i ∈ r.exs → σ'.lookup i = σ.lookup i) ∧ StepVBy c r σ' x y' ∧ T x y') :
    stdI_T c T ⊧ᴵP (Γ c ∪ Γstep c ∪ ΓTotal c) := by
  intro φ hφ
  rcases hφ with (hφ | hφ) | hφ
  · rcases hφ with (((((hφ | hφ) | hφ) | hφ) | hφ) | hφ) | hφ
    · exact AtT.satSigGoal h φ hφ
    · exact AtT.satConsGoal h hl φ hφ
    · exact AtT.satDomainsGoal h φ hφ
    · exact AtT.satCollsGoal h φ hφ
    · exact AtT.satFnsGoalEx h (hypModelCore_clsFactsCe h) hp hq φ hφ
    · exact satRulesGoal_held h hrules T hall hsome φ hφ
    · exact AtT.satFallbackGoal h φ hφ
  · exact satStepGoal_held h hrules T hsub φ hφ
  · exact AtT.sat_total h hv φ hφ

/-- **`StepVAt` is `StepMAt`** for a semantics that `coreOK` accepts where a term has at most one
result and every function terminates, whose rules are well sorted: `pre`, `post` and each
competitor's `pre` have truth values (`holds_decided`, `Rule.decided_pp`), which are the value
model's (`holds_trueV`). -/
theorem stepVAt_iff_stepMAt (hc : c.coreOK = true) (hfd : FnDet c) (hft : FnTerminates c)
    (hsr : ∀ r' ∈ c.rules, c.ruleSorted r' = true) {r : Rule} (hr : c.ruleSorted r = true)
    {σ : Subst} {x y : GroundTerm} : StepVAt c r σ x y ↔ StepMAt c r σ x y := by
  have hsc := hypSound_of_core hc
  obtain ⟨-, -, -, -, -, -, -, hokP, hokQ, -⟩ := ruleSorted_partsPP hr
  have happ : ∀ r' ∈ c.rules, (RuleAppliesV c r' x ↔ RuleApplies c r' x) := fun r' hr' =>
    ruleAppliesV_iff hfd fun σ' hσ' hm' _ => ((Faithful.Rule.decided_pp hsc hft (hsr r' hr') x).1 σ' hσ' hm').2
  constructor
  · rintro ⟨hσ, hm, hreq, hpre, hev, hens, hpost, hprio⟩
    have htrue : ∀ {p : Cond}, c.condOK r.vars p = true → TrueV c r.vars.length σ p →
        Holds c r.vars.length σ p true := fun {p} hok ht => by
      obtain ⟨b, hb⟩ := holds_decided hsc hft p hok (hσ.at _)
      rw [(holds_trueV hfd hb).mp ht] at hb
      exact hb
    exact ⟨hσ, hm, hreq, htrue hokP hpre, hev, hens, htrue hokQ hpost,
      fun r' hr' hlt ha => hprio r' hr' hlt ((happ r' hr').mpr ha)⟩
  · rintro ⟨hσ, hm, hreq, hpre, hev, hens, hpost, hprio⟩
    exact ⟨hσ, hm, hreq, (holds_trueV hfd hpre).mpr rfl, hev, hens, (holds_trueV hfd hpost).mpr rfl,
      fun r' hr' hlt ha => hprio r' hr' hlt ((happ r' hr').mp ha)⟩

/-- **`StepV` is `StepM`** under `stepVAt_iff_stepMAt`'s hypotheses. -/
theorem stepV_iff_stepM (hc : c.coreOK = true) (hfd : FnDet c) (hft : FnTerminates c)
    (hsr : ∀ r' ∈ c.rules, c.ruleSorted r' = true) {x y : GroundTerm} : StepV c x y ↔ StepM c x y := by
  rw [stepM_iff_by]
  constructor
  · rintro ⟨r, σ, hr, hb⟩; exact ⟨r, σ, hr, (stepVAt_iff_stepMAt hc hfd hft hsr (hsr r hr)).mp hb⟩
  · rintro ⟨r, σ, hr, hb⟩; exact ⟨r, σ, hr, (stepVAt_iff_stepMAt hc hfd hft hsr (hsr r hr)).mpr hb⟩

end Model

/-- **The value model satisfies `Γ`, the step's closure and the totality axioms**, for a semantics
that `coreOK` accepts whose functions meet `FnHyp` and whose rules have `ruleSorted` and
`rulePlainHeldH`: under `FnHyp` the value model's step `StepV` is `StepM`, the transition of `stdI`. -/
theorem has_model_total_held {c : Semantics} {H : Sym → Bool} (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) :
    Model.stdI c ⊧ᴵP (Γ c ∪ Γstep c ∪ Model.ΓTotal c) := by
  have hiff : ∀ {x y : GroundTerm}, Model.StepV c x y ↔ Model.StepM c x y :=
    Model.stepV_iff_stepM h (fnModel_of_fnHyp h hf).1 hf.1 (fun r hr => (hrules r hr).1)
  exact Model.has_model_total_core_held (hypModel_of_fnHyp h hf) (clausePreDecided_of_fnHyp h hf)
    (clausePostDecided_of_fnHypCEx (Semantics.coreOKEx_of_coreOK h) hf) hf.2.2.2.2.2 hf.2.1 hrules (Model.StepM c)
    (fun _ _ _ _ hT => hiff.mpr hT) (fun r σ _ _ hb _ => hiff.mp ⟨r, σ, hb⟩)
    (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, hiff.mp ⟨r, σ, hb⟩⟩)

/-- **The model conjunct of `SoundC` holds with the totality axioms**: for a semantics that
`coreOK` accepts and whose functions meet `FnHyp`, the value model satisfies `Γ c`, the step's
closure, and the functional axiom `∃y. f(x̄) = y` of every function declared `total`. -/
theorem has_model_total {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) :
    Model.stdI c ⊧ᴵP (Γ c ∪ Γstep c ∪ Model.ΓTotal c) :=
  has_model_total_held h hf (Semantics.ruleFactsHeld_of_core h)

/-- The functional axiom of each `total` function holds in the value model, under `coreOK` and
`FnHyp`, at every valuation. -/
theorem sat_functional_of_fnHyp {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) {fn : Fn}
    (hfn : fn ∈ c.fns) (ht : fn.total = true) : Model.stdI c ⊧ᴵ (Model.functionalItem c fn).pat :=
  Model.sat_functional (hypModel_of_fnHyp h hf) hf.2.1 hfn ht

/-- **Soundness with the totality axioms, for rules with `pre` and `post`**: `sound_total`'s
statement from the per-rule facts `ruleSorted` and `rulePlainHeldH`. The model is the value model at
its own step, `stdI_T c (StepV c)`. -/
theorem sound_total_held {c : Semantics} {H : Sym → Bool} (h : c.coreOK = true) (hf : FnHyp c)
    (hrules : ∀ r ∈ c.rules, c.ruleSorted r = true ∧ c.rulePlainHeldH H r = true) :
    (∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      I ⊧ᴵP (Γc c ∪ Γstep c ∪ Model.ΓTotal c)) ∧
    ∀ (x y : Config c) (r : Rule) (σ : Subst), StepBy c r σ x y →
      ((Γc c ∪ Model.ΓTotal c) ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧
      ((Γc c ∪ Model.ΓTotal c) ⊧ (den c y.val ⇒ famEx c r σ)) := by
  have hm : Model.stdI_T c (Model.StepV c) ⊧ᴵP (Γc c ∪ Γstep c ∪ Model.ΓTotal c) := by
    intro φ hφ
    rcases hφ with hφ | hφ
    · exact stdI_T_model_heldCEx c (hypModel_of_fnHyp h hf) (clausePreDecided_of_fnHyp h hf) (clausePostDecided_of_fnHypCEx (Semantics.coreOKEx_of_coreOK h) hf) hf.2.2.2.2.2 hrules (Model.StepV c)
        (fun _ _ _ _ hT => hT) (fun r σ _ _ hb _ => ⟨r, σ, hb⟩)
        (fun r σ _ y hb _ => ⟨y, σ, fun _ _ => rfl, hb, ⟨r, σ, hb⟩⟩) φ hφ
    · exact Model.AtT.sat_total (hypModel_of_fnHyp h hf) hf.2.1 φ hφ
  refine ⟨⟨_, inferInstance, _, hm⟩, fun x y r σ hs => ?_⟩
  obtain ⟨h1, h2⟩ := (sound_hyp c h hf).2 x y r σ hs
  refine ⟨?_, ?_⟩
  · intro M _ I hI
    exact h1 (fun φ hφ => hI φ (Or.inl hφ))
  · intro M _ I hI
    exact h2 (fun φ hφ => hI φ (Or.inl hφ))

/-- **Soundness with the totality axioms**: under `coreOK` and `FnHyp`, `Γc c`, the step's closure
and the totality axioms have a model, and `sound_hyp`'s two entailments at each step hold of `Γc c`
with the totality axioms (a theorem of `Γc c` is one of every larger theory). -/
theorem sound_total {c : Semantics} (h : c.coreOK = true) (hf : FnHyp c) :
    (∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      I ⊧ᴵP (Γc c ∪ Γstep c ∪ Model.ΓTotal c)) ∧
    ∀ (x y : Config c) (r : Rule) (σ : Subst), StepBy c r σ x y →
      ((Γc c ∪ Model.ΓTotal c) ⊧ (den c x.val ⇒ KoreAML.sNext (famEx c r σ))) ∧
      ((Γc c ∪ Model.ΓTotal c) ⊧ (den c y.val ⇒ famEx c r σ)) :=
  sound_total_held h hf (Semantics.ruleFactsHeld_of_core h)

/-- **Completeness with the totality axioms**: under `coreOK` and `FnHyp`, for an outcome function
that lists the outcomes at each configuration (`OutIs`), `complete_hyp`'s statement holds of
`Γc c ∪ Γstep c` with the totality axioms. -/
theorem complete_total {c : Semantics} (ref : OutFn) (h : c.coreOK = true) (hf : FnHyp c) :
    OutIs c ref → ∀ x : Config c, (Γc c ∪ Γstep c ∪ Model.ΓTotal c) ⊧
      (den c x.val ⇒ KoreAML.allNext (KoreAML.disjList ((ref x.val).map (Outcome.pat c)))) := by
  intro href x M _ I hI
  exact complete_hyp c ref h hf href x (fun φ hφ => hI φ (Or.inl hφ))

end Faithful

end KCore
