/-
  `transfer` (ConsTransfer.lean) at two premises of `Γ`:
  - the no-junk item of a collection whose sorts and symbols are outside `D` (`collNoJunk`, a
    least fixed point): it is of the class (`ownSorted_collNoJunk`), so the extension satisfies it
    where the model does (`transfer_collNoJunk`);
  - the translation of a sentence `axiom{R} \equals{S, R}(l, r)` (`transfer_trAxiom_equals`), and
    among those the idempotence sentence of an open generator (`transfer_idem`);
  - a function equation, with its sort variable, its premise `X0 ∈ A` and its guards
    (`transfer_fnEq`): the equation of the clause `f(A) = A` at a sort outside `D`.
-/
import KcoreSpec.ConsTransferR

set_option autoImplicit false

namespace KCore.Cons

open ML Faithful
open KoreAML (DefOK Inh IsSort)

section
variable {D : KoreAML.Sym → Prop}

/-- **The no-junk item of a collection is of the class**, where its sorts and its unit, element and
concatenation symbols are outside `D`. -/
theorem ownSorted_collNoJunk (c : Semantics) (k : CollSig)
    (hs : ¬ D (.sort ("Sort" ++ c.sortName k.sort))) (hkey : ¬ D (.sort ("Sort" ++ c.sortName k.key)))
    (hval : ¬ D (.sort ("Sort" ++ c.sortName (valSort k))))
    (hu : ¬ D (.symbol (c.symName k.unit))) (he : ¬ D (.symbol (c.symName k.elem)))
    (hc : ¬ D (.symbol (c.symName k.concat))) : OwnSorted D [] [] .pred (collNoJunk c k) := by
  have key : ∀ el, OwnSorted D [] [⟨1⟩] .ex el → OwnSorted D [] [] .pred
      (KoreAML.inhOf (sortP (c.sortName k.sort)) ⊆⊆
        .mu ⟨1⟩ (symP (c.symName k.unit) ⋁ KoreAML.appList (symP (c.symName k.concat)) [el, .svar ⟨1⟩])) :=
    fun el hel => .included (.inhOf (.sortC hs)) (.toOld (.mu (.disj_ex (.symC hu)
      (.appList (.symC hc) fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hel.toOld
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact .svar (List.mem_cons_self ..)
          · exact absurd ha List.not_mem_nil))))
  have hk1 : OwnSorted D [] [⟨1⟩] .old (KoreAML.inhOf (sortP (c.sortName k.key))) :=
    (OwnSorted.inhOf (.sortC hkey)).toOld
  have hv1 : OwnSorted D [] [⟨1⟩] .old (KoreAML.inhOf (sortP (c.sortName (valSort k)))) :=
    (OwnSorted.inhOf (.sortC hval)).toOld
  have h2 : OwnSorted D [] [⟨1⟩] .ex (KoreAML.appList (symP (c.symName k.elem))
      [KoreAML.inhOf (sortP (c.sortName k.key)), KoreAML.inhOf (sortP (c.sortName (valSort k)))]) :=
    .appE (.appE (.symC he) hk1) hv1
  have h1 : OwnSorted D [] [⟨1⟩] .ex (KoreAML.appList (symP (c.symName k.elem))
      [KoreAML.inhOf (sortP (c.sortName k.key))]) := .appE (.symC he) hk1
  unfold collNoJunk
  refine key _ ?_
  cases k.kind <;> first | exact h2 | exact h1

variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}
  (hD : ∀ σ, D σ → plainSym σ) (hI : DefOK I)
include hD hI

/-- The extension satisfies the no-junk item of a collection outside `D` where the model does. -/
theorem transfer_collNoJunk (k : CollSig)
    (hs : ¬ D (.sort ("Sort" ++ c.sortName k.sort))) (hkey : ¬ D (.sort ("Sort" ++ c.sortName k.key)))
    (hval : ¬ D (.sort ("Sort" ++ c.sortName (valSort k))))
    (hu : ¬ D (.symbol (c.symName k.unit))) (he : ¬ D (.symbol (c.symName k.elem)))
    (hc : ¬ D (.symbol (c.symName k.concat))) (h : I ⊧ᴵ collNoJunk c k) :
    extModel c D I ⊧ᴵ collNoJunk c k :=
  transfer (gs := []) hD hI nil_sub (ownSorted_collNoJunk c k hs hkey hval hu he hc) (.inl rfl) h

/-- **Transfer of the translation of `axiom{R} \equals{S, R}(l, r)`**, for a sort `S` outside `D`
that is a sort in the model, free variables of sorts outside `D`, and sides `l`, `r` whose
translations are of the class. -/
theorem transfer_trAxiom_equals (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) {n : String} {l r : Kore.Pattern}
    {attrs : List Kore.AppPattern} (i : Nat) (md : String)
    (hn : ¬ D (.sort ("Sort" ++ n)))
    (hSs : ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ n)) a ↔ a = σ)
    (hfree : ∀ key ∈ KoreAML.freeOf [] l ++ KoreAML.freeOf [] r,
      ∃ x n', key = .evar x (KoreAML.srt n') ∧ ¬ D (.sort ("Sort" ++ n')))
    (hl : OwnSorted D ((KoreAML.freeOf [] l ++ KoreAML.freeOf [] r).map
        (KoreAML.tableOf [KoreAML.Rv] (.equals (KoreAML.srt n) KoreAML.R l r)).ev) [] .old
      (KoreAML.tr ⟨KoreAML.tableOf [KoreAML.Rv] (.equals (KoreAML.srt n) KoreAML.R l r), []⟩ l))
    (hr : OwnSorted D ((KoreAML.freeOf [] l ++ KoreAML.freeOf [] r).map
        (KoreAML.tableOf [KoreAML.Rv] (.equals (KoreAML.srt n) KoreAML.R l r)).ev) [] .old
      (KoreAML.tr ⟨KoreAML.tableOf [KoreAML.Rv] (.equals (KoreAML.srt n) KoreAML.R l r), []⟩ r))
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, md,
      { sortVars := [KoreAML.Rv], pattern := .equals (KoreAML.srt n) KoreAML.R l r, attributes := attrs }⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, md,
      { sortVars := [KoreAML.Rv], pattern := .equals (KoreAML.srt n) KoreAML.R l r, attributes := attrs }⟩).pat := by
  generalize ht : KoreAML.tableOf [KoreAML.Rv] (.equals (KoreAML.srt n) KoreAML.R l r) = t at hl hr
  generalize hfr : KoreAML.freeOf [] l ++ KoreAML.freeOf [] r = fr at hfree hl hr
  let Rk : KoreAML.VarKey := .sortVar "R"
  let fk : List KoreAML.VarKey := (fr.filter fun b => b != Rk).eraseDups
  let sortOfKey : KoreAML.VarKey → KoreAML.P := fun key => match key with
    | .evar _ s => KoreAML.trSort t s
    | _ => ⊥
  let gs : List (EVar × KoreAML.P) := fk.map fun key => (t.ev key, sortOfKey key)
  have hfk : ∀ key ∈ fk, key ∈ fr ∧ key ≠ Rk := fun key hk => by
    have := List.mem_filter.mp (List.mem_eraseDups.mp hk)
    exact ⟨this.1, by simpa using this.2⟩
  have hfk' : ∀ key ∈ fr, key ∈ fk := fun key hk => by
    obtain ⟨x, n', rfl, _⟩ := hfree key hk
    exact List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hk, by simp [Rk]⟩)
  have hfreeEq : ([KoreAML.Rv].map KoreAML.sortVarKey ++
      KoreAML.freeOf [] (.equals (KoreAML.srt n) KoreAML.R l r)).eraseDups = Rk :: fk := by
    have : KoreAML.freeOf [] (.equals (KoreAML.srt n) KoreAML.R l r) = fr := by rw [KoreAML.freeOf]; exact hfr
    rw [this]
    exact List.eraseDups_cons
  have hgs : fk.map (KoreAML.guardOf t) = memGs gs := by
    simp only [memGs, gs, List.map_map]
    refine List.map_congr_left fun key hk => ?_
    obtain ⟨x, n', rfl, _⟩ := hfree key (hfk key hk).1
    rfl
  have hpat : (KoreAML.trAxiom [] [] ⟨i, md,
      { sortVars := [KoreAML.Rv], pattern := .equals (KoreAML.srt n) KoreAML.R l r, attributes := attrs }⟩).pat =
      KoreAML.guarded (KoreAML.sortGuard (t.ev Rk) :: memGs gs)
        (KoreAML.sEquals (KoreAML.sym (.sort ("Sort" ++ n))) (.evar (t.ev Rk)) (KoreAML.tr ⟨t, []⟩ l)
          (KoreAML.tr ⟨t, []⟩ r) ≡ KoreAML.inhOf (.evar (t.ev Rk))) := by
    unfold KoreAML.trAxiom
    simp only
    rw [ht, hfreeEq, List.map_cons, hgs, KoreAML.tr, trSort_srt]
    rfl
  have ht0 : ∃ rest, t = Rk :: rest := by
    rw [← ht]
    exact ⟨_, List.eraseDups_cons⟩
  have hR : t.ev Rk ∉ gs.map (·.1) := by
    intro hmem
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨rest, hrest⟩ := ht0
    have hne := (hfk key hk).2
    have h1 : t.idxOf key + 1 = t.idxOf Rk + 1 := congrArg EVar.val hpe
    rw [hrest] at h1
    simp [List.idxOf_cons, Ne.symm hne] at h1
  have hsub : ∀ x ∈ fr.map t.ev, x ∈ gs.map (·.1) := fun x hx => by
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨key, hfk' key hk, rfl⟩, rfl⟩
  have hs : ∀ p ∈ gs, OwnSorted D [] [] .ex p.2 := fun p hp => by
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨x, n', rfl, hn'⟩ := hfree key (hfk key hk).1
    show OwnSorted D [] [] .ex (KoreAML.trSort t (KoreAML.srt n'))
    rw [trSort_srt]
    exact .sortC hn'
  obtain ⟨σ, hσ, hSσ⟩ := hSs
  rw [hpat] at h ⊢
  exact transfer_equation hD hI hs hc hR (.sortC hn) ⟨σ, hσ, fun _ a => hSσ a⟩
    (hl.mono hsub fun _ h => h) (hr.mono hsub fun _ h => h) h

/-- **The extension satisfies the idempotence sentence of an open generator** where the model
does: `axiom{R} \equals{S, R}(f(K, K), K)`, for `f` and its result sort `S` outside `D`. -/
theorem transfer_idem (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) (k : ParamSig)
    (hn : ¬ D (.sort ("Sort" ++ c.sortName k.sig.result))) (hf : ¬ D (.symbol (c.symName k.sig.name)))
    (hSs : ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName k.sig.result)) a ↔ a = σ)
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxK c k⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", idemAxK c k⟩).pat := by
  let S := KoreAML.srt (c.sortName k.sig.result)
  have hfr : KoreAML.freeOf [] (KoreAML.ap (c.symName k.sig.name) [KoreAML.ev "K" S, KoreAML.ev "K" S]) ++
      KoreAML.freeOf [] (KoreAML.ev "K" S) = [.evar "K" S, .evar "K" S, .evar "K" S] := rfl
  have hK : ∀ t : KoreAML.VarTable, KoreAML.tr ⟨t, []⟩ (KoreAML.ev "K" S) = .evar (t.ev (.evar "K" S)) :=
    fun t => by unfold KoreAML.ev; rw [KoreAML.tr]; rfl
  refine transfer_trAxiom_equals hD hI hc 0 "kernel" hn hSs ?_ ?_ ?_ h
  · rw [hfr]
    intro key hk
    refine ⟨"K", c.sortName k.sig.result, ?_, hn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hk
    exact hk
  · rw [hfr]
    unfold KoreAML.ap
    rw [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil, hK]
    have hm : (KoreAML.tableOf [KoreAML.Rv] (.equals S KoreAML.R
        (.app ⟨⟨c.symName k.sig.name⟩⟩ [] [KoreAML.ev "K" S, KoreAML.ev "K" S]) (KoreAML.ev "K" S))).ev (.evar "K" S) ∈
        [KoreAML.VarKey.evar "K" S, .evar "K" S, .evar "K" S].map
          (KoreAML.tableOf [KoreAML.Rv] (.equals S KoreAML.R
            (.app ⟨⟨c.symName k.sig.name⟩⟩ [] [KoreAML.ev "K" S, KoreAML.ev "K" S]) (KoreAML.ev "K" S))).ev :=
      List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩
    exact (OwnSorted.appE (.appE (.symC hf) (OwnSorted.toOld (.evar hm))) (OwnSorted.toOld (.evar hm))).toOld
  · rw [hfr, hK]
    exact OwnSorted.toOld (.evar (List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩))

/-- **The extension satisfies the associativity sentence of an open generator** where the model
does: `axiom{R} \equals{S, R}(f(f(K1, K2), K3), f(K1, f(K2, K3)))`, for `f` and its result sort `S`
outside `D`. -/
theorem transfer_assoc (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) (k : ParamSig)
    (hn : ¬ D (.sort ("Sort" ++ c.sortName k.sig.result))) (hf : ¬ D (.symbol (c.symName k.sig.name)))
    (hSs : ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ c.sortName k.sig.result)) a ↔ a = σ)
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", assocAxK c k⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel", assocAxK c k⟩).pat := by
  let S := KoreAML.srt (c.sortName k.sig.result)
  let f := c.symName k.sig.name
  have hfr : KoreAML.freeOf [] (KoreAML.ap f [KoreAML.ap f [KoreAML.ev "K1" S, KoreAML.ev "K2" S], KoreAML.ev "K3" S]) ++
      KoreAML.freeOf [] (KoreAML.ap f [KoreAML.ev "K1" S, KoreAML.ap f [KoreAML.ev "K2" S, KoreAML.ev "K3" S]]) =
      [.evar "K1" S, .evar "K2" S, .evar "K3" S, .evar "K1" S, .evar "K2" S, .evar "K3" S] := rfl
  have hK : ∀ (t : KoreAML.VarTable) (x : String),
      KoreAML.tr ⟨t, []⟩ (KoreAML.ev x S) = .evar (t.ev (.evar x S)) :=
    fun t x => by unfold KoreAML.ev; rw [KoreAML.tr]; rfl
  refine transfer_trAxiom_equals hD hI hc 0 "kernel" hn hSs ?_ ?_ ?_ h
  · rw [hfr]
    intro key hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨_, c.sortName k.sig.result, rfl, hn⟩
  · rw [hfr]
    generalize KoreAML.tableOf _ _ = t
    have h1 : t.ev (.evar "K1" S) ∈ [KoreAML.VarKey.evar "K1" S, .evar "K2" S, .evar "K3" S, .evar "K1" S,
        .evar "K2" S, .evar "K3" S].map t.ev := List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩
    have h2 : t.ev (.evar "K2" S) ∈ [KoreAML.VarKey.evar "K1" S, .evar "K2" S, .evar "K3" S, .evar "K1" S,
        .evar "K2" S, .evar "K3" S].map t.ev :=
      List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
    have h3 : t.ev (.evar "K3" S) ∈ [KoreAML.VarKey.evar "K1" S, .evar "K2" S, .evar "K3" S, .evar "K1" S,
        .evar "K2" S, .evar "K3" S].map t.ev :=
      List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl⟩
    unfold KoreAML.ap
    rw [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil,
      KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil, hK, hK, hK]
    exact (OwnSorted.appE (.appE (.symC hf)
      (OwnSorted.appE (.appE (.symC hf) (OwnSorted.toOld (.evar h1))) (OwnSorted.toOld (.evar h2))).toOld)
      (OwnSorted.toOld (.evar h3))).toOld
  · rw [hfr]
    generalize KoreAML.tableOf _ _ = t
    have h1 : t.ev (.evar "K1" S) ∈ [KoreAML.VarKey.evar "K1" S, .evar "K2" S, .evar "K3" S, .evar "K1" S,
        .evar "K2" S, .evar "K3" S].map t.ev := List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩
    have h2 : t.ev (.evar "K2" S) ∈ [KoreAML.VarKey.evar "K1" S, .evar "K2" S, .evar "K3" S, .evar "K1" S,
        .evar "K2" S, .evar "K3" S].map t.ev :=
      List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
    have h3 : t.ev (.evar "K3" S) ∈ [KoreAML.VarKey.evar "K1" S, .evar "K2" S, .evar "K3" S, .evar "K1" S,
        .evar "K2" S, .evar "K3" S].map t.ev :=
      List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl⟩
    unfold KoreAML.ap
    rw [KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil,
      KoreAML.tr_app0, KoreAML.trArgs_cons, KoreAML.trArgs_cons, KoreAML.trArgs_nil, hK, hK, hK]
    exact (OwnSorted.appE (.appE (.symC hf) (OwnSorted.toOld (.evar h1)))
      (OwnSorted.appE (.appE (.symC hf) (OwnSorted.toOld (.evar h2))) (OwnSorted.toOld (.evar h3))).toOld).toOld

/-- The pattern of the equation of the clause `f(A) = A`, `A` a variable of the sort `s`:
`\implies{R}(\and{R}(\top{R}(), \and{R}(\in{s,R}(X0, A), \top{R}())), \equals{s,R}(f(X0), \and{s}(A, \top{s}())))`. -/
def fnEqIdPat (f s : String) : Kore.Pattern :=
  .implies KoreAML.R
    (.and KoreAML.R [.top KoreAML.R, .and KoreAML.R
      [.in (KoreAML.srt s) KoreAML.R (KoreAML.ev "X0" (KoreAML.srt s)) (KoreAML.ev "VarA" (KoreAML.srt s)), .top KoreAML.R]])
    (.equals (KoreAML.srt s) KoreAML.R (KoreAML.ap f [KoreAML.ev "X0" (KoreAML.srt s)])
      (.and (KoreAML.srt s) [KoreAML.ev "VarA" (KoreAML.srt s), .top (KoreAML.srt s)]))

/-- **The extension satisfies a function equation where the model does**: the equation of the
clause `f(A) = A`, for `f` and the sort `s` outside `D`, in a model in which some sort has an
element. Its sort variable ranges over the detached sort names in the extension. -/
theorem transfer_fnEq (hc : I ⊧ᴵ KoreAML.ceilDefItem.pat) (hne : ∃ τ, IsSort I τ ∧ ∃ m, Inh I τ m)
    (f s : String) (hn : ¬ D (.sort ("Sort" ++ s))) (hf : ¬ D (.symbol f))
    (hSs : ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort ("Sort" ++ s)) a ↔ a = σ)
    (h : I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := fnEqIdPat f s, attributes := [] }⟩).pat) :
    extModel c D I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨0, "kernel",
      { sortVars := [KoreAML.Rv], pattern := fnEqIdPat f s, attributes := [] }⟩).pat := by
  let S := KoreAML.srt s
  have hO : ∀ N, N = "Sort" ++ s → ¬ D (.sort N) ∧ ∃ σ, IsSort I σ ∧ ∀ a, I.evalSymb (.sort N) a ↔ a = σ :=
    fun N hN => hN ▸ ⟨hn, hSs⟩
  have hO' : ∀ N, N = "Sort" ++ s → ¬ D (.sort N) := fun N hN => (hO N hN).1
  have hfr : KoreAML.freeOf [] (fnEqIdPat f s) =
      [.evar "X0" S, .evar "VarA" S, .evar "X0" S, .evar "VarA" S] := rfl
  refine transfer_trAxiom_R hD hI hc hO hne 0 "kernel" rfl ?_ ?_ h
  · rw [hfr]
    intro key hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨"X0", _, rfl, hn⟩
    · exact ⟨"VarA", _, rfl, hn⟩
    · exact ⟨"X0", _, rfl, hn⟩
    · exact ⟨"VarA", _, rfl, hn⟩
  · rw [hfr]
    generalize KoreAML.tableOf [KoreAML.Rv] (fnEqIdPat f s) = t
    have htr : KoreAML.tr ⟨t, []⟩ (fnEqIdPat f s) =
        KoreAML.sImp (.evar (t.ev (.sortVar "R")))
          (KoreAML.sAnd (KoreAML.sTop (.evar (t.ev (.sortVar "R"))))
            (KoreAML.sAnd (KoreAML.sIn (KoreAML.sym (.sort ("Sort" ++ s))) (.evar (t.ev (.sortVar "R")))
              (.evar (t.ev (.evar "X0" S))) (.evar (t.ev (.evar "VarA" S))))
              (KoreAML.sTop (.evar (t.ev (.sortVar "R"))))))
          (KoreAML.sEquals (KoreAML.sym (.sort ("Sort" ++ s))) (.evar (t.ev (.sortVar "R")))
            (KoreAML.sym (.symbol f) ⬝ .evar (t.ev (.evar "X0" S)))
            (KoreAML.sAnd (.evar (t.ev (.evar "VarA" S))) (KoreAML.sTop (KoreAML.sym (.sort ("Sort" ++ s)))))) := rfl
    rw [htr]
    have hmem : ∀ x, x = "X0" ∨ x = "VarA" → (t.ev (.evar x S), "Sort" ++ s) ∈
        ((([KoreAML.VarKey.evar "X0" S, .evar "VarA" S, .evar "X0" S, .evar "VarA" S].filter
          fun b => b != KoreAML.VarKey.sortVar "R").eraseDups).map fun key => (t.ev key, keySortName key)) :=
      fun x hx => List.mem_map.mpr ⟨.evar x S, List.mem_eraseDups.mpr (List.mem_filter.mpr
        ⟨by rcases hx with rfl | rfl <;> simp, by simp⟩), rfl⟩
    have hv : ∀ x, x = "X0" ∨ x = "VarA" → OwnSorted D
        (((([KoreAML.VarKey.evar "X0" S, .evar "VarA" S, .evar "X0" S, .evar "VarA" S].filter
          fun b => b != KoreAML.VarKey.sortVar "R").eraseDups).map fun key => (t.ev key, keySortName key)).map (·.1))
        [] .ex (.evar (t.ev (.evar x S))) :=
      fun x hx => .evar (List.mem_map.mpr ⟨_, hmem x hx, rfl⟩)
    exact .sImp (.and .top (.and (.sIn rfl (hmem "X0" (.inl rfl)) (hv "VarA" (.inr rfl)).toOld) .top))
      (.sEquals hO' rfl (OwnSorted.appE (.symC hf) (hv "X0" (.inl rfl)).toOld).toOld
        (OwnSorted.toOld (.sAnd (hv "VarA" (.inr rfl))
          (OwnSorted.toOld (.sEx (V' := []) (.sortC hn) nil_sub (.inl rfl) (.evar (List.mem_cons_self ..)))))))

end

end KCore.Cons
