/-
  The constructor sentences of a text against Γ's constructor items, for any text: the
  `functional` sentence of a constructor and the `subsort` sentence of an injection from the
  generator's Cons-Fun item, the no-confusion sentence of one generator from its Cons-Fun and
  Cons-Inj items, the no-confusion sentence of two generators from their Cons-Fun items and their
  Cons-Dist item. Each lemma takes the sentence's shape as hypotheses that are decided on the text;
  `tieConsB` decides them, and finds the sort and the generators, for a semantics and an axiom.
-/
import KcoreSpec.TieLemmas

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace Faithful

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

omit [Inhabited M] in
/-- A translated axiom is satisfied where, at every valuation that meets its guards, the
translation of its pattern is the whole of its sort (the converse of `trAxiom_at`). -/
theorem tieAxiom_intro (hD : KoreAML.DefOK I) {i : Nat} {mod : String} {a : Kore.Axiom}
    (h : ∀ e : Valuation M,
      (∀ k ∈ (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups, ∀ m,
        (KoreAML.guardOf (KoreAML.tableOf a.sortVars a.pattern) k).interpret I e m) →
      ∀ x, (KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ a.pattern).interpret I e x ↔
        (match KoreAML.sortOf [] a.pattern with
          | some s => KoreAML.inhOf (KoreAML.trSort (KoreAML.tableOf a.sortVars a.pattern) s)
          | none => KoreAML.sym (.untranslated "sort of the axiom")).interpret I e x) :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  intro e m
  unfold KoreAML.trAxiom
  dsimp only
  rw [interpret_impl]
  intro hg
  rw [KoreAML.interp_equal hD]
  refine h e fun k hk m' => ?_
  have := conjList_mem hg _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  cases k with
  | sortVar n => exact (KoreAML.interp_guard_sortVar hD).mpr ((KoreAML.interp_guard_sortVar hD).mp this)
  | evar n s => exact (KoreAML.interp_guard_evar hD).mpr ((KoreAML.interp_guard_evar hD).mp this)
  | svar n s =>
    unfold KoreAML.guardOf at this ⊢
    exact (KoreAML.interp_included hD).mpr ((KoreAML.interp_included hD).mp this)

/-- The elements the valuation gives the variables `ks`, whose guards hold, are in their sorts. -/
theorem tieArgs_inS (hD : KoreAML.DefOK I) {t : KoreAML.VarTable} {e : Valuation M} {free : List KoreAML.VarKey}
    (hg : ∀ k ∈ free, ∀ m, (KoreAML.guardOf t k).interpret I e m) :
    ∀ {ks : List Kore.EVar} {ss : List String}, (∀ k ∈ ks, KoreAML.evarKey k ∈ free) →
      ks.map (·.sort) = ss.map KoreAML.srt →
      ∀ (i : Nat) x s, ((ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar)[i]? = some x → ss[i]? = some s → InS I s x
  | [], _, _, _, i, x, s, hx, _ => by simp at hx
  | _ :: _, [], _, hs, _, _, _, _, _ => by simp at hs
  | k :: ks, s' :: ss, hk, hs, i, x, s, hx, hsi => by
    simp only [List.map_cons, List.cons.injEq] at hs
    cases i with
    | zero =>
      simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hx hsi
      subst hx; subst hsi
      have h1 := hg _ (hk k (List.mem_cons_self ..)) default
      have h2 : (KoreAML.guardOf t (.evar k.var.ident.name k.sort)).interpret I e default := h1
      rw [KoreAML.interp_guard_evar hD, hs.1, trSort_srt] at h2
      have hkey : KoreAML.evarKey k = .evar k.var.ident.name (KoreAML.srt s') := by rw [← hs.1]; rfl
      rw [hkey]
      exact (inS_iff _).mp h2
    | succ i =>
      simp only [List.map_cons, List.getElem?_cons_succ] at hx hsi
      exact tieArgs_inS hD hg (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk')) hs.2 i x s hx hsi

/-- The generator applied to variables, at a valuation: the generator's set at their elements. -/
theorem tieGen_vars (N : String) (g : KoreAML.Gen) (e : Valuation M) (vs : List EVar) (m : M) :
    (KoreAML.Cons.genPat N g (vs.map .evar)).interpret I e m ↔ GS I N g (vs.map e.evalEvar) m :=
  interp_genPat_vars N g e vs m

section Fun
variable {c : Semantics} [OvlOK c]

/-- **The `functional` sentence of a generator** (a constructor's, or a `subsort` sentence for an
injection), `axiom{R} \exists{R}(Val:N, \equals{N, R}(Val:N, g(K̄)))`, is satisfied in a model of
Γ that satisfies the generator's Cons-Fun item. The hypotheses on the sentence are decided on its
text: its shape, its free variables (R, then the generator's arguments), the sorts, the translation
of the right side as the generator applied to the argument variables, and that the bound variable's
index is none of theirs. -/
theorem tieFun_entailed (hI : I ⊧ᴵP Γ c) {N : Srt} (hN : N < nRegSorts + c.sortNames.length) {g : KoreAML.Gen}
    (hitem : I ⊧ᴵ (KoreAML.Cons.funItem (c.sortName N) g).pat)
    {i : Nat} {mod : String} {a : Kore.Axiom} {val : Kore.EVar} {ks : List Kore.EVar} {body : Kore.Pattern}
    (hpat : a.pattern = .exist KoreAML.R val (.equals (KoreAML.srt (c.sortName N)) KoreAML.R (.var (.evar val)) body))
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey)
    (hval : val.sort = KoreAML.srt (c.sortName N))
    (hks : ks.map (·.sort) = g.argSorts.map KoreAML.srt)
    (hbody : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ body =
      KoreAML.Cons.genPat (c.sortName N) g
        ((ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hfresh : (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey val) ∉
      (KoreAML.tableOf a.sortVars a.pattern).ev (.sortVar "R") ::
        ks.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)) :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  obtain ⟨σN, hσN1, hσN2⟩ := sortSing hI hN
  refine tieAxiom_intro hD fun e hg x => ?_
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hg hbody hfresh ⊢
  rw [hfree] at hg
  have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
    (KoreAML.interp_guard_sortVar hD).mp (hg _ (List.mem_cons_self ..) default)
  have hargs := tieArgs_inS hD (fun k hk m => hg k (List.mem_cons_of_mem _ hk) m)
    (ks := ks) (ss := g.argSorts) (fun k hk => List.mem_map.mpr ⟨k, hk, rfl⟩) hks
  have hl : ((ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar).length = g.argSorts.length := by
    have := congrArg List.length hks
    simpa using this
  obtain ⟨y, hyN, hy⟩ := fun_at hD hitem hl hargs
  rw [hpat]
  show (KoreAML.tr ⟨t, []⟩ (.exist KoreAML.R val (.equals (KoreAML.srt (c.sortName N)) KoreAML.R (.var (.evar val)) body))).interpret I e x ↔
    (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e x
  have hRv : ∀ (e' : Valuation M) b, (KoreAML.trSort t KoreAML.R).interpret I e' b ↔ b = e'.evalEvar (t.ev (.sortVar "R")) :=
    fun e' b => by rw [trSort_R, KoreAML.interp_evar]
  have hS : ∀ (e' : Valuation M) b, (KoreAML.trSort t (KoreAML.srt (c.sortName N))).interpret I e' b ↔ b = σN :=
    fun e' b => by rw [trSort_srt]; exact hσN1 b
  rw [KoreAML.tr, KoreAML.interp_sExists, KoreAML.interp_inhOf_of (hRv e)]
  have hne : t.ev (.sortVar "R") ≠ t.ev (KoreAML.evarKey val) := fun h => hfresh (h ▸ List.mem_cons_self ..)
  have hupd : ∀ v : M, (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ : Valuation M).evalEvar
      (t.ev (.sortVar "R")) = e.evalEvar (t.ev (.sortVar "R")) := fun v => Function.update_noteq hne _ _
  have hmap : ∀ v : M, (ks.map fun k => t.ev (KoreAML.evarKey k)).map
      (⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ : Valuation M).evalEvar =
      (ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar := fun v =>
    List.map_congr_left fun z hz => Function.update_noteq (fun (h : z = t.ev (KoreAML.evarKey val)) => hfresh (List.mem_cons_of_mem _ (h ▸ hz))) _ _
  have hbodyI : ∀ (v b : M), (KoreAML.tr ⟨t, []⟩ body).interpret I
      ⟨Function.update e.evalEvar (t.ev (KoreAML.evarKey val)) v, e.evalSvar⟩ b ↔ b = y := fun v b => by
    rw [hbody, tieGen_vars, hmap]; exact hy b
  constructor
  · rintro ⟨v, -, h2⟩
    rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hS _) (hRv _) hσN2 (by rw [hupd]; exact hR)] at h2
    rw [← hupd v]; exact h2.1
  · intro hx
    refine ⟨y, ?_, ?_⟩
    · rw [KoreAML.interp_member hD]
      simp only [Function.update_same]
      rw [hval, trSort_srt]
      exact (inS_iff _).mpr hyN
    · rw [KoreAML.tr, KoreAML.interp_sEquals hD hc (hS _) (hRv _) hσN2 (by rw [hupd]; exact hR)]
      refine ⟨by rw [hupd]; exact hx, fun b _ => ?_⟩
      rw [hbodyI, KoreAML.tr, KoreAML.interp_evar]
      simp only [Function.update_same]

end Fun

omit [Inhabited M] in
/-- Conjunctions `x ∧ y` of variables that hold the same elements denote those elements. -/
theorem tieAnd_sing {e : Valuation M} : ∀ (ix iy : List EVar), ix.map e.evalEvar = iy.map e.evalEvar →
    All2 (fun (φ : KoreAML.P) x => ∀ m, φ.interpret I e m ↔ m = x)
      ((ix.zip iy).map fun p => KoreAML.sAnd (.evar p.1) (.evar p.2)) (ix.map e.evalEvar)
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: ix, y :: iy, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    refine .cons (fun m => ?_) (tieAnd_sing ix iy h.2)
    rw [KoreAML.interp_sAnd, KoreAML.interp_evar, KoreAML.interp_evar, ← h.1]
    exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

section Inj
variable {c : Semantics}

/-- **The no-confusion sentence of one generator**, `\implies{N}(\and{N}(g(X̄), g(Ȳ)), g(X̄ ∧ Ȳ))`,
is satisfied in a model of definedness that satisfies the generator's Cons-Fun and Cons-Inj items:
an element both applications hold is the one element of each, so the arguments are equal, and the
application to the conjunctions is the application to them. The hypotheses on the sentence are
decided on its text. -/
theorem tieInj_entailed (hD : KoreAML.DefOK I) {N : String} {g : KoreAML.Gen}
    (hfun : I ⊧ᴵ (KoreAML.Cons.funItem N g).pat) (hinj : I ⊧ᴵ (KoreAML.Cons.injItem N g).pat)
    {i : Nat} {mod : String} {a : Kore.Axiom} {xs ys : List Kore.EVar} {p1 p2 q : Kore.Pattern}
    (hpat : a.pattern = .implies (KoreAML.srt N) (.and (KoreAML.srt N) [p1, p2]) q)
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey)
    (hxs : xs.map (·.sort) = g.argSorts.map KoreAML.srt) (hys : ys.map (·.sort) = g.argSorts.map KoreAML.srt)
    (hp1 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p1 = KoreAML.Cons.genPat N g
      ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hp2 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p2 = KoreAML.Cons.genPat N g
      ((ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hq : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ q = KoreAML.Cons.genPat N g
      (((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).zip
        (ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k))).map
          fun p => KoreAML.sAnd (.evar p.1) (.evar p.2))) :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  refine tieAxiom_intro hD fun e hg x => ?_
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hg hp1 hp2 hq ⊢
  rw [hfree] at hg
  have hX := tieArgs_inS hD hg (ks := xs) (ss := g.argSorts)
    (fun k hk => List.mem_map.mpr ⟨k, List.mem_append_left _ hk, rfl⟩) hxs
  have hY := tieArgs_inS hD hg (ks := ys) (ss := g.argSorts)
    (fun k hk => List.mem_map.mpr ⟨k, List.mem_append_right _ hk, rfl⟩) hys
  have hlX : ((xs.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar).length = g.argSorts.length := by
    have := congrArg List.length hxs
    simpa using this
  have hlY : ((ys.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar).length = g.argSorts.length := by
    have := congrArg List.length hys
    simpa using this
  obtain ⟨y1, -, hy1⟩ := fun_at hD hfun hlX hX
  obtain ⟨y2, -, hy2⟩ := fun_at hD hfun hlY hY
  rw [hpat]
  show (KoreAML.sImp (KoreAML.trSort t (KoreAML.srt N))
      (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2)) (KoreAML.tr ⟨t, []⟩ q)).interpret I e x ↔
    (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N))).interpret I e x
  rw [KoreAML.interp_sImp, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars]
  refine ⟨fun h => h.1, fun hx => ⟨hx, fun ⟨h1, h2⟩ => ?_⟩⟩
  have e1 : x = y1 := (hy1 x).mp h1
  have e2 : x = y2 := (hy2 x).mp h2
  have heq := inj_at hD hinj hlX hlY hX hY (fun m => by rw [hy1, hy2, ← e1, ← e2])
  rw [hq, genPat_eq, interp_appList_sing _ _ _ (tieAnd_sing _ _ heq)]
  obtain ⟨a0, ha0, happ⟩ := h1
  exact ⟨a0, (genHead_val0 N g e a0).mpr ha0, happ⟩

/-- **The no-confusion sentence of two generators**, `\not{N}(\and{N}(g(X̄), g'(Ȳ)))`, is satisfied
in a model of definedness that satisfies the two generators' Cons-Fun items and their Cons-Dist
item, in either order. The hypotheses on the sentence are decided on its text. -/
theorem tieDist_entailed (hD : KoreAML.DefOK I) {N : String} {g g' : KoreAML.Gen}
    (hfun : I ⊧ᴵ (KoreAML.Cons.funItem N g).pat) (hfun' : I ⊧ᴵ (KoreAML.Cons.funItem N g').pat)
    (hdist : (I ⊧ᴵ (KoreAML.Cons.distItem N g g').pat) ∨ (I ⊧ᴵ (KoreAML.Cons.distItem N g' g).pat))
    {i : Nat} {mod : String} {a : Kore.Axiom} {xs ys : List Kore.EVar} {p1 p2 : Kore.Pattern}
    (hpat : a.pattern = .not (KoreAML.srt N) (.and (KoreAML.srt N) [p1, p2]))
    (hfree : (a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey)
    (hxs : xs.map (·.sort) = g.argSorts.map KoreAML.srt) (hys : ys.map (·.sort) = g'.argSorts.map KoreAML.srt)
    (hp1 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p1 = KoreAML.Cons.genPat N g
      ((xs.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar))
    (hp2 : KoreAML.tr ⟨KoreAML.tableOf a.sortVars a.pattern, []⟩ p2 = KoreAML.Cons.genPat N g'
      ((ys.map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).map .evar)) :
    I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  refine tieAxiom_intro hD fun e hg x => ?_
  generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hg hp1 hp2 ⊢
  rw [hfree] at hg
  have hX := tieArgs_inS hD hg (ks := xs) (ss := g.argSorts)
    (fun k hk => List.mem_map.mpr ⟨k, List.mem_append_left _ hk, rfl⟩) hxs
  have hY := tieArgs_inS hD hg (ks := ys) (ss := g'.argSorts)
    (fun k hk => List.mem_map.mpr ⟨k, List.mem_append_right _ hk, rfl⟩) hys
  have hlX : ((xs.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar).length = g.argSorts.length := by
    have := congrArg List.length hxs
    simpa using this
  have hlY : ((ys.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar).length = g'.argSorts.length := by
    have := congrArg List.length hys
    simpa using this
  obtain ⟨y1, -, hy1⟩ := fun_at hD hfun hlX hX
  obtain ⟨y2, -, hy2⟩ := fun_at hD hfun' hlY hY
  rw [hpat]
  show (KoreAML.sNot (KoreAML.trSort t (KoreAML.srt N))
      (KoreAML.sAnd (KoreAML.tr ⟨t, []⟩ p1) (KoreAML.tr ⟨t, []⟩ p2))).interpret I e x ↔
    (KoreAML.inhOf (KoreAML.trSort t (KoreAML.srt N))).interpret I e x
  rw [KoreAML.interp_sNot, KoreAML.interp_sAnd, hp1, hp2, tieGen_vars, tieGen_vars]
  refine ⟨fun h => h.2, fun hx => ⟨fun ⟨h1, h2⟩ => ?_, hx⟩⟩
  have e1 : x = y1 := (hy1 x).mp h1
  have e2 : x = y2 := (hy2 x).mp h2
  rcases hdist with hd | hd
  · exact dist_at hD hd hlX hlY hX hY (fun m => by rw [hy1, hy2, ← e1, ← e2])
  · exact dist_at hD hd hlY hlX hY hX (fun m => by rw [hy1, hy2, ← e1, ← e2])

end Inj

/-! ## The constructor sentences, decided on a text -/

/-- The element variables among keys, as KORE variables. -/
def tieKeyVars (ks : List KoreAML.VarKey) : List Kore.EVar :=
  ks.filterMap fun
    | .evar n s => some (KoreAML.evar n s)
    | _ => none

/-- The axiom `a` is the `functional` sentence of the generator `g` of the sort N, in the form
`tieFun_entailed` reads, and Γ holds the generator's Cons-Fun item. -/
def tieFunB (c : Semantics) (N : Srt) (g : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .exist r val (.equals s r' (.var (.evar val')) body) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let ks := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    decide (s = KoreAML.srt (c.sortName N)) && decide (r = KoreAML.R) && decide (r' = KoreAML.R) &&
    decide (val' = val) && decide (N < nRegSorts + c.sortNames.length) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey) &&
    decide (val.sort = KoreAML.srt (c.sortName N)) && decide (ks.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ body =
      KoreAML.Cons.genPat (c.sortName N) g ((ks.map fun k => t.ev (KoreAML.evarKey k)).map .evar)) &&
    decide (t.ev (KoreAML.evarKey val) ∉ t.ev (.sortVar "R") :: ks.map fun k => t.ev (KoreAML.evarKey k)) &&
    (consItemsK c).any (fun it => decide (it.pat = (KoreAML.Cons.funItem (c.sortName N) g).pat))
  | _ => false

/-- The axiom `a` is the no-confusion sentence of the generator `g` of the sort N, in the form
`tieInj_entailed` reads, and Γ holds the generator's Cons-Fun and Cons-Inj items. -/
def tieInjB (c : Semantics) (N : Srt) (g : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .implies s (.and s' [p1, p2]) q =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName N)) && decide (s' = KoreAML.srt (c.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c.sortName N) g (iy.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ q = KoreAML.Cons.genPat (c.sortName N) g
      ((ix.zip iy).map fun p => KoreAML.sAnd (.evar p.1) (.evar p.2))) &&
    (consItemsK c).any (fun it => decide (it.pat = (KoreAML.Cons.funItem (c.sortName N) g).pat)) &&
    (consItemsK c).any (fun it => decide (it.pat = (KoreAML.Cons.injItem (c.sortName N) g).pat))
  | _ => false

/-- The axiom `a` is the no-confusion sentence of the generators `g` and `g'` of the sort N, in the
form `tieDist_entailed` reads, and Γ holds their Cons-Fun items and their Cons-Dist item in one of
the two orders. -/
def tieDistB (c : Semantics) (N : Srt) (g g' : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .not s (.and s' [p1, p2]) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName N)) && decide (s' = KoreAML.srt (c.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g'.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c.sortName N) g' (iy.map .evar)) &&
    (consItemsK c).any (fun it => decide (it.pat = (KoreAML.Cons.funItem (c.sortName N) g).pat)) &&
    (consItemsK c).any (fun it => decide (it.pat = (KoreAML.Cons.funItem (c.sortName N) g').pat)) &&
    ((consItemsK c).any (fun it => decide (it.pat = (KoreAML.Cons.distItem (c.sortName N) g g').pat)) ||
      (consItemsK c).any (fun it => decide (it.pat = (KoreAML.Cons.distItem (c.sortName N) g' g).pat)))
  | _ => false

/-- **The axiom is a constructor sentence Γ's constructor items entail**: for a constructor sort N
of the semantics and generators of N, it is the `functional` (or `subsort`) sentence of one, the
no-confusion sentence of one, or the no-confusion sentence of two. -/
def tieConsB (c : Semantics) (a : Kore.Axiom) : Bool :=
  (consSorts c).any fun N =>
    let gs := (c.gens N).map (Gen.toK c)
    gs.any (fun g => tieFunB c N g a || tieInjB c N g a || gs.any fun g' => tieDistB c N g g' a)

omit [Inhabited M] in
theorem tieItem_sat {c : Semantics} (hI : I ⊧ᴵP Γ c) {φ : KoreAML.P}
    (h : (consItemsK c).any (fun it => decide (it.pat = φ)) = true) : I ⊧ᴵ φ := by
  obtain ⟨it, hit, he⟩ := List.any_eq_true.mp h
  exact sat_cons hI (Or.inl ⟨it, hit, of_decide_eq_true he⟩)

/-- **A constructor sentence `tieConsB` accepts is entailed by Γ.** -/
theorem tieCons_entailed {c : Semantics} [OvlOK c] {a : Kore.Axiom} (h : tieConsB c a = true) (i : Nat) (mod : String) :
    Γ c ⊧ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  intro M _ I hI
  have hD := defOK hI
  simp only [tieConsB, List.any_eq_true, Bool.or_eq_true] at h
  obtain ⟨N, -, g, -, h⟩ := h
  rcases h with (h | h) | ⟨g', -, h⟩
  · unfold tieFunB at h
    split at h
    · rename_i r val s r' val' body hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
      subst h1 h2 h3 h4
      exact tieFun_entailed hI h5 (tieItem_sat hI h11) hp h6 h7 h8 h9 h10
    · cases h
  · unfold tieInjB at h
    split at h
    · rename_i s s' p1 p2 q hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
      subst h1 h2
      exact tieInj_entailed hD (tieItem_sat hI h9) (tieItem_sat hI h10) hp h3 h4 h5 h6 h7 h8
    · cases h
  · unfold tieDistB at h
    split at h
    · rename_i s s' p1 p2 hp
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
      subst h1 h2
      exact tieDist_entailed hD (tieItem_sat hI h8) (tieItem_sat hI h9)
        (h10.elim (fun h => .inl (tieItem_sat hI h)) fun h => .inr (tieItem_sat hI h)) hp h3 h4 h5 h6 h7
    · cases h

end
end Faithful

kernel_rfl Faithful.tieConsB_withHooks : ∀ (c : Semantics) (H : HookParams) (a : Kore.Axiom),
  Faithful.tieConsB (c.withHooks H) a = Faithful.tieConsB c a

end KCore
