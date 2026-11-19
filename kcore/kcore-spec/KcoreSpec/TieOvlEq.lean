/-
  KCore, outside the cone: the two sentences a text states of an overloading symbol `f` and a
  symbol `g` it overloads, against Γ, for any text.

  - The overload axiom `\equals{N, R}(f(lift K̄), lift(g(K̄)))`, each `lift` the injection between
    the two sorts where they differ. Γ holds the overload equation `KoreAML.Cons.ovlEqItem f g`: for
    elements x̄ of g's argument sorts, f applied to their lifts denotes what g applied to them
    denotes, lifted to f's result sort. At a valuation that meets the sentence's guards, its
    variables K̄ take such elements, and the two sides of the sentence denote what the item's two
    sides denote at x̄ = K̄; so the sentence's equality holds as the whole of R, and every model of Γ
    satisfies it (`tieOvlEq_entailed`; `tieOvlEqB` decides its hypotheses on the text).
  - The no-confusion sentence of two generators, `\not{N}(\and{N}(g₁(X̄), g₂(Ȳ)))`. Where values
    w̄₁, w̄₂ of the two generators' argument sorts have one normal form under the two symbols
    (`Semantics.norm`), every model of Γ builds that normal form's element from the values' elements
    by both generators (`Faithful.norm_gs`); at the valuation sending X̄ and Ȳ to those elements the
    sentence's conjunction holds of it, so no model of Γ satisfies the sentence
    (`tieOvlNc_refuted`). `tieOvlNcB` decides the hypotheses, with the values `exhibit?` gives of
    the overloaded symbol's argument sorts and their lifts to the overloading symbol's.
-/
import KcoreSpec.TieOvlConf
import KcoreSpec.Exhibit
import KcoreSpec.TieDefs

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace Faithful

/-! ## The two sides of an overload equation, at any variables -/

/-- `φ` itself where the sorts named `A` and `B` are named alike, `inj{A,B}(φ)` otherwise. -/
def tieOvlLift (A B : String) (φ : KoreAML.P) : KoreAML.P :=
  if A == B then φ else KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP B, φ]

/-- An argument of the overloading symbol: the variable lifted from the overloaded symbol's
argument sort to the overloading symbol's. -/
def tieOvlArg (p : (String × String) × EVar) : KoreAML.P := tieOvlLift p.1.1 p.1.2 (.evar p.2)

/-- The left side of the overload equation of `F` over `G` at the variables `vs`: `F(lift vs)`. -/
def tieOvlLhs (F G : KoreAML.CtorSig) (vs : List EVar) : KoreAML.P :=
  KoreAML.appList (KoreAML.sym (.symbol F.name)) (((G.args.zip F.args).zip vs).map tieOvlArg)

/-- The right side of the overload equation of `F` over `G` at the variables `vs`: `lift(G(vs))`. -/
def tieOvlRhs (F G : KoreAML.CtorSig) (vs : List EVar) : KoreAML.P :=
  tieOvlLift G.result F.result (KoreAML.appList (KoreAML.sym (.symbol G.name)) (vs.map .evar))

/-- Γ's overload equation is the equality of the two sides at its variables, under their guards. -/
theorem ovlEqItem_tieOvl (F G : KoreAML.CtorSig) : (KoreAML.Cons.ovlEqItem F G).pat =
    KoreAML.guarded (KoreAML.Cons.memGuards (KoreAML.Cons.xs 0 G.args.length) G.args)
      (tieOvlLhs F G (KoreAML.Cons.xs 0 G.args.length) ≡ tieOvlRhs F G (KoreAML.Cons.xs 0 G.args.length)) := rfl

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- Heads and arguments that denote alike under two valuations give applications that do. -/
theorem tieOvl_appList_congr {e e' : Valuation M} {φs ψs : List KoreAML.P}
    (hr : All2 (fun (φ ψ : KoreAML.P) => ∀ m, φ.interpret I e m ↔ ψ.interpret I e' m) φs ψs) :
    ∀ {h h' : KoreAML.P}, (∀ m, h.interpret I e m ↔ h'.interpret I e' m) →
      ∀ m, (KoreAML.appList h φs).interpret I e m ↔ (KoreAML.appList h' ψs).interpret I e' m := by
  induction hr with
  | nil => intro h h' hh m; exact hh m
  | cons hφ _ ih =>
    intro h h' hh m
    exact ih (fun m => by
      rw [KoreAML.interp_app, KoreAML.interp_app]
      exact ⟨fun ⟨a, b, ha, hb, hab⟩ => ⟨a, b, (hh a).mp ha, (hφ b).mp hb, hab⟩,
        fun ⟨a, b, ha, hb, hab⟩ => ⟨a, b, (hh a).mpr ha, (hφ b).mpr hb, hab⟩⟩) m

theorem tieOvl_sym_congr (e e' : Valuation M) (σ : KoreAML.Sym) (m : M) :
    (KoreAML.sym σ).interpret I e m ↔ (KoreAML.sym σ).interpret I e' m :=
  (KoreAML.Closed.sym σ).interp e e' m

theorem tieOvlLift_congr {e e' : Valuation M} (A B : String) {φ ψ : KoreAML.P}
    (h : ∀ m, φ.interpret I e m ↔ ψ.interpret I e' m) (m : M) :
    (tieOvlLift A B φ).interpret I e m ↔ (tieOvlLift A B ψ).interpret I e' m := by
  unfold tieOvlLift
  split
  · exact h m
  · exact tieOvl_appList_congr (.cons (tieOvl_sym_congr e e' _) (.cons (tieOvl_sym_congr e e' _) (.cons h .nil)))
      (tieOvl_sym_congr e e' _) m

theorem tieOvl_evars_congr {e e' : Valuation M} : ∀ {vs ws : List EVar}, vs.map e.evalEvar = ws.map e'.evalEvar →
    All2 (fun (φ ψ : KoreAML.P) => ∀ m, φ.interpret I e m ↔ ψ.interpret I e' m)
      (vs.map .evar) (ws.map .evar)
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | v :: vs, w :: ws, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons (fun m => by rw [KoreAML.interp_evar, KoreAML.interp_evar, h.1]) (tieOvl_evars_congr h.2)

theorem tieOvl_args_congr {e e' : Valuation M} : ∀ (ps : List (String × String)) {vs ws : List EVar},
    vs.map e.evalEvar = ws.map e'.evalEvar →
    All2 (fun (φ ψ : KoreAML.P) => ∀ m, φ.interpret I e m ↔ ψ.interpret I e' m)
      ((ps.zip vs).map tieOvlArg) ((ps.zip ws).map tieOvlArg)
  | [], _, _, _ => by simp only [List.zip_nil_left, List.map_nil]; exact .nil
  | _ :: _, [], [], _ => by simp only [List.zip_nil_right, List.map_nil]; exact .nil
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h
  | p :: ps, v :: vs, w :: ws, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.map_cons]
    exact .cons (tieOvlLift_congr p.1 p.2 (fun m => by rw [KoreAML.interp_evar, KoreAML.interp_evar, h.1]))
      (tieOvl_args_congr ps h.2)

/-- The two sides at variables holding, under two valuations, the same elements denote alike. -/
theorem tieOvlLhs_congr {e e' : Valuation M} (F G : KoreAML.CtorSig) {vs ws : List EVar}
    (h : vs.map e.evalEvar = ws.map e'.evalEvar) (m : M) :
    (tieOvlLhs F G vs).interpret I e m ↔ (tieOvlLhs F G ws).interpret I e' m :=
  tieOvl_appList_congr (tieOvl_args_congr (G.args.zip F.args) h) (tieOvl_sym_congr e e' _) m

theorem tieOvlRhs_congr {e e' : Valuation M} (F G : KoreAML.CtorSig) {vs ws : List EVar}
    (h : vs.map e.evalEvar = ws.map e'.evalEvar) (m : M) :
    (tieOvlRhs F G vs).interpret I e m ↔ (tieOvlRhs F G ws).interpret I e' m :=
  tieOvlLift_congr _ _ (tieOvl_appList_congr (tieOvl_evars_congr h) (tieOvl_sym_congr e e' _)) m

end

/-! ## The overload axiom -/

/-- The axiom `a` is the overload axiom of the overloading symbol `o` over `kg`, in the form
`tieOvlEq_entailed` reads: `\equals{N, R}(lhs, rhs)` with N the result sort of `o`, its free
variables R and then K̄ of `kg`'s argument sorts, `lhs` translated to `o`'s symbol applied to the
lifts of K̄ and `rhs` to the lift of `kg`'s symbol applied to K̄. -/
def tieOvlEqAtB (c : Semantics) (o : OvlSig) (kg : CtorSig) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .equals s r lhs rhs =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let ks := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let ix := ks.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName o.sig.result)) && decide (r = KoreAML.R) &&
    decide (o.sig.result < nRegSorts + c.sortNames.length) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey) &&
    decide (ks.map (·.sort) = (toK c kg).args.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ lhs = tieOvlLhs (toK c o.sig) (toK c kg) ix) &&
    decide (KoreAML.tr ⟨t, []⟩ rhs = tieOvlRhs (toK c o.sig) (toK c kg) ix)
  | _ => false

/-- **The axiom is an overload axiom of the semantics**: of an overloading symbol over one of the
symbols it overloads (`Semantics.ovlOver`), whose overload equation Γ holds. -/
def tieOvlEqB (c : Semantics) (a : Kore.Axiom) : Bool :=
  c.ovls.any fun o => (c.ovlOver o).any fun kg => tieOvlEqAtB c o kg a

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **An overload axiom `tieOvlEqB` accepts is entailed by Γ.** -/
theorem tieOvlEq_entailed {c : Semantics} [OvlOK c] {a : Kore.Axiom} (h : tieOvlEqB c a = true) (i : Nat)
    (mod : String) : Γ c ⊧ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  intro M _ I hI
  have hD := defOK hI
  have hc := sat_sigItem hI (sig_ceilDef (c := c))
  simp only [tieOvlEqB, List.any_eq_true] at h
  obtain ⟨o, ho, kg, hkg, h⟩ := h
  have hitem : I ⊧ᴵ (KoreAML.Cons.ovlEqItem (toK c o.sig) (toK c kg)).pat :=
    sat_cons hI (Or.inl ⟨_, ovlEqItem_mem ho hkg, rfl⟩)
  unfold tieOvlEqAtB at h
  split at h
  · rename_i s r lhs rhs hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hN⟩, hfree⟩, hks⟩, hl⟩, hr⟩ := h
    subst h1 h2
    obtain ⟨σN, hσN1, hσN2⟩ := sortSing hI hN
    refine tieAxiom_intro hD fun e hg x => ?_
    generalize ht : KoreAML.tableOf a.sortVars a.pattern = t at hg hl hr ⊢
    generalize hks' : tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups = ks at hfree hks hl hr
    rw [hfree] at hg
    have hR : KoreAML.IsSort I (e.evalEvar (t.ev (.sortVar "R"))) :=
      (KoreAML.interp_guard_sortVar hD).mp (hg _ (List.mem_cons_self ..) default)
    have hargs := tieArgs_inS hD (fun k hk m => hg k (List.mem_cons_of_mem _ hk) m)
      (ks := ks) (ss := (toK c kg).args) (fun k hk => List.mem_map.mpr ⟨k, hk, rfl⟩) hks
    rw [hp]
    show (KoreAML.sEquals (KoreAML.trSort t (KoreAML.srt (c.sortName o.sig.result))) (KoreAML.trSort t KoreAML.R)
        (KoreAML.tr ⟨t, []⟩ lhs) (KoreAML.tr ⟨t, []⟩ rhs)).interpret I e x ↔
      (KoreAML.inhOf (KoreAML.trSort t KoreAML.R)).interpret I e x
    have hRv : ∀ b, (KoreAML.trSort t KoreAML.R).interpret I e b ↔ b = e.evalEvar (t.ev (.sortVar "R")) :=
      fun b => by rw [trSort_R, KoreAML.interp_evar]
    have hS : ∀ b, (KoreAML.trSort t (KoreAML.srt (c.sortName o.sig.result))).interpret I e b ↔ b = σN :=
      fun b => by rw [trSort_srt]; exact hσN1 b
    rw [KoreAML.interp_sEquals hD hc hS hRv hσN2 hR, KoreAML.interp_inhOf_of hRv]
    refine ⟨fun h => h.1, fun hx => ⟨hx, fun b _ => ?_⟩⟩
    rw [hl, hr]
    -- the item at the elements the sentence's variables take
    generalize hzs : (ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar = zs at hargs
    have hlen : zs.length = (toK c kg).args.length := by
      rw [← hzs]; have := congrArg List.length hks; simpa using this
    have h1 := hitem (listVal zs) default
    rw [ovlEqItem_tieOvl] at h1
    have hb := KoreAML.interp_guarded h1 (fun w hw => memGuards_hold hD _ _ (xs_length 0 _)
      (fun j v s hv hs => by
        obtain ⟨hj, _⟩ := xs_get hv
        rw [listVal_get zs hv, Nat.zero_add, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [hlen]; exact hj)]
        exact hargs j _ s (List.getElem?_eq_getElem _) hs) w hw default)
    rw [KoreAML.interp_equal hD] at hb
    have hxs : (KoreAML.Cons.xs 0 (toK c kg).args.length).map (listVal zs).evalEvar = zs := by
      have := (listVal_split zs [] _ 0 hlen rfl).1
      rwa [List.append_nil] at this
    have hmap : (ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar =
        (KoreAML.Cons.xs 0 (toK c kg).args.length).map (listVal zs).evalEvar := by rw [hzs, hxs]
    rw [tieOvlLhs_congr _ _ hmap, tieOvlRhs_congr _ _ hmap]
    exact hb b
  · cases h

end

kernel_rfl tieOvlEqB_withHooks : ∀ (c : Semantics) (H : HookParams) (a : Kore.Axiom),
  tieOvlEqB (c.withHooks H) a = tieOvlEqB c a

/-! ## The no-confusion sentence of two generators that meet -/

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The valuation giving each of `ks` the element at its place in `vals` (the first place). -/
noncomputable def tieZipVal (ks : List EVar) (vals : List M) : Valuation M :=
  ⟨fun x => ((ks.zip vals).find? (·.1 == x)).elim default (·.2), fun _ _ => False⟩

theorem tieZipVal_map : ∀ {ks : List EVar} {vals : List M}, ks.Nodup → ks.length = vals.length →
    ks.map (tieZipVal ks vals).evalEvar = vals
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | k :: ks, v :: vals, hn, hl => by
    have hk : k ∉ ks := (List.nodup_cons.mp hn).1
    have hrest : ks.map (tieZipVal (k :: ks) (v :: vals)).evalEvar = ks.map (tieZipVal ks vals).evalEvar :=
      List.map_congr_left fun x hx => by
        have hne : (k == x) = false := by
          rw [beq_eq_false_iff_ne]; exact fun h => hk (h ▸ hx)
        simp only [tieZipVal, List.zip_cons_cons, List.find?_cons, hne]
    rw [List.map_cons, hrest, tieZipVal_map (List.nodup_cons.mp hn).2 (by simpa using hl)]
    simp [tieZipVal]

omit [Inhabited M] in
/-- The guards of variables whose elements are in their sorts hold. -/
theorem tieGuards_vals (hD : KoreAML.DefOK I) {t : KoreAML.VarTable} {e : Valuation M} :
    ∀ {ks : List Kore.EVar} {ss : List String} {vals : List M},
      ks.map (·.sort) = ss.map KoreAML.srt →
      (ks.map fun k => t.ev (KoreAML.evarKey k)).map e.evalEvar = vals →
      All2 (fun s v => (KoreAML.inhOf (KoreAML.Cons.sortP s)).interpret I e v) ss vals →
      ∀ k ∈ ks, ∀ m, (KoreAML.guardOf t (KoreAML.evarKey k)).interpret I e m
  | [], _, _, _, _, _, k, hk, _ => by simp at hk
  | _ :: _, [], _, hs, _, _, _, _, _ => by simp at hs
  | _ :: _, _ :: _, [], _, hv, _, _, _, _ => by simp at hv
  | k :: ks, s :: ss, v :: vals, hs, hv, hin, k', hk', m => by
    simp only [List.map_cons, List.cons.injEq] at hs hv
    cases hin with
    | cons h0 hrest =>
      rcases List.mem_cons.mp hk' with rfl | hk'
      · show (KoreAML.guardOf t (.evar k'.var.ident.name k'.sort)).interpret I e m
        rw [KoreAML.interp_guard_evar hD]
        have he : e.evalEvar (t.ev (.evar k'.var.ident.name k'.sort)) = v := hv.1
        rw [he, hs.1, trSort_srt]
        exact h0
      · exact tieGuards_vals hD hs.2 hv.2 hrest k' hk' m

/-- The elements of values of the sorts `ss` are in those sorts. -/
theorem tieElems_inS {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c) (e : Valuation M) :
    ∀ {ws : List GroundTerm} {ss : List Srt}, c.sortsOf ws = some ss →
      All2 (fun s v => (KoreAML.inhOf (KoreAML.Cons.sortP s)).interpret I e v)
        (ss.map c.sortName) (ws.map (elemOf c I))
  | [], ss, h => by
    simp only [Semantics.sortsOf, Option.some.injEq] at h; subst h; exact .nil
  | w :: ws, [], h => by
    simp only [Semantics.sortsOf] at h
    cases h1 : c.sortOf w <;> cases h2 : c.sortsOf ws <;> simp [h1, h2] at h
  | w :: ws, s :: ss, h => by
    obtain ⟨h1, h2⟩ := OvlLaws.sortsOf_cons_iff.mp h
    exact .cons (elemOf_spec hI h1 e).2 (tieElems_inS hI e h2)

/-- The axiom `a` is the no-confusion sentence of the symbols `k1` and `k2`, in the form
`tieDist_refuted` reads, at values `w1` and `w2` of their argument sorts that have one normal form
under the two symbols, of k1's result sort, which is k2's. -/
def tieOvlNcAtB (c : Semantics) (k1 k2 : CtorSig) (w1 w2 : List GroundTerm) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .not s (.and s' [p1, p2]) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take k1.args.length
    let ys := vs.drop k1.args.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName k1.result)) && decide (s' = KoreAML.srt (c.sortName k1.result)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = (k1.args.map c.sortName).map KoreAML.srt) &&
    decide (ys.map (·.sort) = (k2.args.map c.sortName).map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c.sortName k1.result) (Gen.toK c (.ctor k1)) (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c.sortName k1.result) (Gen.toK c (.ctor k2)) (iy.map .evar)) &&
    decide (ix ++ iy).Nodup && decide (k2.result = k1.result) &&
    decide (lookupSig (c.ctorSigs ++ c.ovlSigs) k1.name = some k1) &&
    decide (lookupSig (c.ctorSigs ++ c.ovlSigs) k2.name = some k2) &&
    decide (c.sortsOf w1 = some k1.args) && decide (c.sortsOf w2 = some k2.args) &&
    decide (c.fnCover k1.name w1 = none) && decide (c.fnCover k2.name w2 = none) &&
    decide (c.norm k1.name w1 = c.norm k2.name w2) && decide (c.sortOf (c.norm k1.name w1) = some k1.result) &&
    c.subsorts.all (fun p => c.subsorts.all fun q => !(p.2 == q.1) || c.subsorts.contains (p.1, q.2))
  | _ => false

/-- **A no-confusion sentence of two symbols that meet at values is refuted** by every model of Γ. -/
theorem tieOvlNc_refuted_at {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c) {k1 k2 : CtorSig}
    {w1 w2 : List GroundTerm} {a : Kore.Axiom} (h : tieOvlNcAtB c k1 k2 w1 w2 a = true) (i : Nat) (mod : String) :
    ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) := by
  have hD := defOK hI
  unfold tieOvlNcAtB at h
  split at h
  · rename_i s s' p1 p2 hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hs'⟩, hfree⟩, hxs⟩, hys⟩, hp1⟩, hp2⟩, hnd⟩, hres⟩, hk1⟩, hk2⟩,
      hw1⟩, hw2⟩, hc1⟩, hc2⟩, hnorm⟩, hsn⟩, htrB⟩ := h
    subst hs hs'
    have htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := by
      intro a b d h1 h2
      have := List.all_eq_true.mp (List.all_eq_true.mp htrB _ h1) _ h2
      simpa using this
    have hE1 := (norm_gs hI htr _ k1 hk1 (Nat.le_refl _) w1 hw1 hc1 (elemOf c I (c.norm k1.name w1))).mpr rfl
    have hE2 := (norm_gs hI htr _ k2 hk2 (Nat.le_refl _) w2 hw2 hc2 (elemOf c I (c.norm k1.name w1))).mpr
      (by rw [hnorm])
    rw [hres] at hE2
    have hin1 := tieElems_inS hI (I := I) (M := M) KoreAML.val0 hw1
    have hin2 := tieElems_inS hI (I := I) (M := M) KoreAML.val0 hw2
    generalize hvs : tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups = vs at hfree hxs hys hp1 hp2 hnd
    have hl1 : ((vs.take k1.args.length).map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).length =
        (w1.map (elemOf c I)).length := by
      have h1 := congrArg List.length hxs
      have h2 := hin1.length
      simp only [List.length_map] at h1 h2
      simp only [List.length_map]; rw [h1, h2]
    let e := tieZipVal (((vs.take k1.args.length).map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)) ++
      ((vs.drop k1.args.length).map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)))
      (w1.map (elemOf c I) ++ w2.map (elemOf c I))
    have hl2 : ((vs.drop k1.args.length).map fun k => (KoreAML.tableOf a.sortVars a.pattern).ev (KoreAML.evarKey k)).length =
        (w2.map (elemOf c I)).length := by
      have h1 := congrArg List.length hys
      have h2 := hin2.length
      simp only [List.length_map] at h1 h2
      simp only [List.length_map]; rw [h1, h2]
    have hval := tieZipVal_map (M := M) hnd (by rw [List.length_append, List.length_append, hl1, hl2])
    rw [List.map_append] at hval
    obtain ⟨hv1, hv2⟩ := List.append_inj hval (by rw [List.length_map, hl1])
    refine tieDist_refuted hD (xs := vs.take k1.args.length) (ys := vs.drop k1.args.length)
      (m := elemOf c I (c.norm k1.name w1)) hp hp1 hp2 e ?_ ?_ ?_ ?_
    · rw [hfree]
      intro k hk m
      rw [List.map_append, List.mem_append] at hk
      rcases hk with hk | hk
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
        exact tieGuards_vals hD hxs hv1 (by
          have := tieElems_inS hI (I := I) (M := M) e hw1
          exact this) x hx m
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
        exact tieGuards_vals hD hys hv2 (by
          have := tieElems_inS hI (I := I) (M := M) e hw2
          exact this) x hx m
    · exact (inS_iff KoreAML.val0).mp (elemOf_spec hI hsn KoreAML.val0).2
    · rw [hv1]; exact hE1
    · rw [hv2]; exact hE2
  · cases h

/-- The signature of the symbol a pattern applies, among the semantics' constructors and
overloading symbols. -/
def tieOvlNcSig (c : Semantics) : Kore.Pattern → Option CtorSig
  | .app h _ _ => (c.ctorSigs ++ c.ovlSigs).find? fun k => c.symName k.name == h.ident.name
  | _ => none

/-- Values of the argument sorts of `kg` (`exhibit?`), and their lifts to the argument sorts of
`k` (`inj` where the two sorts differ). -/
def tieOvlWit (c : Semantics) (k kg : CtorSig) : Option (List GroundTerm × List GroundTerm) :=
  (kg.args.mapM (Parse.exhibit? c)).map fun vs =>
    (((kg.args.zip k.args).zip vs).map fun p => if p.1.1 == p.1.2 then p.2 else .inj p.1.1 p.1.2 p.2, vs)

/-- **The axiom is a no-confusion sentence of two symbols that meet**: the symbols the two sides
apply, and values of their argument sorts at which they have one normal form, the values exhibited
for one symbol's arguments and lifted to the other's (in either order). -/
def tieOvlNcB (c : Semantics) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .not _ (.and _ [p1, p2]) =>
    match tieOvlNcSig c p1, tieOvlNcSig c p2 with
    | some k1, some k2 =>
      (match tieOvlWit c k1 k2 with
        | some (w1, w2) => tieOvlNcAtB c k1 k2 w1 w2 a
        | none => false) ||
      (match tieOvlWit c k2 k1 with
        | some (w2, w1) => tieOvlNcAtB c k1 k2 w1 w2 a
        | none => false)
    | _, _ => false
  | _ => false

theorem tieOvlNcB_at {c : Semantics} {a : Kore.Axiom} (h : tieOvlNcB c a = true) :
    ∃ k1 k2 w1 w2, tieOvlNcAtB c k1 k2 w1 w2 a = true := by
  unfold tieOvlNcB at h
  split at h
  · split at h
    · rename_i k1 k2 _ _
      rcases Bool.or_eq_true _ _ ▸ h with h | h
      · split at h
        · exact ⟨_, _, _, _, h⟩
        · cases h
      · split at h
        · exact ⟨_, _, _, _, h⟩
        · cases h
    · cases h
  · cases h

/-- **A no-confusion sentence `tieOvlNcB` accepts is refuted** by every model of Γ. -/
theorem tieOvlNc_refuted {c : Semantics} [OvlOK c] (hI : I ⊧ᴵP Γ c) {a : Kore.Axiom} (h : tieOvlNcB c a = true)
    (i : Nat) (mod : String) : ¬ (I ⊧ᴵ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat) :=
  let ⟨_, _, _, _, h⟩ := tieOvlNcB_at h
  tieOvlNc_refuted_at hI h i mod

end

end Faithful

/-- **The classes of the account of a text with a sentence of an overloading symbol**:
`tieClasses` with the class overload equation before no direction. An overload axiom
`tieOvlEqB` accepts is in that class; Γ entails it (`Faithful.tieOvlEq_entailed`). Its direction
is `entailed`: Γ's item states the equation at every element and the sentence within the
overloading symbol's result sort, so the item is not the sentence's translation. -/
def tieClassesOvl : List (String × TieDir) :=
  tieClasses.filter (·.1 != "no direction") ++ [("overload equation", .entailed), ("no direction", .none)]

end KCore
