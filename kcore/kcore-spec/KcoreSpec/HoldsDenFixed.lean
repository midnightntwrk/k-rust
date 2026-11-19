/-
  KCore. The Holds lemma at an `ex` binder of a sort that is not confined, in every model of `Γc`
  (`holds_binder_fixed`), and the lemma over `Cond.boundV` (`holds_den_fixed`).

  `Cond.boundV c val` accepts an `ex` binder of a sort s that `val` admits where the body fixes
  the bound variable by a term over the other variables (`Cond.fixes`), `val` true only at sorts
  with a value. In a model of `Γc` the sort s may have elements that are no value's, so the
  binder of the sentence, over the elements of s, is not the binder of `Holds`, over the values of
  s, by the sort alone. The two agree at such a body:
  - where `Holds` gives `true`, a value of s has the body true, and its element is a witness;
  - where an element of s satisfies the body, it is the element of a value (`fixes_value_read`,
    the body having a truth value at every value of s by the derivation of `Holds`), and the
    body is true at that value. So where `Holds` gives `false`, no element satisfies the body.

  The lemma is stated as the other cases are (`HoldsDenB`): only the variables the condition holds
  are read of the substitution and of the valuation. It reads the atoms' facts as a hypothesis, so
  the modules that prove them (TermSoundCEx.lean) import this one.

  The same reading at one truth value that comes with the readings of its terms (`HoldsRead`),
  with the constructors' facts in place of the atoms' (`holdsAt_ex_fixed`,
  `holdsReadT_holdsAt_fixed`, and `holdsReadT_holdsAt_bound` over `Cond.bound`): a recursion that
  proves the soundness of `EvalTerm` reads its own clauses' predicates through it. The fixing term's
  result at a substitution of values is the one the body's truth value at an extension of σ
  evaluates, which that substitution agrees with at the body's variables (`HoldsReadT.congr_NIR`).
-/
import KcoreSpec.FixesValue
import KcoreSpec.HoldsCongr
import KcoreSpec.CondTwoTables

set_option autoImplicit false

namespace KCore

open ML Faithful HoldsShape

namespace CE

section HoldsDenFixed
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **`holds_binder_fixed`: the `ex` case of the Holds lemma over `Cond.boundV`, in every model of
`Γc`** of a definition with `coreOK` that reads confined sorts, with the atoms' facts and `val`
true only at sorts with a value. The binder's sort is confined, and its elements are values'; or
`val` admits it and the body fixes the bound variable, and an element that satisfies the body is
a value's. -/
theorem holds_binder_fixed (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (F : AtomFacts c I) {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s)
    (s : Srt) {body : Cond} (ih : HoldsDenB (Cond.boundV c val) c I body) :
    HoldsDenB (Cond.boundV c val) c I (.ex s body) := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have G : BinderFacts c I := binderFacts_of_core h hrc hIc
  intro vars P σ b tbl e S hok hbd hP hr hk hS hh a ha
  rw [Semantics.condOK] at hok
  rw [Cond.boundV, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := by
    rcases hbd.1 with hc | ⟨hv, -⟩
    · exact G.confinedNum hc
    · obtain ⟨v, hv⟩ := hval s hv
      exact F.valNum hv
  obtain ⟨τ, hτ, hτd⟩ := F.sort hsn
  obtain ⟨τS, hτS, hτSd⟩ := F.sort hS
  let K := canonKey c (vars ++ [s]) vars.length
  have hkb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = K := Model.binder_keyStdI vars s
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.ex s body) =
      .exist (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
        (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
    rw [← Model.canonVars_snocStdI c vars s]; rfl
  rw [hkore] at hk ⊢
  have hK : K ∈ tbl := hk _ (by rw [KoreAML.varsOf, hkb]; simp)
  have hkB : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body), k ∈ tbl :=
    fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have hPB : ∀ i ∈ varOccsCond (vars ++ [s]).length body, i < (vars ++ [s]).length → P i ∨ i = vars.length := by
    intro i hi hl
    rw [hlen] at hi hl
    by_cases hlt : i < vars.length
    · exact .inl (hP i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hlt⟩) hlt)
    · exact .inr (by omega)
  have haS : ∀ e' : Valuation M, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e' a :=
    fun e' => (KoreAML.interp_inhOf_of (hτSd tbl e')).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha)
  have hread : ∀ σ' v a0, (∀ i < vars.length, σ'.lookup i = σ.lookup i) → σ'.lookup vars.length = some v →
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) → ∀ b', Holds c (vars.length + 1) σ' body b' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ b' = true) := by
    intro σ' v a0 hσ' hn hv hd b' hb'
    exact ih hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS
      (by rw [hlen]; exact hb') a (haS _)
  have hsrt : ∀ (e' : Valuation M) m,
      (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret I e' m ↔
        KoreAML.Inh I τ m := fun e' m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret _ _ m ↔ _
    exact KoreAML.interp_inhOf_of (hτd tbl e')
  have hextOne : ∀ v, c.sortOf v = some s → Extends c vars.length [s] σ (Model.extOneStdI σ vars.length v) :=
    fun v hv => ⟨fun i hi => Model.extOneStdI_off σ v (by omega), fun j s' hj => by
      cases j with
      | zero => simp at hj; subst hj; exact ⟨v, Model.extOneStdI_at σ _ v, hv⟩
      | succ j => simp at hj⟩
  cases hh with
  | ex g hb hr' =>
    -- an element of s that satisfies the body is a value's
    have hE : ∀ m, KoreAML.Inh I τ m →
        (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
          ⟨Function.update e.evalEvar (tbl.ev K) m, e.evalSvar⟩ a →
        ∃ v, c.sortOf v = some s ∧ ∀ m', (den c v).interpret I e m' ↔ m' = m := by
      intro m hm hbody
      have hms : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret I e m :=
        (KoreAML.interp_inhOf_of (hτd tbl e)).mpr hm
      rcases hbd.1 with hc | ⟨hv, hfx⟩
      · exact G.confined hc tbl e m hms
      · obtain ⟨v0, hv0⟩ := hval s hv
        -- the valuation under the binder, and what it keeps of the variables read
        have hkey : ∀ j, j < vars.length → canonKey c (vars ++ [s]) j = canonKey c vars j :=
          fun j hj => Model.canonKey_appendStdI (c := c) (ys := [s]) hj
        have hev : ∀ j, P j →
            Function.update e.evalEvar (tbl.ev K) m (tbl.ev (canonKey c vars j)) =
              e.evalEvar (tbl.ev (canonKey c vars j)) := by
          intro j hPj
          obtain ⟨hl, hkj, -⟩ := hr j hPj
          rw [Function.update_noteq]
          intro he
          have := canonKey_inj (vars := vars ++ [s]) (c := c) (i := j) (j := vars.length) (by simp; omega) (by simp)
            ((hkey j hl).trans (ev_inj hkj hK he))
          omega
        have hgd : ∀ j, j < vars.length → (vars ++ [s]).getD j 0 = vars.getD j 0 :=
          fun j hj => Model.getD_appendL_stdI _ _ _ hj
        -- a read variable is at the element of its value under σ
        have hat : ∀ j, P j → ∃ w, σ.lookup j = some w ∧ c.sortOf w = some (vars.getD j 0) ∧
            elemOf c I w = e.evalEvar (tbl.ev (canonKey c vars j)) := by
          intro j hPj
          obtain ⟨-, -, w, hw, hsw, hd⟩ := hr j hPj
          exact ⟨w, hw, hsw, (((elemOf_spec hI hsw e).1 _).mp ((hd _).mp rfl)).symm⟩
        have hσP : SortedOn c vars P σ := fun j s' hPj hj => by
          obtain ⟨w, hw, hsw, -⟩ := hat j hPj
          exact ⟨w, hw, by rw [hsw, List.getD_eq_getElem?_getD, hj]; rfl⟩
        have hW := fixes_value_read h hrc hIc F hval body (fun j => j != vars.length)
          (fun j => P j ∨ j = vars.length) vars.length (vars ++ [s]) tbl
          ⟨Function.update e.evalEvar (tbl.ev K) m, e.evalSvar⟩ S hok (by rw [hlen]; exact hbd.2)
          (by rw [hlen]; exact hfx) (by rw [hlen]; omega) (Or.inr rfl) hPB
          ⟨_, sortedOn_snocFV hσP hv0⟩
          (fun σ' hσ' hat' => by
            -- the body has a truth value at σ with the value σ' gives the bound variable, and σ'
            -- is that substitution at the body's variables
            obtain ⟨v, hσ'n, hv⟩ := hσ' vars.length s (Or.inr rfl) (by simp)
            refine ⟨g (Model.extOneStdI σ vars.length v), ?_⟩
            rw [hlen]
            refine (hb _ (hextOne v hv)).congr_NI fun j hj => ?_
            have hjl : j < vars.length + 1 := by
              have := varOccsCond_lt_twoT body hok j (by rw [hlen]; exact hj)
              rwa [hlen] at this
            by_cases hjn : j = vars.length
            · subst hjn
              rw [Model.extOneStdI_at, hσ'n]
            · have hl : j < vars.length := by omega
              have hPj : P j := (hPB j (by rw [hlen]; exact hj) (by rw [hlen]; exact hjl)).resolve_right hjn
              rw [Model.extOneStdI_off σ v hjn]
              obtain ⟨w, hw, hsw, hew⟩ := hat j hPj
              obtain ⟨w', hw', hew'⟩ := hat' j (by simpa using hjn) (Or.inl hPj) (by rw [hlen]; exact hjl)
              obtain ⟨w'', hw'', hsw''⟩ := hσ' j (vars.getD j 0) (Or.inl hPj) (by
                rw [List.getElem?_append_left hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl)
              rw [hw', Option.some.injEq] at hw''
              subst hw''
              have hew'' : elemOf c I w' = e.evalEvar (tbl.ev (canonKey c vars j)) := by
                rw [← hev j hPj, ← hkey j hl]; exact hew'
              have hww : w = w' := F.apart hsw hsw'' e (e.evalEvar (tbl.ev (canonKey c vars j)))
                (((elemOf_spec hI hsw e).1 _).mpr hew.symm) (((elemOf_spec hI hsw'' e).1 _).mpr hew''.symm)
              rw [hw, hw', hww])
          (fun j hj hRj hjl => by
            have hjn : j ≠ vars.length := by simpa using hj
            have hPj : P j := hRj.resolve_right hjn
            obtain ⟨hl, -, -⟩ := hr j hPj
            obtain ⟨w, -, hsw, hew⟩ := hat j hPj
            refine ⟨w, by rw [hgd j hl]; exact hsw, ?_⟩
            show elemOf c I w = Function.update e.evalEvar (tbl.ev K) m (tbl.ev (canonKey c (vars ++ [s]) j))
            rw [hkey j hl, hev j hPj]; exact hew)
          (fun j hRj hjl => by
            rw [hlen] at hjl
            by_cases hjn : j = vars.length
            · subst hjn
              refine ⟨hK, ?_⟩
              show InS I (c.sortName ((vars ++ [s]).getD vars.length 0))
                (Function.update e.evalEvar (tbl.ev K) m (tbl.ev K))
              rw [Function.update_same, Model.getD_appendR_stdI _ _ _ (Nat.le_refl _)]
              simpa using inhOf_srtOf_inS.mp hms
            · have hPj : P j := hRj.resolve_right hjn
              obtain ⟨hl, hkj, -⟩ := hr j hPj
              refine ⟨by rw [hkey j hl]; exact hkj, ?_⟩
              show InS I (c.sortName ((vars ++ [s]).getD j 0))
                (Function.update e.evalEvar (tbl.ev K) m (tbl.ev (canonKey c (vars ++ [s]) j)))
              rw [hgd j hl, hkey j hl, hev j hPj]
              exact inhOf_srtOf_inS.mp (hr.inSort F hPj))
          hkB hS ⟨a, haS _, hbody⟩
        obtain ⟨v, hv, hve⟩ := hW
        have hv' : c.sortOf v = some s := by
          rw [Model.getD_appendR_stdI _ _ _ (Nat.le_refl _)] at hv; simpa using hv
        have hve' : elemOf c I v = m := by
          have : elemOf c I v = Function.update e.evalEvar (tbl.ev K) m (tbl.ev K) := hve
          rwa [Function.update_same] at this
        exact ⟨v, hv', fun m' => by rw [(elemOf_spec hI hv' e).1 m', hve']⟩
    rw [KoreAML.tr, KoreAML.interp_sExists, hkb]
    simp only [KoreAML.interp_member F.defOK, Function.update_same, hsrt]
    constructor
    · rintro ⟨m, hm, hbody⟩
      obtain ⟨v, hv, hdv⟩ := hE m hm hbody
      have hext := hextOne v hv
      exact hr'.mpr ⟨_, hext, (hread _ v m hext.1 (Model.extOneStdI_at σ _ v) hv hdv _ (hb _ hext)).mp hbody⟩
    · intro hbt
      obtain ⟨σ', hext, hg⟩ := hr'.mp hbt
      obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
      rw [Nat.add_zero] at hv
      obtain ⟨a0, ha0, hin⟩ := F.val hsv tbl e
      exact ⟨a0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin, (hread σ' v a0 hext.1 hv hsv ha0 _ (hb σ' hext)).mpr hg⟩

/-- **The Holds lemma over `Cond.boundV`, in every model of `Γc`** of a definition with `coreOK`,
with the atoms' facts and `val` true only at sorts with a value, by structural recursion;
`readsConfined` is asked only of a condition with a binder. -/
theorem holds_den_fixed (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) (F : AtomFacts c I) {val : Srt → Bool}
    (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s) :
    ∀ p : Cond, (hasBinder p = true → c.readsConfined = true) → HoldsDenB (Cond.boundV c val) c I p
  | .top, _ => fun hok _ hP hr hk hS hh a ha => holds_top' F hok rfl hP hr hk hS hh a ha
  | .bot, _ => fun hok _ hP hr hk hS hh a ha => holds_bot' F hok rfl hP hr hk hS hh a ha
  | .not p, hrc => holds_notB (bd := Cond.boundV c val) (fun hb => by rw [Cond.boundV] at hb; exact hb)
      (holds_den_fixed h hIc F hval p hrc)
  | .and p q, hrc => holds_andB (bd := Cond.boundV c val)
      (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb)
      (holds_den_fixed h hIc F hval p fun hp => hrc (by rw [hasBinder, hp, Bool.true_or]))
      (holds_den_fixed h hIc F hval q fun hq => hrc (by rw [hasBinder, hq, Bool.or_true]))
  | .or p q, hrc => holds_orB (bd := Cond.boundV c val)
      (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb)
      (holds_den_fixed h hIc F hval p fun hp => hrc (by rw [hasBinder, hp, Bool.true_or]))
      (holds_den_fixed h hIc F hval q fun hq => hrc (by rw [hasBinder, hq, Bool.or_true]))
  | .implies p q, hrc => holds_impliesB (bd := Cond.boundV c val)
      (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb)
      (holds_den_fixed h hIc F hval p fun hp => hrc (by rw [hasBinder, hp, Bool.true_or]))
      (holds_den_fixed h hIc F hval q fun hq => hrc (by rw [hasBinder, hq, Bool.or_true]))
  | .ceil s t, _ => fun hok _ hP hr hk hS hh a ha => holds_ceil' F s t hok rfl hP hr hk hS hh a ha
  | .equals s t u, _ => fun hok _ hP hr hk hS hh a ha => holds_equals' F s t u hok rfl hP hr hk hS hh a ha
  | .mem s t u, _ => fun hok _ hP hr hk hS hh a ha => holds_mem' F s t u hok rfl hP hr hk hS hh a ha
  | .exMatch ys s p t body, hrc =>
      holds_exMatchB F (binderFacts_of_core h (hrc rfl) hIc) (bd := Cond.boundV c val)
        (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb) ys s p t
        (holds_den_fixed h hIc F hval body fun _ => hrc rfl)
  | .ex s body, hrc =>
      holds_binder_fixed h (hrc rfl) hIc F hval s (holds_den_fixed h hIc F hval body fun _ => hrc rfl)
  | .all s body, hrc =>
      holds_allB F (bd := Cond.boundV c val) (body := body) s
        (fun hb => by
          rw [Cond.boundV, Bool.and_eq_true] at hb
          exact ⟨(binderFacts_of_core h (hrc rfl) hIc).elemsValues hb.1, hb.2⟩)
        (holds_den_fixed h hIc F hval body fun _ => hrc rfl)

/-- **The reading at one truth value over `Cond.boundV`, in every model of `Γc`**: `holds_den_fixed`
at the truth value a derivation of `Holds` gives. -/
theorem holdsAt_den_fixed (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) (F : AtomFacts c I) {val : Srt → Bool}
    (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s) {p : Cond}
    (hrc : hasBinder p = true → c.readsConfined = true) {n : Nat} {σ : Subst} {b : Bool}
    (hh : Holds c n σ p b) : HoldsAtB (Cond.boundV c val) c I n σ p b :=
  holdsAt_of_den (holds_den_fixed h hIc F hval p hrc) hh

/-- **The Holds lemma over `Cond.bound`, in every model of `Γc`**: `holds_den_fixed` at
`Semantics.valued`, whose Bool bounds every condition `Cond.bound` bounds. -/
theorem holds_den_bound (h : c.coreOK = true) (hIc : I ⊧ᴵP Γc c) (F : AtomFacts c I) (p : Cond)
    (hrc : hasBinder p = true → c.readsConfined = true) : HoldsDenB (Cond.bound c) c I p :=
  HoldsDenB.mono (Cond.boundV_valued_of_bound c p) (holds_den_fixed h hIc F (fun _ => Semantics.valued_value) p hrc)

omit [Inhabited M] in
/-- An evaluation read in I (`TermAt`) is read whatever σ is sorted on: `TermAt` asks of σ only
the values `Reads` gives the term's variables. -/
theorem termUse_termAtW {w : Prop} : TermUse c I w (TermAt c I) :=
  fun hT _ _ _ _ _ _ hP hr ht m => hT hP hr ht m

/-- **The `ex` case of reading a truth value with its terms' readings over `Cond.boundV`, in every
model of `Γc`** of a definition with `coreOK` that reads confined sorts, with the constructors'
facts and `val` true only at sorts with a value: `holdsAt_ex` where the binder's sort is confined,
and, where `val` admits it and the body fixes the bound variable, the argument of
`holds_binder_fixed` with the body's truth values read through their terms (`HoldsRead`) in place
of the soundness of `EvalTerm`. An element of the sort that satisfies the body is a value's
(`fixes_value_readT` over `TermAt`): the body has a truth value at each substitution that gives
the variables read the values the valuation reads and the bound variable a value, the one it has
at the extension of σ by that value, by `HoldsReadT.congr_NIR`. -/
theorem holdsAt_ex_fixed (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s)
    {n : Nat} {σ : Subst} {s : Srt} {body : Cond} {b : Bool} (g : Subst → Bool)
    (hb : ∀ σ', Extends c n [s] σ σ' → HoldsRead c I (n + 1) σ' body (g σ'))
    (ih : ∀ σ', Extends c n [s] σ σ' → HoldsAtB (Cond.boundV c val) c I (n + 1) σ' body (g σ'))
    (hr' : b = true ↔ ∃ σ', Extends c n [s] σ σ' ∧ g σ' = true) :
    HoldsAtB (Cond.boundV c val) c I n σ (.ex s body) b := by
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have G : BinderFacts c I := binderFacts_of_core h hrc hIc
  intro vars P tbl e S hlenN hok hbd hP hr hk hS a ha
  subst hlenN
  rw [Semantics.condOK] at hok
  rw [Cond.boundV, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hbd
  have hlen : (vars ++ [s]).length = vars.length + 1 := by simp
  have hsn : s < nRegSorts + c.sortNames.length := by
    rcases hbd.1 with hc | ⟨hv, -⟩
    · exact G.confinedNum hc
    · obtain ⟨v, hv⟩ := hval s hv
      exact N.valNum hv
  obtain ⟨τ, hτ, hτd⟩ := N.sort hsn
  obtain ⟨τS, hτS, hτSd⟩ := N.sort hS
  let K := canonKey c (vars ++ [s]) vars.length
  have hkb : KoreAML.evarKey (Cond.binder c (canonVars c vars).length s).kore = K := Model.binder_keyStdI vars s
  have hkore : Cond.kore c (canonVars c vars) (srtOf c S) (.ex s body) =
      .exist (srtOf c S) (Cond.binder c (canonVars c vars).length s).kore
        (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body) := by
    rw [← Model.canonVars_snocStdI c vars s]; rfl
  rw [hkore] at hk ⊢
  have hK : K ∈ tbl := hk _ (by rw [KoreAML.varsOf, hkb]; simp)
  have hkB : ∀ k ∈ KoreAML.varsOf (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body), k ∈ tbl :=
    fun k hk0 => hk k (by rw [KoreAML.varsOf]; exact List.mem_append_right _ hk0)
  have hPB : ∀ i ∈ varOccsCond (vars ++ [s]).length body, i < (vars ++ [s]).length → P i ∨ i = vars.length := by
    intro i hi hl
    rw [hlen] at hi hl
    by_cases hlt : i < vars.length
    · exact .inl (hP i (by rw [varOccsCond]; exact List.mem_filter.mpr ⟨hi, by simpa using hlt⟩) hlt)
    · exact .inr (by omega)
  have haS : ∀ e' : Valuation M, (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c S))).interpret I e' a :=
    fun e' => (KoreAML.interp_inhOf_of (hτSd tbl e')).mpr ((KoreAML.interp_inhOf_of (hτSd tbl e)).mp ha)
  have hread : ∀ σ' v a0, (∀ i < vars.length, σ'.lookup i = σ.lookup i) → σ'.lookup vars.length = some v →
      c.sortOf v = some s → (∀ m, (den c v).interpret I e m ↔ m = a0) → Extends c vars.length [s] σ σ' →
      ((KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) a0, e.evalSvar⟩ a ↔ g σ' = true) := by
    intro σ' v a0 hσ' hn hv hd hx
    exact ih σ' hx hlen hok (by rw [hlen]; exact hbd.2) hPB (hr.snoc hK hσ' hn hv hd) hkB hS a (haS _)
  have hsrt : ∀ (e' : Valuation M) m,
      (KoreAML.inhOf (KoreAML.trSort tbl (Cond.binder c (canonVars c vars).length s).kore.sort)).interpret I e' m ↔
        KoreAML.Inh I τ m := fun e' m => by
    show (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret _ _ m ↔ _
    exact KoreAML.interp_inhOf_of (hτd tbl e')
  have hextOne : ∀ v, c.sortOf v = some s → Extends c vars.length [s] σ (Model.extOneStdI σ vars.length v) :=
    fun v hv => ⟨fun i hi => Model.extOneStdI_off σ v (by omega), fun j s' hj => by
      cases j with
      | zero => simp at hj; subst hj; exact ⟨v, Model.extOneStdI_at σ _ v, hv⟩
      | succ j => simp at hj⟩
  -- an element of s that satisfies the body is a value's
  have hE : ∀ m, KoreAML.Inh I τ m →
      (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c (vars ++ [s])) (srtOf c S) body)).interpret I
        ⟨Function.update e.evalEvar (tbl.ev K) m, e.evalSvar⟩ a →
      ∃ v, c.sortOf v = some s ∧ ∀ m', (den c v).interpret I e m' ↔ m' = m := by
    intro m hm hbody
    have hms : (KoreAML.inhOf (KoreAML.trSort tbl (srtOf c s))).interpret I e m :=
      (KoreAML.interp_inhOf_of (hτd tbl e)).mpr hm
    rcases hbd.1 with hc | ⟨hv, hfx⟩
    · exact G.confined hc tbl e m hms
    · obtain ⟨v0, hv0⟩ := hval s hv
      have hkey : ∀ j, j < vars.length → canonKey c (vars ++ [s]) j = canonKey c vars j :=
        fun j hj => Model.canonKey_appendStdI (c := c) (ys := [s]) hj
      have hev : ∀ j, P j →
          Function.update e.evalEvar (tbl.ev K) m (tbl.ev (canonKey c vars j)) =
            e.evalEvar (tbl.ev (canonKey c vars j)) := by
        intro j hPj
        obtain ⟨hl, hkj, -⟩ := hr j hPj
        rw [Function.update_noteq]
        intro he
        have := canonKey_inj (vars := vars ++ [s]) (c := c) (i := j) (j := vars.length) (by simp; omega) (by simp)
          ((hkey j hl).trans (ev_inj hkj hK he))
        omega
      have hgd : ∀ j, j < vars.length → (vars ++ [s]).getD j 0 = vars.getD j 0 :=
        fun j hj => Model.getD_appendL_stdI _ _ _ hj
      have hat : ∀ j, P j → ∃ w, σ.lookup j = some w ∧ c.sortOf w = some (vars.getD j 0) ∧
          elemOf c I w = e.evalEvar (tbl.ev (canonKey c vars j)) := by
        intro j hPj
        obtain ⟨-, -, w, hw, hsw, hd⟩ := hr j hPj
        exact ⟨w, hw, hsw, (((elemOf_spec hI hsw e).1 _).mp ((hd _).mp rfl)).symm⟩
      have hσP : SortedOn c vars P σ := fun j s' hPj hj => by
        obtain ⟨w, hw, hsw, -⟩ := hat j hPj
        exact ⟨w, hw, by rw [hsw, List.getD_eq_getElem?_getD, hj]; rfl⟩
      have hW := fixes_value_readT h hrc hIc N (w := False) termUse_termAtW hval [] body
        (fun j => j != vars.length) (fun j => P j ∨ j = vars.length) vars.length (vars ++ [s]) tbl
        ⟨Function.update e.evalEvar (tbl.ev K) m, e.evalSvar⟩ S hok (by rw [hlen]; exact hbd.2)
        (by rw [hlen]; exact hfx) (by rw [hlen]; omega) (Or.inr rfl) hPB
        ⟨_, (sortedOn_snocFV hσP hv0).mono fun _ hj => hj.elim id False.elim⟩
        (fun σ' _ hσ' hat' => by
          -- the body has the truth value it has at the extension of σ by the value σ' gives the
          -- bound variable, σ' being that extension at the body's variables
          obtain ⟨v, hσ'n, hv⟩ := hσ' vars.length s (.inl (Or.inr rfl)) (by simp)
          refine ⟨g (Model.extOneStdI σ vars.length v), ?_⟩
          rw [hlen]
          refine (hb _ (hextOne v hv)).congr_NIR (fun hT ha => hT.congr_occ fun i hi => (ha i hi).symm) _
            fun j hj => ?_
          have hjl : j < vars.length + 1 := by
            have := varOccsCond_lt_twoT body hok j (by rw [hlen]; exact hj)
            rwa [hlen] at this
          by_cases hjn : j = vars.length
          · subst hjn
            rw [Model.extOneStdI_at, hσ'n]
          · have hl : j < vars.length := by omega
            have hPj : P j := (hPB j (by rw [hlen]; exact hj) (by rw [hlen]; exact hjl)).resolve_right hjn
            rw [Model.extOneStdI_off σ v hjn]
            obtain ⟨w, hw, hsw, hew⟩ := hat j hPj
            obtain ⟨w', hw', hew'⟩ := hat' j (by simpa using hjn) (Or.inl hPj) (by rw [hlen]; exact hjl)
            obtain ⟨w'', hw'', hsw''⟩ := hσ' j (vars.getD j 0) (.inl (Or.inl hPj)) (by
              rw [List.getElem?_append_left hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; rfl)
            rw [hw', Option.some.injEq] at hw''
            subst hw''
            have hew'' : elemOf c I w' = e.evalEvar (tbl.ev (canonKey c vars j)) := by
              rw [← hev j hPj, ← hkey j hl]; exact hew'
            have hww : w = w' := N.apart hsw hsw'' e (e.evalEvar (tbl.ev (canonKey c vars j)))
              (((elemOf_spec hI hsw e).1 _).mpr hew.symm) (((elemOf_spec hI hsw'' e).1 _).mpr hew''.symm)
            rw [hw, hw', hww])
        (fun j hj hRj hjl => by
          have hjn : j ≠ vars.length := by simpa using hj
          have hPj : P j := hRj.resolve_right hjn
          obtain ⟨hl, -, -⟩ := hr j hPj
          obtain ⟨w, -, hsw, hew⟩ := hat j hPj
          refine ⟨w, by rw [hgd j hl]; exact hsw, ?_⟩
          show elemOf c I w = Function.update e.evalEvar (tbl.ev K) m (tbl.ev (canonKey c (vars ++ [s]) j))
          rw [hkey j hl, hev j hPj]; exact hew)
        (fun j hRj hjl => by
          rw [hlen] at hjl
          by_cases hjn : j = vars.length
          · subst hjn
            refine ⟨hK, ?_⟩
            show InS I (c.sortName ((vars ++ [s]).getD vars.length 0))
              (Function.update e.evalEvar (tbl.ev K) m (tbl.ev K))
            rw [Function.update_same, Model.getD_appendR_stdI _ _ _ (Nat.le_refl _)]
            simpa using inhOf_srtOf_inS.mp hms
          · have hPj : P j := hRj.resolve_right hjn
            obtain ⟨hl, hkj, -⟩ := hr j hPj
            refine ⟨by rw [hkey j hl]; exact hkj, ?_⟩
            show InS I (c.sortName ((vars ++ [s]).getD j 0))
              (Function.update e.evalEvar (tbl.ev K) m (tbl.ev (canonKey c (vars ++ [s]) j)))
            rw [hgd j hl, hkey j hl, hev j hPj]
            exact inhOf_srtOf_inS.mp (Reads.inSortN N hr hPj))
        hkB hS ⟨a, haS _, hbody⟩
      obtain ⟨v, hv, hve⟩ := hW
      have hv' : c.sortOf v = some s := by
        rw [Model.getD_appendR_stdI _ _ _ (Nat.le_refl _)] at hv; simpa using hv
      have hve' : elemOf c I v = m := by
        have : elemOf c I v = Function.update e.evalEvar (tbl.ev K) m (tbl.ev K) := hve
        rwa [Function.update_same] at this
      exact ⟨v, hv', fun m' => by rw [(elemOf_spec hI hv' e).1 m', hve']⟩
  rw [KoreAML.tr, KoreAML.interp_sExists, hkb]
  simp only [KoreAML.interp_member N.defOK, Function.update_same, hsrt]
  constructor
  · rintro ⟨m, hm, hbody⟩
    obtain ⟨v, hv, hdv⟩ := hE m hm hbody
    have hext := hextOne v hv
    exact hr'.mpr ⟨_, hext, (hread _ v m hext.1 (Model.extOneStdI_at σ _ v) hv hdv hext).mp hbody⟩
  · intro hbt
    obtain ⟨σ', hext, hg⟩ := hr'.mp hbt
    obtain ⟨v, hv, hsv⟩ := hext.2 0 s rfl
    rw [Nat.add_zero] at hv
    obtain ⟨a0, ha0, hin⟩ := N.val hsv tbl e
    exact ⟨a0, (KoreAML.interp_inhOf_of (hτd tbl e)).mp hin, (hread σ' v a0 hext.1 hv hsv ha0 hext).mpr hg⟩

/-- **A truth value with its terms' readings is read in I over `Cond.boundV`, in every model of
`Γc`** of a definition with `coreOK` that reads confined sorts, with the constructors' facts and
`val` true only at sorts with a value: each constructor by its lemma over the Bool
(`holdsAt_notB`, …, `holdsAt_exMatchB`, `holdsAt_allB`; an atom does not read the Bool), the `ex`
binder by `holdsAt_ex_fixed`. -/
theorem holdsReadT_holdsAt_fixed (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {val : Srt → Bool} (hval : ∀ s, val s = true → ∃ v, c.sortOf v = some s)
    {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (hh : HoldsRead c I n σ p b) :
    HoldsAtB (Cond.boundV c val) c I n σ p b := by
  have G : BinderFacts c I := binderFacts_of_core h hrc hIc
  induction hh with
  | top => exact holdsAt_top N
  | bot => exact holdsAt_bot N
  | not _ ih => exact holdsAt_notB (fun hb => by rw [Cond.boundV] at hb; exact hb) ih
  | and _ _ ih ih' => exact holdsAt_andB (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb) ih ih'
  | or _ _ ih ih' => exact holdsAt_orB (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb) ih ih'
  | implies _ _ ih ih' =>
    exact holdsAt_impliesB (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb) ih ih'
  | ceil he hT => exact HoldsAtB.mono (fun _ _ => rfl) (holdsAt_ceil N he hT)
  | equals he hT he' hT' => exact HoldsAtB.mono (fun _ _ => rfl) (holdsAt_equals N he hT he' hT')
  | mem he hT he' hT' => exact HoldsAtB.mono (fun _ _ => rfl) (holdsAt_mem N he hT he' hT')
  | exNone he hT =>
    exact holdsAt_exMatchB N G (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb) he hT
      (Or.inl ⟨rfl, rfl⟩)
  | exSome g he hT _ hr ih =>
    exact holdsAt_exMatchB N G (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact hb) he hT
      (Or.inr ⟨_, g, rfl, ih, hr⟩)
  | ex g hb hr ih => exact holdsAt_ex_fixed h hrc hIc N hval g hb ih hr
  | all g _ hr ih =>
    exact holdsAt_allB N
      (fun hb => by rw [Cond.boundV, Bool.and_eq_true] at hb; exact ⟨G.elemsValues hb.1, hb.2⟩) g ih hr

/-- **A truth value with its terms' readings is read in I over `Cond.bound`, in every model of
`Γc`**: `holdsReadT_holdsAt_fixed` at `Semantics.valued`, whose Bool bounds every condition
`Cond.bound` bounds. -/
theorem holdsReadT_holdsAt_bound (h : c.coreOK = true) (hrc : c.readsConfined = true) (hIc : I ⊧ᴵP Γc c)
    (N : NodeFacts c I) {n : Nat} {σ : Subst} {p : Cond} {b : Bool} (hh : HoldsRead c I n σ p b) :
    HoldsAtB (Cond.bound c) c I n σ p b :=
  HoldsAtB.mono (fun m hb => Cond.boundV_valued_of_bound c p m hb)
    (holdsReadT_holdsAt_fixed h hrc hIc N (fun _ => Semantics.valued_value) hh)

end HoldsDenFixed

end CE

end KCore
