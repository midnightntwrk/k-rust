/-
  The names' sorts of the arm (`nodR`, `KcoreSpec/GenEqsNodir.lean`) read from a table.

  `nodR` reads a name of `order` at the depth of `order`'s length, each name it applies one level
  down (`nodRAt`): a decision that evaluates it at each name of a deep tree reads the names below
  each one again, at another depth. Where every name of `order` comes after the names of `order`
  its right side applies (`armRankB`), the reading at any depth above a name's position is the
  same, so `nodR` is the table that gives each name of `order` its right side's sort read through
  the table itself, and every other name `nodBaseR`.

  - **The sorts are read only at the heads (`nodTy_congr_tbl`).** Two readings of the names that
    agree at every head of a pattern give it one sort.
  - **The table (`nodRTbl`, `nodTblB`).** A function `tf` on the names of `order`, extended by
    `nodBaseR`; the check that `tf` gives each name of `order` its right side's sort read through
    the table.
  - **What it gives (`nodR_eq_tbl`).** Where `order` is ranked and the table checks, `nodR` is the
    table: a decision then reads each name's right side once.
-/
import KcoreSpec.GenEqsNodir

set_option autoImplicit false

namespace KCore

namespace GenEqs

mutual
  /-- **The sort of a pattern depends on the names' sorts only at its heads.** -/
  theorem nodTy_congr_tbl (c : Semantics) (isN : String → Bool) (ar : String → Nat) (nA : String → List Srt)
      {nR nR' : String → Option (Srt × Bool)} (vs : List (Kore.EVar × Srt)) :
      ∀ p : Kore.Pattern, (∀ h ∈ armHeads p, nR h = nR' h) → nodTy c isN ar nA nR vs p = nodTy c isN ar nA nR' vs p
    | .var (.evar _), _ => by rw [nodTy, nodTy]
    | .dv _ _, _ => by rw [nodTy, nodTy]
    | .app h ss ps, hh => by
      have hs : ∀ n ∈ armHeadsL ps, nR n = nR' n :=
        fun n hn => hh n (by rw [armHeads]; exact List.mem_cons_of_mem _ hn)
      have h0 : nR h.ident.name = nR' h.ident.name := hh h.ident.name (by rw [armHeads]; exact List.mem_cons_self ..)
      rw [nodTy, nodTy, nodTys_congr_tbl c isN ar nA vs ps hs]
      unfold nodHead
      rw [h0]
    | .var (.svar _), _ => by simp only [nodTy]
    | .string _, _ => by simp only [nodTy]
    | .top _, _ => by simp only [nodTy]
    | .bottom _, _ => by simp only [nodTy]
    | .not _ _, _ => by simp only [nodTy]
    | .and _ _, _ => by simp only [nodTy]
    | .or _ _, _ => by simp only [nodTy]
    | .implies _ _ _, _ => by simp only [nodTy]
    | .iff _ _ _, _ => by simp only [nodTy]
    | .exist _ _ _, _ => by simp only [nodTy]
    | .forall _ _ _, _ => by simp only [nodTy]
    | .mu _ _, _ => by simp only [nodTy]
    | .nu _ _, _ => by simp only [nodTy]
    | .ceil _ _ _, _ => by simp only [nodTy]
    | .floor _ _ _, _ => by simp only [nodTy]
    | .equals _ _ _ _, _ => by simp only [nodTy]
    | .in _ _ _ _, _ => by simp only [nodTy]
    | .next _ _, _ => by simp only [nodTy]
    | .rewrites _ _ _, _ => by simp only [nodTy]
    | .leftAssoc _ _ _, _ => by simp only [nodTy]
    | .rightAssoc _ _ _, _ => by simp only [nodTy]
    termination_by structural p => p
  theorem nodTys_congr_tbl (c : Semantics) (isN : String → Bool) (ar : String → Nat) (nA : String → List Srt)
      {nR nR' : String → Option (Srt × Bool)} (vs : List (Kore.EVar × Srt)) :
      ∀ ps : List Kore.Pattern, (∀ h ∈ armHeadsL ps, nR h = nR' h) →
        nodTys c isN ar nA nR vs ps = nodTys c isN ar nA nR' vs ps
    | [], _ => by rw [nodTys, nodTys]
    | p :: ps, hh => by
      rw [nodTys, nodTys,
        nodTy_congr_tbl c isN ar nA vs p (fun n hn => hh n (by rw [armHeadsL]; exact List.mem_append_left _ hn)),
        nodTys_congr_tbl c isN ar nA vs ps (fun n hn => hh n (by rw [armHeadsL]; exact List.mem_append_right _ hn))]
    termination_by structural ps => ps
end

/-- The names' sorts read from a table: `tf` at a name of `order`, `nodBaseR` at another. -/
def nodRTbl (c : Semantics) (eqs : List Parse.RawEqn) (order : List String) (tf : String → Option (Srt × Bool)) :
    String → Option (Srt × Bool) :=
  fun n => if order.contains n then tf n else nodBaseR c eqs n

/-- The reading of the name `n` one level up from the names' sorts `nR`: its equation's right side's
sort (`nodRAt`'s step). -/
def nodRStep (c : Semantics) (names : List String) (eqs : List Parse.RawEqn) (order : List String)
    (nR : String → Option (Srt × Bool)) (n : String) : Option (Srt × Bool) :=
  match armLook order eqs n with
  | some e => match Parse.distinctEVars? e.pats with
    | some xs => nodTy c names.contains (armAr eqs) (nodA c eqs order) nR (xs.zip (nodA c eqs order n)) e.rhs
    | none => none
  | none => nodBaseR c eqs n

/-- **The check of a table**: it gives each name of `order` its right side's sort read through the
table. -/
def nodTblB (c : Semantics) (names : List String) (eqs : List Parse.RawEqn) (order : List String)
    (tf : String → Option (Srt × Bool)) : Bool :=
  order.all fun n => decide (tf n = nodRStep c names eqs order (nodRTbl c eqs order tf) n)

theorem nodRAt_succ_step (c : Semantics) (names : List String) (eqs : List Parse.RawEqn) (order : List String)
    (k : Nat) (n : String) :
    nodRAt c names.contains (armAr eqs) (nodA c eqs order) eqs order (k + 1) n =
      nodRStep c names eqs order (nodRAt c names.contains (armAr eqs) (nodA c eqs order) eqs order k) n := by
  rfl

/-- **At a depth above a name's position, the reading is the table's.** -/
theorem nodRAt_tbl {c : Semantics} {names : List String} {eqs : List Parse.RawEqn} {order : List String}
    {tf : String → Option (Srt × Bool)} (hR : armRankB order eqs = true) (hT : nodTblB c names eqs order tf = true) :
    ∀ k n, (order.contains n = true → order.idxOf n < k) →
      nodRAt c names.contains (armAr eqs) (nodA c eqs order) eqs order k n = nodRTbl c eqs order tf n := by
  intro k
  induction k with
  | zero =>
    intro n hk
    cases ho : order.contains n with
    | false =>
      have hl : armLook order eqs n = none := by unfold armLook; rw [ho]; rfl
      rw [nodRAt_none hl 0]
      unfold nodRTbl; rw [ho]; rfl
    | true => exact absurd (hk ho) (Nat.not_lt_zero _)
  | succ j ih =>
    intro n hk
    cases ho : order.contains n with
    | false =>
      have hl : armLook order eqs n = none := by unfold armLook; rw [ho]; rfl
      rw [nodRAt_none hl (j + 1)]
      unfold nodRTbl; rw [ho]; rfl
    | true =>
      have hlt := hk ho
      have hTn : tf n = nodRStep c names eqs order (nodRTbl c eqs order tf) n :=
        of_decide_eq_true (List.all_eq_true.mp hT n (List.contains_iff_mem.mp ho))
      rw [nodRAt_succ_step]
      have hrt : nodRTbl c eqs order tf n = tf n := by unfold nodRTbl; rw [ho]; rfl
      rw [hrt, hTn]
      unfold nodRStep
      cases he : armLook order eqs n with
      | none => rfl
      | some e =>
        dsimp only
        cases hx : Parse.distinctEVars? e.pats with
        | none => rfl
        | some xs =>
          dsimp only
          refine nodTy_congr_tbl c _ _ _ _ e.rhs fun h hh => ?_
          refine ih h fun hoh => ?_
          have := armRank_of order eqs hR he hh hoh
          omega

/-- **Where `order` is ranked and the table checks, the names' sorts are the table's.** -/
theorem nodR_eq_tbl {c : Semantics} {names : List String} {eqs : List Parse.RawEqn} {order : List String}
    {tf : String → Option (Srt × Bool)} (hR : armRankB order eqs = true) (hT : nodTblB c names eqs order tf = true) :
    nodR c names eqs order = nodRTbl c eqs order tf := by
  funext n
  exact nodRAt_tbl hR hT order.length n fun ho => List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp ho)

end GenEqs

end KCore
