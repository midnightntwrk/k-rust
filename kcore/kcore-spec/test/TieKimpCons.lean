/-
  The tie (C14) of kimp's constructor sentences (rows 8, 11 to 14) on its text as kompile wrote it
  (`examples/ref-kimp/RefKimp/definition.kore`, user module `IMP`), on the literals `kore` and
  `defn`. Nothing here reads `Parse.parse` or `emit`. Run from the package root:
  `lake env lean test/TieKimpCons.lean`.

  - `cons_entailed` (E): Γ entails, for every H, each of the 565 sentences of the classes
    constructor functional (54), subsort (25), injectivity (49) and distinctness (437) of the
    account (`cons_account`). Each is read at a constructor sort and generators of it named in
    `consPairs`, as the `functional` or `subsort` sentence of a generator (kind 0), the no-confusion
    sentence of one generator (kind 1) or of two (kind 2), and follows from Γ's constructor items
    that the reading names by their places in `consItemsK c` (`consAt_entailed`, through
    `tieFun_entailed`, `tieInj_entailed`, `tieDist_entailed`). The places are hints: each is
    checked by the kernel to hold the item. Decided by ranges of `consPairs`, joined by
    `tieAll_range`.
  - `nojunk_entailed` (E): Γ entails, for every H, each of the 16 no-junk sentences. Four
    (Bool, Id, Int, KConfigVar: `\or{S}(\top{S}(), \bottom{S}())`) are logical truths
    (`nojunk_trivial_entailed`). Ten are Γ's no-junk item of their sort, pattern for pattern
    (`nojunk_items`). Expr's and KItem's list their generators in another order than Γ's item
    does (`nojunk_order`): Γ's item entails them (`noJunkItem_of_subset`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieKimp

open KCore ML Faithful KoreAML

kore_term kore from "examples/ref-kimp/RefKimp/definition.kore"
definition_of defn from "examples/ref-kimp/RefKimp/definition.kore"
user_axioms U from "examples/ref-kimp/RefKimp/definition.kore" module "IMP"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

/-- No overloading symbol, and irreflexive subsorts: what the readings of Γ's constructor items ask. -/
theorem ovls_nil : c.ovls = [] := by decide +kernel
theorem subsorts_irrefl : c.subsorts.all (fun p => p.1 != p.2) = true := by decide +kernel
instance ovlOKH (H : HookParams) : OvlOK (cH H) := OvlOK.of_nil ovls_nil subsorts_irrefl

/-! ## A constructor sentence read at a named sort, generators and items

`tieConsB` finds the sort and the generators by search, and each of `tieFunB`, `tieInjB`, `tieDistB`
finds Γ's items by a search through `consItemsK c`; on this text (13 constructor sorts, KItem with 44
generators, 1304 items) one kernel decision of `tieConsB` over 20 of KItem's distinctness sentences
peaks at 10.3 GiB, against 2.4 GiB with the places named. Here the reading names them, and the
kernel checks the named ones. The places follow `consItemsK c`'s order: a change of that order
asks for new places (each `consAtB` is then false where a place no longer holds the item), which
test/TieKimpHints.lean prints. -/

/-- A reading of a constructor sentence: its kind (`0` the `functional` or `subsort` sentence of a
generator, `1` the no-confusion sentence of one, `2` of two), the place of its sort in
`consSorts c`, the places of its generators among the sort's, and the places in `consItemsK c` of
the items it follows from (Cons-Fun of the first generator; Cons-Inj of it, or Cons-Fun of the
second; Cons-Dist of the two). -/
structure ConsHint where
  kind : Nat
  sort : Nat
  g : Nat
  g' : Nat
  k1 : Nat
  k2 : Nat
  k3 : Nat

/-- The item at place `k` of `consItemsK c0` has the pattern `φ`. -/
def consItemAt (c0 : Semantics) (k : Nat) (φ : KoreAML.P) : Bool :=
  match (consItemsK c0)[k]? with
  | some it => decide (it.pat = φ)
  | none => false

/-- The generator at place `i` among the sort N's. -/
def consGenAt (c0 : Semantics) (N : Srt) (i : Nat) : Option KoreAML.Gen := ((c0.gens N).map (Gen.toK c0))[i]?

/-- `tieFunB` with Γ's Cons-Fun item at place `k`. -/
def consFunAt (c0 : Semantics) (N : Srt) (g : KoreAML.Gen) (k : Nat) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .exist r val (.equals s r' (.var (.evar val')) body) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let ks := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    decide (s = KoreAML.srt (c0.sortName N)) && decide (r = KoreAML.R) && decide (r' = KoreAML.R) &&
    decide (val' = val) && decide (N < nRegSorts + c0.sortNames.length) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey) &&
    decide (val.sort = KoreAML.srt (c0.sortName N)) && decide (ks.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ body =
      KoreAML.Cons.genPat (c0.sortName N) g ((ks.map fun k => t.ev (KoreAML.evarKey k)).map .evar)) &&
    decide (t.ev (KoreAML.evarKey val) ∉ t.ev (.sortVar "R") :: ks.map fun k => t.ev (KoreAML.evarKey k)) &&
    consItemAt c0 k (KoreAML.Cons.funItem (c0.sortName N) g).pat
  | _ => false

/-- `tieInjB` with Γ's Cons-Fun and Cons-Inj items at places `k1`, `k2`. -/
def consInjAt (c0 : Semantics) (N : Srt) (g : KoreAML.Gen) (k1 k2 : Nat) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .implies s (.and s' [p1, p2]) q =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c0.sortName N)) && decide (s' = KoreAML.srt (c0.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c0.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c0.sortName N) g (iy.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ q = KoreAML.Cons.genPat (c0.sortName N) g
      ((ix.zip iy).map fun p => KoreAML.sAnd (.evar p.1) (.evar p.2))) &&
    consItemAt c0 k1 (KoreAML.Cons.funItem (c0.sortName N) g).pat &&
    consItemAt c0 k2 (KoreAML.Cons.injItem (c0.sortName N) g).pat
  | _ => false

/-- `tieDistB` with Γ's Cons-Fun items at places `k1`, `k2` and Cons-Dist item at `k3`. -/
def consDistAt (c0 : Semantics) (N : Srt) (g g' : KoreAML.Gen) (k1 k2 k3 : Nat) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .not s (.and s' [p1, p2]) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c0.sortName N)) && decide (s' = KoreAML.srt (c0.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g'.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c0.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c0.sortName N) g' (iy.map .evar)) &&
    consItemAt c0 k1 (KoreAML.Cons.funItem (c0.sortName N) g).pat &&
    consItemAt c0 k2 (KoreAML.Cons.funItem (c0.sortName N) g').pat &&
    consItemAt c0 k3 (KoreAML.Cons.distItem (c0.sortName N) g g').pat
  | _ => false

/-- The axiom is the constructor sentence the reading `h` names. -/
def consAtB (c0 : Semantics) (h : ConsHint) (a : Kore.Axiom) : Bool :=
  match (consSorts c0)[h.sort]? with
  | none => false
  | some N =>
    match consGenAt c0 N h.g, consGenAt c0 N h.g' with
    | some g, some g' =>
      (h.kind == 0 && consFunAt c0 N g h.k1 a) || (h.kind == 1 && consInjAt c0 N g h.k1 h.k2 a) ||
        (h.kind == 2 && consDistAt c0 N g g' h.k1 h.k2 h.k3 a)
    | _, _ => false

kernel_rfl consAtB_withHooks : ∀ (c0 : Semantics) (H : HookParams) (h : ConsHint) (a : Kore.Axiom),
  consAtB (c0.withHooks H) h a = consAtB c0 h a

/-- **A constructor sentence `consAtB` accepts is entailed by Γ.** -/
theorem consAt_entailed {c0 : Semantics} [OvlOK c0] {h : ConsHint} {a : Kore.Axiom}
    (hc : consAtB c0 h a = true) (i : Nat) (mod : String) :
    Γ c0 ⊧ (KoreAML.trAxiom [] [] ⟨i, mod, a⟩).pat := by
  intro M _ I hI
  have hD := defOK hI
  have hitem : ∀ {k : Nat} {φ : KoreAML.P}, consItemAt c0 k φ = true → I ⊧ᴵ φ := by
    intro k φ hk
    unfold consItemAt at hk
    split at hk
    · rename_i it hit
      exact sat_cons hI (Or.inl ⟨it, List.mem_of_getElem? hit, of_decide_eq_true hk⟩)
    · cases hk
  unfold consAtB at hc
  split at hc
  · cases hc
  · rename_i N _
    split at hc
    · rename_i g g' _ _
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
      rcases hc with (⟨-, hc⟩ | ⟨-, hc⟩) | ⟨-, hc⟩
      · unfold consFunAt at hc
        split at hc
        · rename_i r val s r' val' body hp
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hc
          subst h1 h2 h3 h4
          exact tieFun_entailed hI h5 (hitem h11) hp h6 h7 h8 h9 h10
        · cases hc
      · unfold consInjAt at hc
        split at hc
        · rename_i s s' p1 p2 q hp
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
          subst h1 h2
          exact tieInj_entailed hD (hitem h9) (hitem h10) hp h3 h4 h5 h6 h7 h8
        · cases hc
      · unfold consDistAt at hc
        split at hc
        · rename_i s s' p1 p2 hp
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
          subst h1 h2
          exact tieDist_entailed hD (hitem h8) (hitem h9) (.inl (hitem h10)) hp h3 h4 h5 h6 h7
        · cases hc
    · cases hc

/-! ## The 565 constructor sentences -/

/-- The sentences of the classes constructor functional, subsort, injectivity and distinctness, in
text order, each with its reading. -/
noncomputable def consPairs : List (AxiomDecl × ConsHint) :=
  [(U.ax4, ⟨0, 1, 43, 0, 48, 0, 0⟩), (U.ax5, ⟨0, 1, 37, 0, 42, 0, 0⟩), (U.ax6, ⟨0, 9, 1, 0, 1236, 0, 0⟩),
   (U.ax7, ⟨0, 1, 30, 0, 35, 0, 0⟩), (U.ax8, ⟨0, 1, 36, 0, 41, 0, 0⟩), (U.ax9, ⟨0, 1, 31, 0, 36, 0, 0⟩),
   (U.ax10, ⟨0, 1, 41, 0, 46, 0, 0⟩), (U.ax11, ⟨0, 1, 32, 0, 37, 0, 0⟩), (U.ax12, ⟨0, 1, 29, 0, 34, 0, 0⟩),
   (U.ax13, ⟨0, 1, 33, 0, 38, 0, 0⟩), (U.ax14, ⟨0, 1, 35, 0, 40, 0, 0⟩), (U.ax15, ⟨0, 1, 40, 0, 45, 0, 0⟩),
   (U.ax16, ⟨0, 1, 26, 0, 31, 0, 0⟩), (U.ax17, ⟨0, 1, 42, 0, 47, 0, 0⟩), (U.ax18, ⟨0, 1, 38, 0, 43, 0, 0⟩),
   (U.ax19, ⟨0, 1, 34, 0, 39, 0, 0⟩), (U.ax20, ⟨0, 1, 27, 0, 32, 0, 0⟩), (U.ax21, ⟨0, 3, 1, 0, 1031, 0, 0⟩),
   (U.ax22, ⟨0, 1, 39, 0, 44, 0, 0⟩), (U.ax23, ⟨0, 4, 17, 0, 1052, 0, 0⟩), (U.ax24, ⟨0, 1, 28, 0, 33, 0, 0⟩),
   (U.ax25, ⟨0, 12, 1, 0, 1284, 0, 0⟩), (U.ax26, ⟨0, 12, 0, 0, 1283, 0, 0⟩),
   (U.ax27, ⟨0, 4, 16, 0, 1051, 0, 0⟩), (U.ax28, ⟨0, 10, 2, 0, 1242, 0, 0⟩),
   (U.ax29, ⟨0, 4, 0, 0, 1035, 0, 0⟩), (U.ax30, ⟨1, 4, 0, 0, 1035, 1053, 0⟩),
   (U.ax31, ⟨2, 4, 0, 1, 1035, 1036, 1071⟩), (U.ax32, ⟨2, 4, 0, 2, 1035, 1037, 1072⟩),
   (U.ax33, ⟨2, 4, 0, 3, 1035, 1038, 1073⟩), (U.ax34, ⟨2, 4, 0, 4, 1035, 1039, 1074⟩),
   (U.ax35, ⟨2, 4, 0, 5, 1035, 1040, 1075⟩), (U.ax36, ⟨2, 4, 0, 6, 1035, 1041, 1076⟩),
   (U.ax37, ⟨2, 4, 0, 7, 1035, 1042, 1077⟩), (U.ax38, ⟨2, 4, 0, 8, 1035, 1043, 1078⟩),
   (U.ax39, ⟨2, 4, 0, 9, 1035, 1044, 1079⟩), (U.ax40, ⟨2, 4, 0, 10, 1035, 1045, 1080⟩),
   (U.ax41, ⟨2, 4, 0, 11, 1035, 1046, 1081⟩), (U.ax42, ⟨2, 4, 0, 12, 1035, 1047, 1082⟩),
   (U.ax43, ⟨2, 4, 0, 13, 1035, 1048, 1083⟩), (U.ax44, ⟨0, 1, 0, 0, 5, 0, 0⟩),
   (U.ax45, ⟨2, 1, 0, 1, 5, 6, 91⟩), (U.ax46, ⟨2, 1, 0, 2, 5, 7, 92⟩), (U.ax47, ⟨2, 1, 0, 3, 5, 8, 93⟩),
   (U.ax48, ⟨2, 1, 0, 4, 5, 9, 94⟩), (U.ax49, ⟨2, 1, 0, 5, 5, 10, 95⟩), (U.ax50, ⟨2, 1, 0, 6, 5, 11, 96⟩),
   (U.ax51, ⟨2, 1, 0, 7, 5, 12, 97⟩), (U.ax52, ⟨2, 1, 0, 8, 5, 13, 98⟩), (U.ax53, ⟨2, 1, 0, 9, 5, 14, 99⟩),
   (U.ax54, ⟨2, 1, 0, 10, 5, 15, 100⟩), (U.ax55, ⟨2, 1, 0, 11, 5, 16, 101⟩),
   (U.ax56, ⟨2, 1, 0, 12, 5, 17, 102⟩), (U.ax57, ⟨2, 1, 0, 13, 5, 18, 103⟩),
   (U.ax58, ⟨2, 1, 0, 14, 5, 19, 104⟩), (U.ax59, ⟨2, 1, 0, 15, 5, 20, 105⟩),
   (U.ax60, ⟨2, 1, 0, 16, 5, 21, 106⟩), (U.ax61, ⟨2, 1, 0, 17, 5, 22, 107⟩),
   (U.ax62, ⟨2, 1, 0, 18, 5, 23, 108⟩), (U.ax63, ⟨2, 1, 0, 19, 5, 24, 109⟩),
   (U.ax64, ⟨2, 1, 0, 20, 5, 25, 110⟩), (U.ax65, ⟨2, 1, 0, 21, 5, 26, 111⟩),
   (U.ax66, ⟨2, 1, 0, 22, 5, 27, 112⟩), (U.ax67, ⟨2, 1, 0, 23, 5, 28, 113⟩),
   (U.ax68, ⟨2, 1, 0, 24, 5, 29, 114⟩), (U.ax69, ⟨2, 1, 0, 25, 5, 30, 115⟩), (U.ax70, ⟨0, 1, 1, 0, 6, 0, 0⟩),
   (U.ax71, ⟨2, 1, 1, 2, 6, 7, 134⟩), (U.ax72, ⟨2, 1, 1, 3, 6, 8, 135⟩), (U.ax73, ⟨2, 1, 1, 4, 6, 9, 136⟩),
   (U.ax74, ⟨2, 1, 1, 5, 6, 10, 137⟩), (U.ax75, ⟨2, 1, 1, 6, 6, 11, 138⟩), (U.ax76, ⟨2, 1, 1, 7, 6, 12, 139⟩),
   (U.ax77, ⟨2, 1, 1, 8, 6, 13, 140⟩), (U.ax78, ⟨2, 1, 1, 9, 6, 14, 141⟩), (U.ax79, ⟨2, 1, 1, 10, 6, 15, 142⟩),
   (U.ax80, ⟨2, 1, 1, 11, 6, 16, 143⟩), (U.ax81, ⟨2, 1, 1, 12, 6, 17, 144⟩),
   (U.ax82, ⟨2, 1, 1, 13, 6, 18, 145⟩), (U.ax83, ⟨2, 1, 1, 14, 6, 19, 146⟩),
   (U.ax84, ⟨2, 1, 1, 15, 6, 20, 147⟩), (U.ax85, ⟨2, 1, 1, 16, 6, 21, 148⟩),
   (U.ax86, ⟨2, 1, 1, 17, 6, 22, 149⟩), (U.ax87, ⟨2, 1, 1, 18, 6, 23, 150⟩),
   (U.ax88, ⟨2, 1, 1, 19, 6, 24, 151⟩), (U.ax89, ⟨2, 1, 1, 20, 6, 25, 152⟩),
   (U.ax90, ⟨2, 1, 1, 21, 6, 26, 153⟩), (U.ax91, ⟨2, 1, 1, 22, 6, 27, 154⟩),
   (U.ax92, ⟨2, 1, 1, 23, 6, 28, 155⟩), (U.ax93, ⟨2, 1, 1, 24, 6, 29, 156⟩),
   (U.ax94, ⟨2, 1, 1, 25, 6, 30, 157⟩), (U.ax95, ⟨0, 1, 2, 0, 7, 0, 0⟩), (U.ax96, ⟨1, 1, 2, 0, 7, 49, 0⟩),
   (U.ax97, ⟨2, 1, 2, 3, 7, 8, 176⟩), (U.ax98, ⟨2, 1, 2, 4, 7, 9, 177⟩), (U.ax99, ⟨2, 1, 2, 5, 7, 10, 178⟩),
   (U.ax100, ⟨2, 1, 2, 6, 7, 11, 179⟩), (U.ax101, ⟨2, 1, 2, 7, 7, 12, 180⟩),
   (U.ax102, ⟨2, 1, 2, 8, 7, 13, 181⟩), (U.ax103, ⟨2, 1, 2, 9, 7, 14, 182⟩),
   (U.ax104, ⟨2, 1, 2, 10, 7, 15, 183⟩), (U.ax105, ⟨2, 1, 2, 11, 7, 16, 184⟩),
   (U.ax106, ⟨2, 1, 2, 12, 7, 17, 185⟩), (U.ax107, ⟨2, 1, 2, 13, 7, 18, 186⟩),
   (U.ax108, ⟨2, 1, 2, 14, 7, 19, 187⟩), (U.ax109, ⟨2, 1, 2, 15, 7, 20, 188⟩),
   (U.ax110, ⟨2, 1, 2, 16, 7, 21, 189⟩), (U.ax111, ⟨2, 1, 2, 17, 7, 22, 190⟩),
   (U.ax112, ⟨2, 1, 2, 18, 7, 23, 191⟩), (U.ax113, ⟨2, 1, 2, 19, 7, 24, 192⟩),
   (U.ax114, ⟨2, 1, 2, 20, 7, 25, 193⟩), (U.ax115, ⟨2, 1, 2, 21, 7, 26, 194⟩),
   (U.ax116, ⟨2, 1, 2, 22, 7, 27, 195⟩), (U.ax117, ⟨2, 1, 2, 23, 7, 28, 196⟩),
   (U.ax118, ⟨2, 1, 2, 24, 7, 29, 197⟩), (U.ax119, ⟨2, 1, 2, 25, 7, 30, 198⟩),
   (U.ax120, ⟨0, 1, 3, 0, 8, 0, 0⟩), (U.ax121, ⟨1, 1, 3, 0, 8, 50, 0⟩), (U.ax122, ⟨2, 1, 3, 4, 8, 9, 217⟩),
   (U.ax123, ⟨2, 1, 3, 5, 8, 10, 218⟩), (U.ax124, ⟨2, 1, 3, 6, 8, 11, 219⟩),
   (U.ax125, ⟨2, 1, 3, 7, 8, 12, 220⟩), (U.ax126, ⟨2, 1, 3, 8, 8, 13, 221⟩),
   (U.ax127, ⟨2, 1, 3, 9, 8, 14, 222⟩), (U.ax128, ⟨2, 1, 3, 10, 8, 15, 223⟩),
   (U.ax129, ⟨2, 1, 3, 11, 8, 16, 224⟩), (U.ax130, ⟨2, 1, 3, 12, 8, 17, 225⟩),
   (U.ax131, ⟨2, 1, 3, 13, 8, 18, 226⟩), (U.ax132, ⟨2, 1, 3, 14, 8, 19, 227⟩),
   (U.ax133, ⟨2, 1, 3, 15, 8, 20, 228⟩), (U.ax134, ⟨2, 1, 3, 16, 8, 21, 229⟩),
   (U.ax135, ⟨2, 1, 3, 17, 8, 22, 230⟩), (U.ax136, ⟨2, 1, 3, 18, 8, 23, 231⟩),
   (U.ax137, ⟨2, 1, 3, 19, 8, 24, 232⟩), (U.ax138, ⟨2, 1, 3, 20, 8, 25, 233⟩),
   (U.ax139, ⟨2, 1, 3, 21, 8, 26, 234⟩), (U.ax140, ⟨2, 1, 3, 22, 8, 27, 235⟩),
   (U.ax141, ⟨2, 1, 3, 23, 8, 28, 236⟩), (U.ax142, ⟨2, 1, 3, 24, 8, 29, 237⟩),
   (U.ax143, ⟨2, 1, 3, 25, 8, 30, 238⟩), (U.ax144, ⟨0, 1, 4, 0, 9, 0, 0⟩), (U.ax145, ⟨1, 1, 4, 0, 9, 51, 0⟩),
   (U.ax146, ⟨2, 1, 4, 5, 9, 10, 257⟩), (U.ax147, ⟨2, 1, 4, 6, 9, 11, 258⟩),
   (U.ax148, ⟨2, 1, 4, 7, 9, 12, 259⟩), (U.ax149, ⟨2, 1, 4, 8, 9, 13, 260⟩),
   (U.ax150, ⟨2, 1, 4, 9, 9, 14, 261⟩), (U.ax151, ⟨2, 1, 4, 10, 9, 15, 262⟩),
   (U.ax152, ⟨2, 1, 4, 11, 9, 16, 263⟩), (U.ax153, ⟨2, 1, 4, 12, 9, 17, 264⟩),
   (U.ax154, ⟨2, 1, 4, 13, 9, 18, 265⟩), (U.ax155, ⟨2, 1, 4, 14, 9, 19, 266⟩),
   (U.ax156, ⟨2, 1, 4, 15, 9, 20, 267⟩), (U.ax157, ⟨2, 1, 4, 16, 9, 21, 268⟩),
   (U.ax158, ⟨2, 1, 4, 17, 9, 22, 269⟩), (U.ax159, ⟨2, 1, 4, 18, 9, 23, 270⟩),
   (U.ax160, ⟨2, 1, 4, 19, 9, 24, 271⟩), (U.ax161, ⟨2, 1, 4, 20, 9, 25, 272⟩),
   (U.ax162, ⟨2, 1, 4, 21, 9, 26, 273⟩), (U.ax163, ⟨2, 1, 4, 22, 9, 27, 274⟩),
   (U.ax164, ⟨2, 1, 4, 23, 9, 28, 275⟩), (U.ax165, ⟨2, 1, 4, 24, 9, 29, 276⟩),
   (U.ax166, ⟨2, 1, 4, 25, 9, 30, 277⟩), (U.ax167, ⟨0, 1, 5, 0, 10, 0, 0⟩), (U.ax168, ⟨1, 1, 5, 0, 10, 52, 0⟩),
   (U.ax169, ⟨2, 1, 5, 6, 10, 11, 296⟩), (U.ax170, ⟨2, 1, 5, 7, 10, 12, 297⟩),
   (U.ax171, ⟨2, 1, 5, 8, 10, 13, 298⟩), (U.ax172, ⟨2, 1, 5, 9, 10, 14, 299⟩),
   (U.ax173, ⟨2, 1, 5, 10, 10, 15, 300⟩), (U.ax174, ⟨2, 1, 5, 11, 10, 16, 301⟩),
   (U.ax175, ⟨2, 1, 5, 12, 10, 17, 302⟩), (U.ax176, ⟨2, 1, 5, 13, 10, 18, 303⟩),
   (U.ax177, ⟨2, 1, 5, 14, 10, 19, 304⟩), (U.ax178, ⟨2, 1, 5, 15, 10, 20, 305⟩),
   (U.ax179, ⟨2, 1, 5, 16, 10, 21, 306⟩), (U.ax180, ⟨2, 1, 5, 17, 10, 22, 307⟩),
   (U.ax181, ⟨2, 1, 5, 18, 10, 23, 308⟩), (U.ax182, ⟨2, 1, 5, 19, 10, 24, 309⟩),
   (U.ax183, ⟨2, 1, 5, 20, 10, 25, 310⟩), (U.ax184, ⟨2, 1, 5, 21, 10, 26, 311⟩),
   (U.ax185, ⟨2, 1, 5, 22, 10, 27, 312⟩), (U.ax186, ⟨2, 1, 5, 23, 10, 28, 313⟩),
   (U.ax187, ⟨2, 1, 5, 24, 10, 29, 314⟩), (U.ax188, ⟨2, 1, 5, 25, 10, 30, 315⟩),
   (U.ax189, ⟨0, 1, 6, 0, 11, 0, 0⟩), (U.ax190, ⟨1, 1, 6, 0, 11, 53, 0⟩), (U.ax191, ⟨2, 1, 6, 7, 11, 12, 334⟩),
   (U.ax192, ⟨2, 1, 6, 8, 11, 13, 335⟩), (U.ax193, ⟨2, 1, 6, 9, 11, 14, 336⟩),
   (U.ax194, ⟨2, 1, 6, 10, 11, 15, 337⟩), (U.ax195, ⟨2, 1, 6, 11, 11, 16, 338⟩),
   (U.ax196, ⟨2, 1, 6, 12, 11, 17, 339⟩), (U.ax197, ⟨2, 1, 6, 13, 11, 18, 340⟩),
   (U.ax198, ⟨2, 1, 6, 14, 11, 19, 341⟩), (U.ax199, ⟨2, 1, 6, 15, 11, 20, 342⟩),
   (U.ax200, ⟨2, 1, 6, 16, 11, 21, 343⟩), (U.ax201, ⟨2, 1, 6, 17, 11, 22, 344⟩),
   (U.ax202, ⟨2, 1, 6, 18, 11, 23, 345⟩), (U.ax203, ⟨2, 1, 6, 19, 11, 24, 346⟩),
   (U.ax204, ⟨2, 1, 6, 20, 11, 25, 347⟩), (U.ax205, ⟨2, 1, 6, 21, 11, 26, 348⟩),
   (U.ax206, ⟨2, 1, 6, 22, 11, 27, 349⟩), (U.ax207, ⟨2, 1, 6, 23, 11, 28, 350⟩),
   (U.ax208, ⟨2, 1, 6, 24, 11, 29, 351⟩), (U.ax209, ⟨2, 1, 6, 25, 11, 30, 352⟩),
   (U.ax210, ⟨0, 1, 7, 0, 12, 0, 0⟩), (U.ax211, ⟨1, 1, 7, 0, 12, 54, 0⟩), (U.ax212, ⟨2, 1, 7, 8, 12, 13, 371⟩),
   (U.ax213, ⟨2, 1, 7, 9, 12, 14, 372⟩), (U.ax214, ⟨2, 1, 7, 10, 12, 15, 373⟩),
   (U.ax215, ⟨2, 1, 7, 11, 12, 16, 374⟩), (U.ax216, ⟨2, 1, 7, 12, 12, 17, 375⟩),
   (U.ax217, ⟨2, 1, 7, 13, 12, 18, 376⟩), (U.ax218, ⟨2, 1, 7, 14, 12, 19, 377⟩),
   (U.ax219, ⟨2, 1, 7, 15, 12, 20, 378⟩), (U.ax220, ⟨2, 1, 7, 16, 12, 21, 379⟩),
   (U.ax221, ⟨2, 1, 7, 17, 12, 22, 380⟩), (U.ax222, ⟨2, 1, 7, 18, 12, 23, 381⟩),
   (U.ax223, ⟨2, 1, 7, 19, 12, 24, 382⟩), (U.ax224, ⟨2, 1, 7, 20, 12, 25, 383⟩),
   (U.ax225, ⟨2, 1, 7, 21, 12, 26, 384⟩), (U.ax226, ⟨2, 1, 7, 22, 12, 27, 385⟩),
   (U.ax227, ⟨2, 1, 7, 23, 12, 28, 386⟩), (U.ax228, ⟨2, 1, 7, 24, 12, 29, 387⟩),
   (U.ax229, ⟨2, 1, 7, 25, 12, 30, 388⟩), (U.ax230, ⟨0, 1, 8, 0, 13, 0, 0⟩),
   (U.ax231, ⟨1, 1, 8, 0, 13, 55, 0⟩), (U.ax232, ⟨2, 1, 8, 9, 13, 14, 407⟩),
   (U.ax233, ⟨2, 1, 8, 10, 13, 15, 408⟩), (U.ax234, ⟨2, 1, 8, 11, 13, 16, 409⟩),
   (U.ax235, ⟨2, 1, 8, 12, 13, 17, 410⟩), (U.ax236, ⟨2, 1, 8, 13, 13, 18, 411⟩),
   (U.ax237, ⟨2, 1, 8, 14, 13, 19, 412⟩), (U.ax238, ⟨2, 1, 8, 15, 13, 20, 413⟩),
   (U.ax239, ⟨2, 1, 8, 16, 13, 21, 414⟩), (U.ax240, ⟨2, 1, 8, 17, 13, 22, 415⟩),
   (U.ax241, ⟨2, 1, 8, 18, 13, 23, 416⟩), (U.ax242, ⟨2, 1, 8, 19, 13, 24, 417⟩),
   (U.ax243, ⟨2, 1, 8, 20, 13, 25, 418⟩), (U.ax244, ⟨2, 1, 8, 21, 13, 26, 419⟩),
   (U.ax245, ⟨2, 1, 8, 22, 13, 27, 420⟩), (U.ax246, ⟨2, 1, 8, 23, 13, 28, 421⟩),
   (U.ax247, ⟨2, 1, 8, 24, 13, 29, 422⟩), (U.ax248, ⟨2, 1, 8, 25, 13, 30, 423⟩),
   (U.ax249, ⟨0, 1, 9, 0, 14, 0, 0⟩), (U.ax250, ⟨1, 1, 9, 0, 14, 56, 0⟩),
   (U.ax251, ⟨2, 1, 9, 10, 14, 15, 442⟩), (U.ax252, ⟨2, 1, 9, 11, 14, 16, 443⟩),
   (U.ax253, ⟨2, 1, 9, 12, 14, 17, 444⟩), (U.ax254, ⟨2, 1, 9, 13, 14, 18, 445⟩),
   (U.ax255, ⟨2, 1, 9, 14, 14, 19, 446⟩), (U.ax256, ⟨2, 1, 9, 15, 14, 20, 447⟩),
   (U.ax257, ⟨2, 1, 9, 16, 14, 21, 448⟩), (U.ax258, ⟨2, 1, 9, 17, 14, 22, 449⟩),
   (U.ax259, ⟨2, 1, 9, 18, 14, 23, 450⟩), (U.ax260, ⟨2, 1, 9, 19, 14, 24, 451⟩),
   (U.ax261, ⟨2, 1, 9, 20, 14, 25, 452⟩), (U.ax262, ⟨2, 1, 9, 21, 14, 26, 453⟩),
   (U.ax263, ⟨2, 1, 9, 22, 14, 27, 454⟩), (U.ax264, ⟨2, 1, 9, 23, 14, 28, 455⟩),
   (U.ax265, ⟨2, 1, 9, 24, 14, 29, 456⟩), (U.ax266, ⟨2, 1, 9, 25, 14, 30, 457⟩),
   (U.ax267, ⟨0, 1, 10, 0, 15, 0, 0⟩), (U.ax268, ⟨1, 1, 10, 0, 15, 57, 0⟩),
   (U.ax269, ⟨2, 1, 10, 11, 15, 16, 476⟩), (U.ax270, ⟨2, 1, 10, 12, 15, 17, 477⟩),
   (U.ax271, ⟨2, 1, 10, 13, 15, 18, 478⟩), (U.ax272, ⟨2, 1, 10, 14, 15, 19, 479⟩),
   (U.ax273, ⟨2, 1, 10, 15, 15, 20, 480⟩), (U.ax274, ⟨2, 1, 10, 16, 15, 21, 481⟩),
   (U.ax275, ⟨2, 1, 10, 17, 15, 22, 482⟩), (U.ax276, ⟨2, 1, 10, 18, 15, 23, 483⟩),
   (U.ax277, ⟨2, 1, 10, 19, 15, 24, 484⟩), (U.ax278, ⟨2, 1, 10, 20, 15, 25, 485⟩),
   (U.ax279, ⟨2, 1, 10, 21, 15, 26, 486⟩), (U.ax280, ⟨2, 1, 10, 22, 15, 27, 487⟩),
   (U.ax281, ⟨2, 1, 10, 23, 15, 28, 488⟩), (U.ax282, ⟨2, 1, 10, 24, 15, 29, 489⟩),
   (U.ax283, ⟨2, 1, 10, 25, 15, 30, 490⟩), (U.ax284, ⟨0, 1, 11, 0, 16, 0, 0⟩),
   (U.ax285, ⟨1, 1, 11, 0, 16, 58, 0⟩), (U.ax286, ⟨2, 1, 11, 12, 16, 17, 509⟩),
   (U.ax287, ⟨2, 1, 11, 13, 16, 18, 510⟩), (U.ax288, ⟨2, 1, 11, 14, 16, 19, 511⟩),
   (U.ax289, ⟨2, 1, 11, 15, 16, 20, 512⟩), (U.ax290, ⟨2, 1, 11, 16, 16, 21, 513⟩),
   (U.ax291, ⟨2, 1, 11, 17, 16, 22, 514⟩), (U.ax292, ⟨2, 1, 11, 18, 16, 23, 515⟩),
   (U.ax293, ⟨2, 1, 11, 19, 16, 24, 516⟩), (U.ax294, ⟨2, 1, 11, 20, 16, 25, 517⟩),
   (U.ax295, ⟨2, 1, 11, 21, 16, 26, 518⟩), (U.ax296, ⟨2, 1, 11, 22, 16, 27, 519⟩),
   (U.ax297, ⟨2, 1, 11, 23, 16, 28, 520⟩), (U.ax298, ⟨2, 1, 11, 24, 16, 29, 521⟩),
   (U.ax299, ⟨2, 1, 11, 25, 16, 30, 522⟩), (U.ax300, ⟨0, 1, 12, 0, 17, 0, 0⟩),
   (U.ax301, ⟨1, 1, 12, 0, 17, 59, 0⟩), (U.ax302, ⟨2, 1, 12, 13, 17, 18, 541⟩),
   (U.ax303, ⟨2, 1, 12, 14, 17, 19, 542⟩), (U.ax304, ⟨2, 1, 12, 15, 17, 20, 543⟩),
   (U.ax305, ⟨2, 1, 12, 16, 17, 21, 544⟩), (U.ax306, ⟨2, 1, 12, 17, 17, 22, 545⟩),
   (U.ax307, ⟨2, 1, 12, 18, 17, 23, 546⟩), (U.ax308, ⟨2, 1, 12, 19, 17, 24, 547⟩),
   (U.ax309, ⟨2, 1, 12, 20, 17, 25, 548⟩), (U.ax310, ⟨2, 1, 12, 21, 17, 26, 549⟩),
   (U.ax311, ⟨2, 1, 12, 22, 17, 27, 550⟩), (U.ax312, ⟨2, 1, 12, 23, 17, 28, 551⟩),
   (U.ax313, ⟨2, 1, 12, 24, 17, 29, 552⟩), (U.ax314, ⟨2, 1, 12, 25, 17, 30, 553⟩),
   (U.ax315, ⟨0, 1, 13, 0, 18, 0, 0⟩), (U.ax316, ⟨1, 1, 13, 0, 18, 60, 0⟩),
   (U.ax317, ⟨2, 1, 13, 14, 18, 19, 572⟩), (U.ax318, ⟨2, 1, 13, 15, 18, 20, 573⟩),
   (U.ax319, ⟨2, 1, 13, 16, 18, 21, 574⟩), (U.ax320, ⟨2, 1, 13, 17, 18, 22, 575⟩),
   (U.ax321, ⟨2, 1, 13, 18, 18, 23, 576⟩), (U.ax322, ⟨2, 1, 13, 19, 18, 24, 577⟩),
   (U.ax323, ⟨2, 1, 13, 20, 18, 25, 578⟩), (U.ax324, ⟨2, 1, 13, 21, 18, 26, 579⟩),
   (U.ax325, ⟨2, 1, 13, 22, 18, 27, 580⟩), (U.ax326, ⟨2, 1, 13, 23, 18, 28, 581⟩),
   (U.ax327, ⟨2, 1, 13, 24, 18, 29, 582⟩), (U.ax328, ⟨2, 1, 13, 25, 18, 30, 583⟩),
   (U.ax329, ⟨0, 1, 14, 0, 19, 0, 0⟩), (U.ax330, ⟨1, 1, 14, 0, 19, 61, 0⟩),
   (U.ax331, ⟨2, 1, 14, 15, 19, 20, 602⟩), (U.ax332, ⟨2, 1, 14, 16, 19, 21, 603⟩),
   (U.ax333, ⟨2, 1, 14, 17, 19, 22, 604⟩), (U.ax334, ⟨2, 1, 14, 18, 19, 23, 605⟩),
   (U.ax335, ⟨2, 1, 14, 19, 19, 24, 606⟩), (U.ax336, ⟨2, 1, 14, 20, 19, 25, 607⟩),
   (U.ax337, ⟨2, 1, 14, 21, 19, 26, 608⟩), (U.ax338, ⟨2, 1, 14, 22, 19, 27, 609⟩),
   (U.ax339, ⟨2, 1, 14, 23, 19, 28, 610⟩), (U.ax340, ⟨2, 1, 14, 24, 19, 29, 611⟩),
   (U.ax341, ⟨2, 1, 14, 25, 19, 30, 612⟩), (U.ax342, ⟨0, 1, 15, 0, 20, 0, 0⟩),
   (U.ax343, ⟨1, 1, 15, 0, 20, 62, 0⟩), (U.ax344, ⟨2, 1, 15, 16, 20, 21, 631⟩),
   (U.ax345, ⟨2, 1, 15, 17, 20, 22, 632⟩), (U.ax346, ⟨2, 1, 15, 18, 20, 23, 633⟩),
   (U.ax347, ⟨2, 1, 15, 19, 20, 24, 634⟩), (U.ax348, ⟨2, 1, 15, 20, 20, 25, 635⟩),
   (U.ax349, ⟨2, 1, 15, 21, 20, 26, 636⟩), (U.ax350, ⟨2, 1, 15, 22, 20, 27, 637⟩),
   (U.ax351, ⟨2, 1, 15, 23, 20, 28, 638⟩), (U.ax352, ⟨2, 1, 15, 24, 20, 29, 639⟩),
   (U.ax353, ⟨2, 1, 15, 25, 20, 30, 640⟩), (U.ax354, ⟨0, 1, 16, 0, 21, 0, 0⟩),
   (U.ax355, ⟨1, 1, 16, 0, 21, 63, 0⟩), (U.ax356, ⟨2, 1, 16, 17, 21, 22, 659⟩),
   (U.ax357, ⟨2, 1, 16, 18, 21, 23, 660⟩), (U.ax358, ⟨2, 1, 16, 19, 21, 24, 661⟩),
   (U.ax359, ⟨2, 1, 16, 20, 21, 25, 662⟩), (U.ax360, ⟨2, 1, 16, 21, 21, 26, 663⟩),
   (U.ax361, ⟨2, 1, 16, 22, 21, 27, 664⟩), (U.ax362, ⟨2, 1, 16, 23, 21, 28, 665⟩),
   (U.ax363, ⟨2, 1, 16, 24, 21, 29, 666⟩), (U.ax364, ⟨2, 1, 16, 25, 21, 30, 667⟩),
   (U.ax365, ⟨0, 1, 17, 0, 22, 0, 0⟩), (U.ax366, ⟨1, 1, 17, 0, 22, 64, 0⟩),
   (U.ax367, ⟨2, 1, 17, 18, 22, 23, 686⟩), (U.ax368, ⟨2, 1, 17, 19, 22, 24, 687⟩),
   (U.ax369, ⟨2, 1, 17, 20, 22, 25, 688⟩), (U.ax370, ⟨2, 1, 17, 21, 22, 26, 689⟩),
   (U.ax371, ⟨2, 1, 17, 22, 22, 27, 690⟩), (U.ax372, ⟨2, 1, 17, 23, 22, 28, 691⟩),
   (U.ax373, ⟨2, 1, 17, 24, 22, 29, 692⟩), (U.ax374, ⟨2, 1, 17, 25, 22, 30, 693⟩),
   (U.ax375, ⟨0, 1, 18, 0, 23, 0, 0⟩), (U.ax376, ⟨1, 1, 18, 0, 23, 65, 0⟩),
   (U.ax377, ⟨2, 1, 18, 19, 23, 24, 712⟩), (U.ax378, ⟨2, 1, 18, 20, 23, 25, 713⟩),
   (U.ax379, ⟨2, 1, 18, 21, 23, 26, 714⟩), (U.ax380, ⟨2, 1, 18, 22, 23, 27, 715⟩),
   (U.ax381, ⟨2, 1, 18, 23, 23, 28, 716⟩), (U.ax382, ⟨2, 1, 18, 24, 23, 29, 717⟩),
   (U.ax383, ⟨2, 1, 18, 25, 23, 30, 718⟩), (U.ax384, ⟨0, 1, 19, 0, 24, 0, 0⟩),
   (U.ax385, ⟨1, 1, 19, 0, 24, 66, 0⟩), (U.ax386, ⟨2, 1, 19, 20, 24, 25, 737⟩),
   (U.ax387, ⟨2, 1, 19, 21, 24, 26, 738⟩), (U.ax388, ⟨2, 1, 19, 22, 24, 27, 739⟩),
   (U.ax389, ⟨2, 1, 19, 23, 24, 28, 740⟩), (U.ax390, ⟨2, 1, 19, 24, 24, 29, 741⟩),
   (U.ax391, ⟨2, 1, 19, 25, 24, 30, 742⟩), (U.ax392, ⟨0, 1, 20, 0, 25, 0, 0⟩),
   (U.ax393, ⟨1, 1, 20, 0, 25, 67, 0⟩), (U.ax394, ⟨2, 1, 20, 21, 25, 26, 761⟩),
   (U.ax395, ⟨2, 1, 20, 22, 25, 27, 762⟩), (U.ax396, ⟨2, 1, 20, 23, 25, 28, 763⟩),
   (U.ax397, ⟨2, 1, 20, 24, 25, 29, 764⟩), (U.ax398, ⟨2, 1, 20, 25, 25, 30, 765⟩),
   (U.ax399, ⟨0, 1, 21, 0, 26, 0, 0⟩), (U.ax400, ⟨1, 1, 21, 0, 26, 68, 0⟩),
   (U.ax401, ⟨2, 1, 21, 22, 26, 27, 784⟩), (U.ax402, ⟨2, 1, 21, 23, 26, 28, 785⟩),
   (U.ax403, ⟨2, 1, 21, 24, 26, 29, 786⟩), (U.ax404, ⟨2, 1, 21, 25, 26, 30, 787⟩),
   (U.ax405, ⟨0, 1, 22, 0, 27, 0, 0⟩), (U.ax406, ⟨1, 1, 22, 0, 27, 69, 0⟩),
   (U.ax407, ⟨2, 1, 22, 23, 27, 28, 806⟩), (U.ax408, ⟨2, 1, 22, 24, 27, 29, 807⟩),
   (U.ax409, ⟨2, 1, 22, 25, 27, 30, 808⟩), (U.ax410, ⟨0, 1, 23, 0, 28, 0, 0⟩),
   (U.ax411, ⟨1, 1, 23, 0, 28, 70, 0⟩), (U.ax412, ⟨2, 1, 23, 24, 28, 29, 827⟩),
   (U.ax413, ⟨2, 1, 23, 25, 28, 30, 828⟩), (U.ax414, ⟨0, 1, 24, 0, 29, 0, 0⟩),
   (U.ax415, ⟨1, 1, 24, 0, 29, 71, 0⟩), (U.ax416, ⟨2, 1, 24, 25, 29, 30, 847⟩),
   (U.ax417, ⟨0, 1, 25, 0, 30, 0, 0⟩), (U.ax418, ⟨1, 1, 25, 0, 30, 72, 0⟩),
   (U.ax419, ⟨0, 4, 1, 0, 1036, 0, 0⟩), (U.ax420, ⟨1, 4, 1, 0, 1036, 1054, 0⟩),
   (U.ax421, ⟨2, 4, 1, 2, 1036, 1037, 1088⟩), (U.ax422, ⟨2, 4, 1, 3, 1036, 1038, 1089⟩),
   (U.ax423, ⟨2, 4, 1, 4, 1036, 1039, 1090⟩), (U.ax424, ⟨2, 4, 1, 5, 1036, 1040, 1091⟩),
   (U.ax425, ⟨2, 4, 1, 6, 1036, 1041, 1092⟩), (U.ax426, ⟨2, 4, 1, 7, 1036, 1042, 1093⟩),
   (U.ax427, ⟨2, 4, 1, 8, 1036, 1043, 1094⟩), (U.ax428, ⟨2, 4, 1, 9, 1036, 1044, 1095⟩),
   (U.ax429, ⟨2, 4, 1, 10, 1036, 1045, 1096⟩), (U.ax430, ⟨2, 4, 1, 11, 1036, 1046, 1097⟩),
   (U.ax431, ⟨2, 4, 1, 12, 1036, 1047, 1098⟩), (U.ax432, ⟨2, 4, 1, 13, 1036, 1048, 1099⟩),
   (U.ax436, ⟨0, 2, 0, 0, 1027, 0, 0⟩), (U.ax437, ⟨1, 2, 0, 0, 1027, 1028, 0⟩),
   (U.ax438, ⟨0, 5, 0, 0, 1223, 0, 0⟩), (U.ax439, ⟨1, 5, 0, 0, 1223, 1224, 0⟩),
   (U.ax440, ⟨0, 6, 0, 0, 1226, 0, 0⟩), (U.ax441, ⟨1, 6, 0, 0, 1226, 1227, 0⟩),
   (U.ax442, ⟨0, 7, 0, 0, 1229, 0, 0⟩), (U.ax443, ⟨1, 7, 0, 0, 1229, 1230, 0⟩),
   (U.ax444, ⟨0, 8, 0, 0, 1232, 0, 0⟩), (U.ax445, ⟨1, 8, 0, 0, 1232, 1233, 0⟩),
   (U.ax452, ⟨0, 4, 2, 0, 1037, 0, 0⟩), (U.ax453, ⟨1, 4, 2, 0, 1037, 1055, 0⟩),
   (U.ax454, ⟨2, 4, 2, 3, 1037, 1038, 1104⟩), (U.ax455, ⟨2, 4, 2, 4, 1037, 1039, 1105⟩),
   (U.ax456, ⟨2, 4, 2, 5, 1037, 1040, 1106⟩), (U.ax457, ⟨2, 4, 2, 6, 1037, 1041, 1107⟩),
   (U.ax458, ⟨2, 4, 2, 7, 1037, 1042, 1108⟩), (U.ax459, ⟨2, 4, 2, 8, 1037, 1043, 1109⟩),
   (U.ax460, ⟨2, 4, 2, 9, 1037, 1044, 1110⟩), (U.ax461, ⟨2, 4, 2, 10, 1037, 1045, 1111⟩),
   (U.ax462, ⟨2, 4, 2, 11, 1037, 1046, 1112⟩), (U.ax463, ⟨2, 4, 2, 12, 1037, 1047, 1113⟩),
   (U.ax464, ⟨2, 4, 2, 13, 1037, 1048, 1114⟩), (U.ax465, ⟨0, 4, 3, 0, 1038, 0, 0⟩),
   (U.ax466, ⟨1, 4, 3, 0, 1038, 1056, 0⟩), (U.ax467, ⟨2, 4, 3, 4, 1038, 1039, 1119⟩),
   (U.ax468, ⟨2, 4, 3, 5, 1038, 1040, 1120⟩), (U.ax469, ⟨2, 4, 3, 6, 1038, 1041, 1121⟩),
   (U.ax470, ⟨2, 4, 3, 7, 1038, 1042, 1122⟩), (U.ax471, ⟨2, 4, 3, 8, 1038, 1043, 1123⟩),
   (U.ax472, ⟨2, 4, 3, 9, 1038, 1044, 1124⟩), (U.ax473, ⟨2, 4, 3, 10, 1038, 1045, 1125⟩),
   (U.ax474, ⟨2, 4, 3, 11, 1038, 1046, 1126⟩), (U.ax475, ⟨2, 4, 3, 12, 1038, 1047, 1127⟩),
   (U.ax476, ⟨2, 4, 3, 13, 1038, 1048, 1128⟩), (U.ax479, ⟨0, 4, 4, 0, 1039, 0, 0⟩),
   (U.ax480, ⟨1, 4, 4, 0, 1039, 1057, 0⟩), (U.ax481, ⟨2, 4, 4, 5, 1039, 1040, 1133⟩),
   (U.ax482, ⟨2, 4, 4, 6, 1039, 1041, 1134⟩), (U.ax483, ⟨2, 4, 4, 7, 1039, 1042, 1135⟩),
   (U.ax484, ⟨2, 4, 4, 8, 1039, 1043, 1136⟩), (U.ax485, ⟨2, 4, 4, 9, 1039, 1044, 1137⟩),
   (U.ax486, ⟨2, 4, 4, 10, 1039, 1045, 1138⟩), (U.ax487, ⟨2, 4, 4, 11, 1039, 1046, 1139⟩),
   (U.ax488, ⟨2, 4, 4, 12, 1039, 1047, 1140⟩), (U.ax489, ⟨2, 4, 4, 13, 1039, 1048, 1141⟩),
   (U.ax491, ⟨0, 4, 5, 0, 1040, 0, 0⟩), (U.ax492, ⟨1, 4, 5, 0, 1040, 1058, 0⟩),
   (U.ax493, ⟨2, 4, 5, 6, 1040, 1041, 1146⟩), (U.ax494, ⟨2, 4, 5, 7, 1040, 1042, 1147⟩),
   (U.ax495, ⟨2, 4, 5, 8, 1040, 1043, 1148⟩), (U.ax496, ⟨2, 4, 5, 9, 1040, 1044, 1149⟩),
   (U.ax497, ⟨2, 4, 5, 10, 1040, 1045, 1150⟩), (U.ax498, ⟨2, 4, 5, 11, 1040, 1046, 1151⟩),
   (U.ax499, ⟨2, 4, 5, 12, 1040, 1047, 1152⟩), (U.ax500, ⟨2, 4, 5, 13, 1040, 1048, 1153⟩),
   (U.ax503, ⟨0, 4, 6, 0, 1041, 0, 0⟩), (U.ax504, ⟨1, 4, 6, 0, 1041, 1059, 0⟩),
   (U.ax505, ⟨2, 4, 6, 7, 1041, 1042, 1158⟩), (U.ax506, ⟨2, 4, 6, 8, 1041, 1043, 1159⟩),
   (U.ax507, ⟨2, 4, 6, 9, 1041, 1044, 1160⟩), (U.ax508, ⟨2, 4, 6, 10, 1041, 1045, 1161⟩),
   (U.ax509, ⟨2, 4, 6, 11, 1041, 1046, 1162⟩), (U.ax510, ⟨2, 4, 6, 12, 1041, 1047, 1163⟩),
   (U.ax511, ⟨2, 4, 6, 13, 1041, 1048, 1164⟩), (U.ax512, ⟨0, 4, 7, 0, 1042, 0, 0⟩),
   (U.ax513, ⟨1, 4, 7, 0, 1042, 1060, 0⟩), (U.ax514, ⟨2, 4, 7, 8, 1042, 1043, 1169⟩),
   (U.ax515, ⟨2, 4, 7, 9, 1042, 1044, 1170⟩), (U.ax516, ⟨2, 4, 7, 10, 1042, 1045, 1171⟩),
   (U.ax517, ⟨2, 4, 7, 11, 1042, 1046, 1172⟩), (U.ax518, ⟨2, 4, 7, 12, 1042, 1047, 1173⟩),
   (U.ax519, ⟨2, 4, 7, 13, 1042, 1048, 1174⟩), (U.ax523, ⟨0, 4, 8, 0, 1043, 0, 0⟩),
   (U.ax524, ⟨1, 4, 8, 0, 1043, 1061, 0⟩), (U.ax525, ⟨2, 4, 8, 9, 1043, 1044, 1179⟩),
   (U.ax526, ⟨2, 4, 8, 10, 1043, 1045, 1180⟩), (U.ax527, ⟨2, 4, 8, 11, 1043, 1046, 1181⟩),
   (U.ax528, ⟨2, 4, 8, 12, 1043, 1047, 1182⟩), (U.ax529, ⟨2, 4, 8, 13, 1043, 1048, 1183⟩),
   (U.ax531, ⟨0, 4, 9, 0, 1044, 0, 0⟩), (U.ax532, ⟨1, 4, 9, 0, 1044, 1062, 0⟩),
   (U.ax533, ⟨2, 4, 9, 10, 1044, 1045, 1188⟩), (U.ax534, ⟨2, 4, 9, 11, 1044, 1046, 1189⟩),
   (U.ax535, ⟨2, 4, 9, 12, 1044, 1047, 1190⟩), (U.ax536, ⟨2, 4, 9, 13, 1044, 1048, 1191⟩),
   (U.ax543, ⟨0, 4, 10, 0, 1045, 0, 0⟩), (U.ax544, ⟨1, 4, 10, 0, 1045, 1063, 0⟩),
   (U.ax545, ⟨2, 4, 10, 11, 1045, 1046, 1196⟩), (U.ax546, ⟨2, 4, 10, 12, 1045, 1047, 1197⟩),
   (U.ax547, ⟨2, 4, 10, 13, 1045, 1048, 1198⟩), (U.ax548, ⟨0, 11, 0, 0, 1248, 0, 0⟩),
   (U.ax549, ⟨1, 11, 0, 0, 1248, 1255, 0⟩), (U.ax550, ⟨2, 11, 0, 1, 1248, 1249, 1261⟩),
   (U.ax551, ⟨2, 11, 0, 2, 1248, 1250, 1262⟩), (U.ax552, ⟨2, 11, 0, 3, 1248, 1251, 1263⟩),
   (U.ax553, ⟨2, 11, 0, 4, 1248, 1252, 1264⟩), (U.ax554, ⟨2, 11, 0, 5, 1248, 1253, 1265⟩),
   (U.ax555, ⟨2, 11, 0, 6, 1248, 1254, 1266⟩), (U.ax557, ⟨0, 4, 11, 0, 1046, 0, 0⟩),
   (U.ax558, ⟨1, 4, 11, 0, 1046, 1064, 0⟩), (U.ax559, ⟨2, 4, 11, 12, 1046, 1047, 1203⟩),
   (U.ax560, ⟨2, 4, 11, 13, 1046, 1048, 1204⟩), (U.ax562, ⟨0, 4, 12, 0, 1047, 0, 0⟩),
   (U.ax563, ⟨1, 4, 12, 0, 1047, 1065, 0⟩), (U.ax564, ⟨2, 4, 12, 13, 1047, 1048, 1209⟩),
   (U.ax577, ⟨0, 11, 1, 0, 1249, 0, 0⟩), (U.ax578, ⟨1, 11, 1, 0, 1249, 1256, 0⟩),
   (U.ax579, ⟨2, 11, 1, 2, 1249, 1250, 1267⟩), (U.ax580, ⟨2, 11, 1, 3, 1249, 1251, 1268⟩),
   (U.ax581, ⟨2, 11, 1, 4, 1249, 1252, 1269⟩), (U.ax582, ⟨2, 11, 1, 5, 1249, 1253, 1270⟩),
   (U.ax583, ⟨2, 11, 1, 6, 1249, 1254, 1271⟩), (U.ax596, ⟨0, 4, 13, 0, 1048, 0, 0⟩),
   (U.ax597, ⟨1, 4, 13, 0, 1048, 1066, 0⟩), (U.ax600, ⟨0, 11, 2, 0, 1250, 0, 0⟩),
   (U.ax601, ⟨1, 11, 2, 0, 1250, 1257, 0⟩), (U.ax602, ⟨2, 11, 2, 3, 1250, 1251, 1272⟩),
   (U.ax603, ⟨2, 11, 2, 4, 1250, 1252, 1273⟩), (U.ax604, ⟨2, 11, 2, 5, 1250, 1253, 1274⟩),
   (U.ax605, ⟨2, 11, 2, 6, 1250, 1254, 1275⟩), (U.ax606, ⟨0, 11, 3, 0, 1251, 0, 0⟩),
   (U.ax607, ⟨1, 11, 3, 0, 1251, 1258, 0⟩), (U.ax608, ⟨2, 11, 3, 4, 1251, 1252, 1276⟩),
   (U.ax609, ⟨2, 11, 3, 5, 1251, 1253, 1277⟩), (U.ax610, ⟨2, 11, 3, 6, 1251, 1254, 1278⟩),
   (U.ax637, ⟨0, 3, 0, 0, 1030, 0, 0⟩), (U.ax638, ⟨0, 9, 0, 0, 1235, 0, 0⟩),
   (U.ax646, ⟨0, 11, 4, 0, 1252, 0, 0⟩), (U.ax647, ⟨1, 11, 4, 0, 1252, 1259, 0⟩),
   (U.ax648, ⟨2, 11, 4, 5, 1252, 1253, 1279⟩), (U.ax649, ⟨2, 11, 4, 6, 1252, 1254, 1280⟩),
   (U.ax650, ⟨0, 11, 5, 0, 1253, 0, 0⟩), (U.ax651, ⟨1, 11, 5, 0, 1253, 1260, 0⟩),
   (U.ax652, ⟨2, 11, 5, 6, 1253, 1254, 1281⟩), (U.ax653, ⟨0, 11, 6, 0, 1254, 0, 0⟩)]

/-- The sentences of the four classes, in text order. -/
noncomputable def consText : List AxiomDecl := consPairs.map (·.1)

/-- The sentence is the constructor sentence its reading names, and its translation with the
text's declarations is its translation with none. -/
noncomputable def consPairB (p : AxiomDecl × ConsHint) : Bool :=
  decide ((trS p.1).pat = (trAxiom [] [] p.1).pat) && consAtB c p.2 p.1.ax

theorem cons_0 : ((consPairs.drop 0).take 100).all consPairB = true := by decide +kernel
theorem cons_100 : ((consPairs.drop 100).take 100).all consPairB = true := by decide +kernel
theorem cons_200 : ((consPairs.drop 200).take 100).all consPairB = true := by decide +kernel
theorem cons_300 : ((consPairs.drop 300).take 100).all consPairB = true := by decide +kernel
theorem cons_400 : ((consPairs.drop 400).take 100).all consPairB = true := by decide +kernel
theorem cons_500 : (consPairs.drop 500).all consPairB = true := by decide +kernel

theorem cons_checked : consPairs.all consPairB = true :=
  tieAll_whole (p := consPairB) <|
    tieAll_range (a := 0) (n := 100) cons_0 <|
    tieAll_range (a := 100) (n := 100) cons_100 <|
    tieAll_range (a := 200) (n := 100) cons_200 <|
    tieAll_range (a := 300) (n := 100) cons_300 <|
    tieAll_range (a := 400) (n := 100) cons_400 <|
    cons_500

/-- **E for the constructor sentences**: Γ entails each of the 565, for every H. -/
theorem cons_entailed (H : HookParams) : ∀ ad ∈ consText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp had
  have h := List.all_eq_true.mp cons_checked p hp
  simp only [consPairB, Bool.and_eq_true] at h
  rw [of_decide_eq_true h.1]
  intro M _ I hI
  exact consAt_entailed (c0 := cH H) ((consAtB_withHooks c H p.2 p.1.ax).trans h.2) p.1.index p.1.module hI

/-- The account's classes constructor functional, subsort, injectivity and distinctness (as
test/TieKimp.lean's `classes` lists them). -/
def consClasses : List (String × List Nat) :=
  [("constructor functional",
    [29, 44, 70, 95, 120, 144, 167, 189, 210, 230, 249, 267, 284, 300, 315, 329, 342, 354, 365, 375, 384, 392,
     399, 405, 410, 414, 417, 419, 436, 438, 440, 442, 444, 452, 465, 479, 491, 503, 512, 523, 531, 543, 548,
     557, 562, 577, 596, 600, 606, 637, 638, 646, 650, 653]),
   ("subsort",
    [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]),
   ("injectivity",
    [30, 96, 121, 145, 168, 190, 211, 231, 250, 268, 285, 301, 316, 330, 343, 355, 366, 376, 385, 393, 400,
     406, 411, 415, 418, 420, 437, 439, 441, 443, 445, 453, 466, 480, 492, 504, 513, 524, 532, 544, 549, 558,
     563, 578, 597, 601, 607, 647, 651]),
   ("distinctness",
    [31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
     58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84,
     85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
     110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132,
     133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155,
     156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
     179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201,
     202, 203, 204, 205, 206, 207, 208, 209, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224,
     225, 226, 227, 228, 229, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247,
     248, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 269, 270, 271, 272,
     273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295,
     296, 297, 298, 299, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 317, 318, 319, 320,
     321, 322, 323, 324, 325, 326, 327, 328, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 344, 345,
     346, 347, 348, 349, 350, 351, 352, 353, 356, 357, 358, 359, 360, 361, 362, 363, 364, 367, 368, 369, 370,
     371, 372, 373, 374, 377, 378, 379, 380, 381, 382, 383, 386, 387, 388, 389, 390, 391, 394, 395, 396, 397,
     398, 401, 402, 403, 404, 407, 408, 409, 412, 413, 416, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430,
     431, 432, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 467, 468, 469, 470, 471, 472, 473, 474,
     475, 476, 481, 482, 483, 484, 485, 486, 487, 488, 489, 493, 494, 495, 496, 497, 498, 499, 500, 505, 506,
     507, 508, 509, 510, 511, 514, 515, 516, 517, 518, 519, 525, 526, 527, 528, 529, 533, 534, 535, 536, 545,
     546, 547, 550, 551, 552, 553, 554, 555, 559, 560, 564, 579, 580, 581, 582, 583, 602, 603, 604, 605, 608,
     609, 610, 648, 649, 652])]

/-- **`consText` is the four classes**: the same indices, each once. -/
theorem cons_account : (consClasses.flatMap (·.2)).isPerm (consText.map (·.index)) = true := by decide +kernel

/-- The class sizes, and the kind of reading of each class's sentences: a `functional` or `subsort`
sentence of a generator (0), a no-confusion sentence of one generator (1), of two (2). -/
theorem cons_kinds : consClasses.map (fun cl => (cl.1, cl.2.length,
    ((consPairs.filter fun p => cl.2.contains p.1.index).map (·.2.kind)).eraseDups)) =
    [("constructor functional", 54, [0]), ("subsort", 25, [0]), ("injectivity", 49, [1]),
     ("distinctness", 437, [2])] := by decide +kernel

/-! ## No junk (16 sentences, 655 to 670) -/

/-- `\or{S}(\top{S}(), \bottom{S}())` as an axiom: `⊤ ⇒ (⊤_S ∨ ⊥_S ≡ ⟦S⟧)`. -/
def orTopBot (S : P) : P := conjList [] ⇒ (sOr S (sTop S) (sBot S) ≡ inhOf S)

theorem orTopBot_valid {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {S : P}
    (hS : S.isFreeEvar topVar = false) : I ⊧ᴵ orTopBot S := by
  intro e m
  unfold orTopBot
  rw [interpret_impl]
  intro _
  rw [interp_equal hD]
  intro a
  rw [interp_sOr, interp_sTop hD hS]
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩

theorem nj655 : (trS U.ax655).pat = orTopBot (sym (.sort "SortBool")) := by decide +kernel
theorem nj662 : (trS U.ax662).pat = orTopBot (sym (.sort "SortId")) := by decide +kernel
theorem nj663 : (trS U.ax663).pat = orTopBot (sym (.sort "SortInt")) := by decide +kernel
theorem nj666 : (trS U.ax666).pat = orTopBot (sym (.sort "SortKConfigVar")) := by decide +kernel

/-- **E for 655, 662, 663, 666** (Bool, Id, Int, KConfigVar): entailed by Γ (by any theory with
definedness), for every H. -/
theorem nojunk_trivial_entailed (H : HookParams) :
    ∀ ad ∈ [U.ax655, U.ax662, U.ax663, U.ax666], Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had M _ I hI
  have hD := defOK hI
  simp only [List.mem_cons, List.not_mem_nil, or_false] at had
  rcases had with rfl | rfl | rfl | rfl
  · rw [nj655]; exact orTopBot_valid hD rfl
  · rw [nj662]; exact orTopBot_valid hD rfl
  · rw [nj663]; exact orTopBot_valid hD rfl
  · rw [nj666]; exact orTopBot_valid hD rfl

/-- The other twelve, each with its sort. -/
noncomputable def njPairs : List (AxiomDecl × Srt) :=
  [(U.ax656, 32), (U.ax657, 33), (U.ax658, 34), (U.ax659, 19), (U.ax660, 17), (U.ax661, 18), (U.ax664, 30),
   (U.ax665, 31), (U.ax667, 1), (U.ax668, 35), (U.ax669, 36), (U.ax670, 37)]

theorem nj_sorts : njPairs.map (fun p => c.sortName p.2) = ["EnvCell", "EnvCellOpt", "Expr", "GeneratedCounterCell",
    "GeneratedTopCell", "GeneratedTopCellFragment", "KCell", "KCellOpt", "KItem", "KResult", "Stmt", "Value"] := by
  decide +kernel

/-- The sentence is the no-junk item of a constructor sort with generators over its generators in
the text's order (`gensInOrder`), which are the sort's generators (`Semantics.gens`) in some order. -/
noncomputable def njB (p : AxiomDecl × Srt) : Bool :=
  decide (p.2 ∈ consSorts c) && decide ((c.gens p.2).isEmpty = false) &&
  decide ((trS p.1).pat =
    (KoreAML.Cons.noJunkItem (c.sortName p.2) ((gensInOrder c defn.pres p.2).map (Gen.toK c))).pat) &&
  ((gensInOrder c defn.pres p.2).map (Gen.toK c)).isPerm ((c.gens p.2).map (Gen.toK c))

theorem nj_checked : njPairs.all njB = true := by decide +kernel

/-- **Ten are Γ's item**: the translation of the sentence is Γ's no-junk item of its sort, pattern
for pattern. -/
theorem nojunk_items : ∀ p ∈ njPairs.filter (fun p => p.2 != 34 && p.2 != 1),
    (trS p.1).pat = (KoreAML.Cons.noJunkItem (c.sortName p.2) ((c.gens p.2).map (Gen.toK c))).pat := by
  have h : ((njPairs.filter (fun p => p.2 != 34 && p.2 != 1)).all fun p => decide ((trS p.1).pat =
      (KoreAML.Cons.noJunkItem (c.sortName p.2) ((c.gens p.2).map (Gen.toK c))).pat)) = true := by decide +kernel
  exact fun p hp => of_decide_eq_true (List.all_eq_true.mp h p hp)

/-- **Expr's (658) and KItem's (667) are not**: the text lists their generators in another order
than `Semantics.gens`. -/
theorem nojunk_order : ∀ p ∈ [(U.ax658, (34 : Srt)), (U.ax667, 1)],
    (trS p.1).pat ≠ (KoreAML.Cons.noJunkItem (c.sortName p.2) ((c.gens p.2).map (Gen.toK c))).pat := by
  have h : ([(U.ax658, (34 : Srt)), (U.ax667, 1)].all fun p => decide ((trS p.1).pat ≠
      (KoreAML.Cons.noJunkItem (c.sortName p.2) ((c.gens p.2).map (Gen.toK c))).pat)) = true := by decide +kernel
  exact fun p hp => of_decide_eq_true (List.all_eq_true.mp h p hp)

/-- **E for the twelve**: Γ entails each, for every H. Γ's no-junk item of the sort is the sentence
over the same generators, in the same order or another; a no-junk item entails the one over any
list that holds its generators (`noJunkItem_of_subset`). -/
theorem nojunk_gens_entailed (H : HookParams) : ∀ p ∈ njPairs, Γ (cH H) ⊧ (trS p.1).pat := by
  intro p hp M _ I hI
  have h := List.all_eq_true.mp nj_checked p hp
  simp only [njB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hN, hne⟩, heq⟩, hperm⟩ := h
  rw [heq]
  refine noJunkItem_of_subset (defOK hI) (gs := (c.gens p.2).map (Gen.toK c))
    (fun g hg => (List.isPerm_iff.mp hperm).mem_iff.mpr hg) ?_
  exact sat_cons hI (Or.inl ⟨_, noJunkItem_mem (c := cH H) (N := p.2) hN hne, rfl⟩)

/-- The 16 no-junk sentences: the four without generators, then the twelve. -/
noncomputable def njText : List AxiomDecl := [U.ax655, U.ax662, U.ax663, U.ax666] ++ njPairs.map (·.1)

/-- They are the account's no-junk class, 655 to 670, each once. -/
theorem nojunk_account : (njText.map (·.index)).isPerm (List.range' 655 16) = true := by decide +kernel

/-- **E for the no-junk sentences**: Γ entails each of the 16, for every H. -/
theorem nojunk_entailed (H : HookParams) : ∀ ad ∈ njText, Γ (cH H) ⊧ (trS ad).pat := by
  intro ad had
  rcases List.mem_append.mp had with h | h
  · exact nojunk_trivial_entailed H ad h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact nojunk_gens_entailed H p hp

end KCore.TieKimp

#check @KCore.TieKimp.cons_entailed
#check @KCore.TieKimp.nojunk_entailed
#print axioms KCore.TieKimp.cons_entailed
#print axioms KCore.TieKimp.cons_account
#print axioms KCore.TieKimp.cons_kinds
#print axioms KCore.TieKimp.nojunk_entailed
