/-
  The mirrors of kore.k's sorts (`KCore.KK.T`, `D`, `St`, KKStatements.lean) as values of kore.k's
  semantics read from its kompiled text: one kore.k constructor per mirror constructor, each at the
  symbol number the reader gives its production (`emb_names` states each number's KORE name, so a
  wrong number fails the kernel check). `emb` writes a term of sort `Term`, `embTs` a `Ts`, `embK` a
  `Kind`, `embS` a `Subs`, `embCls` a `Clauses`, `embFns` a `Fns`, `embRls` a `Rules`, `embD` a
  `Def` and `embSt` a `Step`.

  Each embedding is a value of its kore.k sort at `c₀` (the `_c₀` lemmas below; at `KCore.KK.K₀
  KCore.KK.sig`, which is `c₀`, in User.Sig), and `emb`, `embTs` and `embSt` are injective: two
  different mirror constructors have different symbol numbers, and the arguments are kept.
-/
import User.KkKit
import User.KkFacts

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK

/-! ## The embeddings -/

/-- kore.k's `Kind`: `map`, `set`, `list`. -/
def embK : Kind → GroundTerm
  | .map => .ctor 429 []
  | .set => .ctor 438 []
  | .list => .ctor 427 []

mutual
/-- A mirror term as a kore.k value of sort `Term`. -/
def emb : T → GroundTerm
  | .ap f as => .ctor 408 [.dv 3 (.int f), embTs as]
  | .iv i => .ctor 425 [.dv 3 (.int i)]
  | .bv b => .ctor 413 [.dv 2 (.bool b)]
  | .tk s x => .ctor 443 [.dv 3 (.int s), .dv 10 (.tok x)]
  | .ij a b t => .ctor 424 [.dv 3 (.int a), .dv 3 (.int b), emb t]
  | .vr i => .ctor 445 [.dv 3 (.int i)]
  | .as p i => .ctor 409 [emb p, .dv 3 (.int i)]
  | .hk o as => .ctor 423 [.dv 3 (.int o), embTs as]
  | .bot => .ctor 412 []
  | .cb k c ps => .ctor 414 [embK k, .dv 3 (.int c), embTs ps]
  | .co k c es => .ctor 416 [embK k, .dv 3 (.int c), embTs es]
  | .en t e => .ctor 420 [emb t, emb e]
  | .kv a v => .ctor 426 [emb a, emb v]
  | .el x => .ctor 419 [emb x]
  termination_by structural t => t
/-- Mirror terms as a kore.k `Ts`: `.Ts` and `T ; Ts`. -/
def embTs : List T → GroundTerm
  | [] => .ctor 406 []
  | t :: ts => .ctor 407 [emb t, embTs ts]
  termination_by structural ts => ts
end

/-- The subsort table as a kore.k `Subs`: `.Subs` and `sub(A, B, S)`. -/
def embS : List (Int × Int) → GroundTerm
  | [] => .ctor 405 []
  | (a, b) :: r => .ctor 442 [.dv 3 (.int a), .dv 3 (.int b), embS r]

/-- A clause before the clauses `r`: `cl(P, O, Pats, Req, Rhs, R)`. -/
def embCl (cl : Cl) (r : GroundTerm) : GroundTerm :=
  .ctor 415 [.dv 3 (.int cl.prio), .dv 2 (.bool cl.owise), embTs cl.pats, emb cl.req, emb cl.rhs, r]

/-- Clauses as a kore.k `Clauses`: `.Cls` and `cl(…)`. -/
def embCls : List Cl → GroundTerm
  | [] => .ctor 401 []
  | cl :: r => embCl cl (embCls r)

/-- Functions with their clauses as a kore.k `Fns`: `.Fns` and `fn(G, Cs, Fs)`. -/
def embFns : List (Int × List Cl) → GroundTerm
  | [] => .ctor 402 []
  | (g, cs) :: r => .ctor 421 [.dv 3 (.int g), embCls cs, embFns r]

/-- A rule before the rules `r`: `rl(P, O, Lhs, Req, Rhs, R)`. -/
def embRl (rl : Rl) (r : GroundTerm) : GroundTerm :=
  .ctor 436 [.dv 3 (.int rl.prio), .dv 2 (.bool rl.owise), emb rl.lhs, emb rl.req, emb rl.rhs, r]

/-- Rules as a kore.k `Rules`: `.Rules` and `rl(…)`. -/
def embRls : List Rl → GroundTerm
  | [] => .ctor 404 []
  | rl :: r => embRl rl (embRls r)

/-- A mirror definition as a kore.k `Def`: `def(Subs, Fns, Rules)`. -/
def embD (E : D) : GroundTerm := .ctor 417 [embS E.subs, embFns E.fns, embRls E.rules]

/-- A mirror step result as a kore.k `Step`: `stuck` and `next(Ts)`. -/
def embSt : St → GroundTerm
  | .stuck => .ctor 441 []
  | .next ss => .ctor 430 [embTs ss]

/-! ## The symbol numbers are the productions' -/

/-- Each symbol number the embeddings use has the KORE name of the production the embedding
writes. -/
theorem emb_names :
    RefKk.defn.sem.symName 401 = "Lbl'Stop'Cls'Unds'KORE-SYNTAX'Unds'Clauses" ∧
    RefKk.defn.sem.symName 402 = "Lbl'Stop'Fns'Unds'KORE-SYNTAX'Unds'Fns" ∧
    RefKk.defn.sem.symName 404 = "Lbl'Stop'Rules'Unds'KORE-SYNTAX'Unds'Rules" ∧
    RefKk.defn.sem.symName 405 = "Lbl'Stop'Subs'Unds'KORE-SYNTAX'Unds'Subs" ∧
    RefKk.defn.sem.symName 406 = "Lbl'Stop'Ts'Unds'KORE-SYNTAX'Unds'Ts" ∧
    RefKk.defn.sem.symName 407 = "Lbl'UndsSClnUndsUnds'KORE-SYNTAX'Unds'Ts'Unds'Term'Unds'Ts" ∧
    RefKk.defn.sem.symName 408 = "Lblap'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 409 = "Lblas'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term'Unds'Int" ∧
    RefKk.defn.sem.symName 412 = "Lblbot'Unds'KORE-SYNTAX'Unds'Term" ∧
    RefKk.defn.sem.symName 413 = "Lblbv'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Bool" ∧
    RefKk.defn.sem.symName 414 = "Lblcb'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Kind'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 415 = "Lblcl'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Clauses'Unds'Int'Unds'Bool'Unds'Ts'Unds'Term'Unds'Term'Unds'Clauses" ∧
    RefKk.defn.sem.symName 416 = "Lblco'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Kind'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 417 = "Lbldef'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Def'Unds'Subs'Unds'Fns'Unds'Rules" ∧
    RefKk.defn.sem.symName 419 = "Lblel'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 420 = "Lblen'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 421 = "Lblfn'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Fns'Unds'Int'Unds'Clauses'Unds'Fns" ∧
    RefKk.defn.sem.symName 423 = "Lblhk'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Ts" ∧
    RefKk.defn.sem.symName 424 = "Lblij'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'Int'Unds'Term" ∧
    RefKk.defn.sem.symName 425 = "Lbliv'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int" ∧
    RefKk.defn.sem.symName 426 = "Lblkv'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Term'Unds'Term" ∧
    RefKk.defn.sem.symName 427 = "Lbllist'Unds'KORE-SYNTAX'Unds'Kind" ∧
    RefKk.defn.sem.symName 429 = "Lblmap'Unds'KORE-SYNTAX'Unds'Kind" ∧
    RefKk.defn.sem.symName 430 = "Lblnext'LParUndsRParUnds'KORE'Unds'Step'Unds'Ts" ∧
    RefKk.defn.sem.symName 436 = "Lblrl'LParUndsCommUndsCommUndsCommUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Rules'Unds'Int'Unds'Bool'Unds'Term'Unds'Term'Unds'Term'Unds'Rules" ∧
    RefKk.defn.sem.symName 438 = "Lblset'Unds'KORE-SYNTAX'Unds'Kind" ∧
    RefKk.defn.sem.symName 441 = "Lblstuck'Unds'KORE'Unds'Step" ∧
    RefKk.defn.sem.symName 442 = "Lblsub'LParUndsCommUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Subs'Unds'Int'Unds'Int'Unds'Subs" ∧
    RefKk.defn.sem.symName 443 = "Lbltk'LParUndsCommUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int'Unds'String" ∧
    RefKk.defn.sem.symName 445 = "Lblvr'LParUndsRParUnds'KORE-SYNTAX'Unds'Term'Unds'Int" := by
  decide +kernel

/-! ## The list embeddings through the kit's -/

theorem embTs_eq : ∀ ts : List T, embTs ts = _root_.KK.Kit.tsOf (ts.map emb)
  | [] => by rw [embTs]; rfl
  | t :: ts => by rw [embTs, embTs_eq ts]; rfl

theorem embFns_eq : ∀ fs : List (Int × List Cl),
    embFns fs = _root_.KK.Kit.fnsOf (fs.map fun p => (p.1, embCls p.2))
  | [] => rfl
  | (g, cs) :: fs => by rw [embFns, embFns_eq fs]; rfl

/-! ## Sorts at `c₀` -/

section Sorts
open _root_.KK _root_.KK.Kit _root_.KK.Facts

theorem sort_string_kemb (x : String) : c₀.sortOf (.dv 10 (.tok x)) = some 10 := by
  have h : (c₀.lib.carrier 10 == Srt.string) = true := by decide +kernel
  have h' : dvOK c₀.lib 10 (.tok x) = true := by simp only [dvOK, h, Bool.or_true, Bool.true_or]
  simp [Semantics.sortOf, h']

theorem embK_sorted_c₀ (k : Kind) : c₀.sortOf (embK k) = some 34 := by
  cases k
  · exact sort_ctor sig_429 sorts_nil
  · exact sort_ctor sig_438 sorts_nil
  · exact sort_ctor sig_427 sorts_nil

theorem embTs_sorted_of_kemb {ts : List T} (h : ∀ t ∈ ts, c₀.sortOf (emb t) = some 33) :
    c₀.sortOf (embTs ts) = some 43 := by
  rw [embTs_eq]
  exact sort_ts fun u hu => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
    exact h t ht

theorem emb_sorted_c₀ (t : T) : c₀.sortOf (emb t) = some 33 := by
  induction t using tInd_kkc with
  | hap f as ih =>
    rw [emb]; exact sort_ctor sig_408 (sorts_cons (sort_int f) (sorts_cons (embTs_sorted_of_kemb ih) sorts_nil))
  | hiv i => rw [emb]; exact sort_ctor sig_425 (sorts_cons (sort_int i) sorts_nil)
  | hbv b => rw [emb]; exact sort_ctor sig_413 (sorts_cons (sort_bool b) sorts_nil)
  | htk s x =>
    rw [emb]; exact sort_ctor sig_443 (sorts_cons (sort_int s) (sorts_cons (sort_string_kemb x) sorts_nil))
  | hij a b t ih =>
    rw [emb]
    exact sort_ctor sig_424 (sorts_cons (sort_int a) (sorts_cons (sort_int b) (sorts_cons ih sorts_nil)))
  | hvr i => rw [emb]; exact sort_ctor sig_445 (sorts_cons (sort_int i) sorts_nil)
  | has p i ih => rw [emb]; exact sort_ctor sig_409 (sorts_cons ih (sorts_cons (sort_int i) sorts_nil))
  | hhk o as ih =>
    rw [emb]; exact sort_ctor sig_423 (sorts_cons (sort_int o) (sorts_cons (embTs_sorted_of_kemb ih) sorts_nil))
  | hbot => rw [emb]; exact sort_ctor sig_412 sorts_nil
  | hcb k c ps ih =>
    rw [emb]
    exact sort_ctor sig_414 (sorts_cons (embK_sorted_c₀ k) (sorts_cons (sort_int c)
      (sorts_cons (embTs_sorted_of_kemb ih) sorts_nil)))
  | hco k c es ih =>
    rw [emb]
    exact sort_ctor sig_416 (sorts_cons (embK_sorted_c₀ k) (sorts_cons (sort_int c)
      (sorts_cons (embTs_sorted_of_kemb ih) sorts_nil)))
  | hen t e iht ihe => rw [emb]; exact sort_ctor sig_420 (sorts_cons iht (sorts_cons ihe sorts_nil))
  | hkv a v iha ihv => rw [emb]; exact sort_ctor sig_426 (sorts_cons iha (sorts_cons ihv sorts_nil))
  | hel x ih => rw [emb]; exact sort_ctor sig_419 (sorts_cons ih sorts_nil)

theorem embTs_sorted_c₀ (ts : List T) : c₀.sortOf (embTs ts) = some 43 :=
  embTs_sorted_of_kemb fun t _ => emb_sorted_c₀ t

theorem embS_sorted_c₀ : ∀ s : List (Int × Int), c₀.sortOf (embS s) = some 32
  | [] => sort_ctor sig_405 sorts_nil
  | (a, b) :: r =>
    sort_ctor sig_442 (sorts_cons (sort_int a) (sorts_cons (sort_int b) (sorts_cons (embS_sorted_c₀ r) sorts_nil)))

theorem embCls_sorted_c₀ : ∀ cs : List Cl, c₀.sortOf (embCls cs) = some 35
  | [] => sort_ctor sig_401 sorts_nil
  | cl :: r =>
    sort_ctor sig_415 (sorts_cons (sort_int cl.prio) (sorts_cons (sort_bool cl.owise)
      (sorts_cons (embTs_sorted_c₀ cl.pats) (sorts_cons (emb_sorted_c₀ cl.req)
        (sorts_cons (emb_sorted_c₀ cl.rhs) (sorts_cons (embCls_sorted_c₀ r) sorts_nil))))))

theorem embFns_sorted_c₀ : ∀ fs : List (Int × List Cl), c₀.sortOf (embFns fs) = some 39
  | [] => sort_ctor sig_402 sorts_nil
  | (g, cs) :: r =>
    sort_ctor sig_421 (sorts_cons (sort_int g) (sorts_cons (embCls_sorted_c₀ cs)
      (sorts_cons (embFns_sorted_c₀ r) sorts_nil)))

theorem embRls_sorted_c₀ : ∀ rs : List Rl, c₀.sortOf (embRls rs) = some 42
  | [] => sort_ctor sig_404 sorts_nil
  | rl :: r =>
    sort_ctor sig_436 (sorts_cons (sort_int rl.prio) (sorts_cons (sort_bool rl.owise)
      (sorts_cons (emb_sorted_c₀ rl.lhs) (sorts_cons (emb_sorted_c₀ rl.req)
        (sorts_cons (emb_sorted_c₀ rl.rhs) (sorts_cons (embRls_sorted_c₀ r) sorts_nil))))))

theorem embD_sorted_c₀ (E : D) : c₀.sortOf (embD E) = some 45 :=
  sort_ctor sig_417 (sorts_cons (embS_sorted_c₀ E.subs) (sorts_cons (embFns_sorted_c₀ E.fns)
    (sorts_cons (embRls_sorted_c₀ E.rules) sorts_nil)))

theorem embSt_sorted_c₀ (s : St) : c₀.sortOf (embSt s) = some 38 := by
  cases s with
  | stuck => exact sort_ctor sig_441 sorts_nil
  | next ss => exact sort_ctor sig_430 (sorts_cons (embTs_sorted_c₀ ss) sorts_nil)

end Sorts

/-! ## Injectivity -/

theorem embK_injective : Function.Injective embK := by
  intro k k' h; cases k <;> cases k' <;> first | rfl | (simp [embK] at h)

theorem embTs_inj_of_kemb {ts : List T} (h : ∀ t ∈ ts, ∀ u, emb t = emb u → t = u) :
    ∀ us, embTs ts = embTs us → ts = us := by
  induction ts with
  | nil => intro us hu; cases us with
    | nil => rfl
    | cons u us => rw [embTs, embTs] at hu; simp at hu
  | cons t ts ih =>
    intro us hu
    cases us with
    | nil => rw [embTs, embTs] at hu; simp at hu
    | cons u us =>
      rw [embTs, embTs] at hu
      simp only [GroundTerm.ctor.injEq, List.cons.injEq, true_and, and_true] at hu
      rw [h t (List.mem_cons_self ..) u hu.1, ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) us hu.2]

/-- Takes apart an equation `h` between two constructor terms: where the heads differ the goal is
closed, where they agree `h` becomes the equations of the arguments. -/
local macro "parts_kemb " h:ident : tactic =>
  `(tactic| (simp only [GroundTerm.ctor.injEq, List.cons.injEq, GroundTerm.dv.injEq, Lit.int.injEq,
      Lit.bool.injEq, Lit.tok.injEq, eq_self_iff_true, and_true, true_and] at $h:ident <;>
    try exact absurd ($h).1 (by decide)))

theorem emb_injective : Function.Injective emb := by
  intro t
  induction t using tInd_kkc with
  | hap f as ih =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨rfl, h⟩ := hu; rw [embTs_inj_of_kemb ih _ h]
  | hiv i => intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu; rw [hu]
  | hbv b => intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu; rw [hu]
  | htk s x =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨rfl, rfl⟩ := hu; rfl
  | hij a b t ih =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨rfl, rfl, h⟩ := hu; rw [ih h]
  | hvr i => intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu; rw [hu]
  | has p i ih =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨h, rfl⟩ := hu; rw [ih h]
  | hhk o as ih =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨rfl, h⟩ := hu; rw [embTs_inj_of_kemb ih _ h]
  | hbot => intro u hu; cases u <;> first | rfl | (rw [emb, emb] at hu; parts_kemb hu)
  | hcb k c ps ih =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨hk, rfl, h⟩ := hu; rw [embK_injective hk, embTs_inj_of_kemb ih _ h]
  | hco k c es ih =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨hk, rfl, h⟩ := hu; rw [embK_injective hk, embTs_inj_of_kemb ih _ h]
  | hen t e iht ihe =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨h1, h2⟩ := hu; rw [iht h1, ihe h2]
  | hkv a v iha ihv =>
    intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu
    obtain ⟨h1, h2⟩ := hu; rw [iha h1, ihv h2]
  | hel x ih => intro u hu; cases u <;> rw [emb, emb] at hu <;> parts_kemb hu; rw [ih hu]

theorem embTs_injective : Function.Injective embTs :=
  fun _ us h => embTs_inj_of_kemb (fun t _ u => @emb_injective t u) us h

theorem embSt_injective : Function.Injective embSt := by
  intro s s' h
  cases s <;> cases s' <;> simp [embSt] at h
  · rfl
  · rw [embTs_injective h]

end KCore.KK
