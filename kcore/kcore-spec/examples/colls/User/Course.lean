/-
  The first cell map: `colls`'s `bump` rule (rule 3) on a configuration whose `<accts>` cell holds
  two accounts, `1 ↦ <acct> <id> 1 </id> <bal> 5 </bal> </acct>` and `2 ↦ … <bal> 7 …`.
  Its left side's collection pattern `AcctCellMapItem(<id> I, <acct> <id> I <bal> B) Rest` denotes
  that map under I = 1, B = 5, Rest = the map of account 2 (`PatVal.coll`: the cell map's element
  and concatenation are parameters implemented by the map's, so the pattern denotes the union of
  the entry with Rest); and the rule steps the configuration to the one with account 1's balance 6.
-/
import Colls

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Colls.Course

open KCore Colls

def int (n : Int) : GroundTerm := .dv KCore.Srt.int (.int n)
def idc (n : Int) : GroundTerm := .ctor Sym.«<id>» [int n]
def acct (n b : Int) : GroundTerm := .ctor Sym.«<acct>» [idc n, .ctor Sym.«<bal>» [int b]]

/-- A map of accounts, each keyed by its `<id>` cell. -/
def accts (es : List (Int × Int)) : GroundTerm := .map Srt.«AcctCellMap» (es.map fun (n, b) => (idc n, acct n b))

def stack : GroundTerm := .ctor Sym.«<stack>» [.list KCore.Srt.list []]
def sum : GroundTerm := .ctor Sym.«<sum>» [int 0]
def counter : GroundTerm := .ctor KCore.counterLabel [int 0]

/-- The configuration: `bump(1)` at the head of the k cell, two accounts. -/
def start : GroundTerm :=
  .ctor KCore.topLabel [.ctor Sym.«<k>» [.ctor KCore.kseq [.inj Srt.«Op» KCore.Srt.kitem (.ctor Sym.«bump» [int 1]),
    .ctor KCore.dotk []]], stack, sum, .ctor Sym.«<accts>» [accts [(1, 5), (2, 7)]], counter]

/-- After the step: the k cell empty, account 1's balance 6. -/
def final : GroundTerm :=
  .ctor KCore.topLabel [.ctor Sym.«<k>» [.ctor KCore.dotk []], stack, sum,
    .ctor Sym.«<accts>» [accts [(1, 6), (2, 7)]], counter]

/-- `bump`'s left side: I is variable 0, the k cell's rest 1, the stack and sum cells 2 and 3, B 4,
the rest of the account map 5, the counter 6. -/
def lhs : Term :=
  .app KCore.topLabel [.app Sym.«<k>» [.app KCore.kseq [.inj Srt.«Op» KCore.Srt.kitem (.app Sym.«bump» [.var 0]), .var 1]],
    .var 2, .var 3,
    .app Sym.«<accts>» [.app Sym.«_AcctCellMap_» [.app Sym.«AcctCellMapItem» [.app Sym.«<id>» [.var 0],
      .app Sym.«<acct>» [.app Sym.«<id>» [.var 0], .app Sym.«<bal>» [.var 4]]], .var 5]], .var 6]

def rhs : Term :=
  .app KCore.topLabel [.app Sym.«<k>» [.var 1], .var 2, .var 3,
    .app Sym.«<accts>» [.app Sym.«_AcctCellMap_» [.app Sym.«AcctCellMapItem» [.app Sym.«<id>» [.var 0],
      .app Sym.«<acct>» [.app Sym.«<id>» [.var 0], .app Sym.«<bal>» [.app KCore.intAdd [.var 4, .dv KCore.Srt.int (.int 1)]]]],
      .var 5]], .var 6]

def bump : Rule :=
  { vars := [KCore.Srt.int, KCore.Srt.k, Srt.«StackCell», Srt.«SumCell», KCore.Srt.int, Srt.«AcctCellMap», KCore.Srt.counter],
    lhs := lhs, req := none, rhs := rhs, ens := none, prio := 50 }

/-- `bump` is rule 3. -/
theorem rule3 : c.rules[3]? = some bump := by kernel_rfl

/-- The match: I = 1, B = 5, Rest = the map of account 2. -/
def σ : Subst := [(0, int 1), (1, .ctor KCore.dotk []), (2, stack), (3, sum), (4, int 5), (5, accts [(2, 7)]), (6, counter)]

theorem idp : PatVal c σ (.app Sym.«<id>» [.var 0]) (idc 1) :=
  .ctor (by decide +kernel) (.cons (.var rfl) .nil)

theorem acctp : PatVal c σ (.app Sym.«<acct>» [.app Sym.«<id>» [.var 0], .app Sym.«<bal>» [.var 4]]) (acct 1 5) :=
  .ctor (by decide +kernel) (.cons idp (.cons (.ctor (by decide +kernel) (.cons (.var rfl) .nil)) .nil))

/-- The entry pattern denotes the one-entry map of account 1. -/
theorem elemp : PatVal c σ (.app Sym.«AcctCellMapItem» [.app Sym.«<id>» [.var 0],
    .app Sym.«<acct>» [.app Sym.«<id>» [.var 0], .app Sym.«<bal>» [.var 4]]]) (accts [(1, 5)]) :=
  .coll (by decide +kernel) (by decide +kernel) (.cons idp (.cons acctp .nil)) (by decide +kernel)

/-- **The cell map's pattern denotes the two accounts**: the entry for 1 joined with Rest, the map
of 2. -/
theorem mapp : PatVal c σ (.app Sym.«_AcctCellMap_» [.app Sym.«AcctCellMapItem» [.app Sym.«<id>» [.var 0],
    .app Sym.«<acct>» [.app Sym.«<id>» [.var 0], .app Sym.«<bal>» [.var 4]]], .var 5]) (accts [(1, 5), (2, 7)]) :=
  .coll (by decide +kernel) (by decide +kernel) (.cons elemp (.cons (.var rfl) .nil)) (by decide +kernel)

theorem kp : PatVal c σ (.app Sym.«<k>» [.app KCore.kseq [.inj Srt.«Op» KCore.Srt.kitem (.app Sym.«bump» [.var 0]), .var 1]])
    (.ctor Sym.«<k>» [.ctor KCore.kseq [.inj Srt.«Op» KCore.Srt.kitem (.ctor Sym.«bump» [int 1]), .ctor KCore.dotk []]]) :=
  .ctor (by decide +kernel) (.cons (.ctor (by decide +kernel)
    (.cons (.inj (.ctor (by decide +kernel) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil)

/-- **The left side denotes the configuration** under σ. -/
theorem lhs_match : PatVal c σ lhs start :=
  .ctor (by decide +kernel) (.cons kp (.cons (.var rfl) (.cons (.var rfl)
    (.cons (.ctor (by decide +kernel) (.cons mapp .nil)) (.cons (.var rfl) .nil)))))

theorem id_eval : EvalTerm c σ (.app Sym.«<id>» [.var 0]) (some (idc 1)) :=
  .ctor (rs := [some (int 1)]) (by decide +kernel) (.cons .var .nil)

/-- `B +Int 1` is 6. -/
theorem add_eval : EvalTerm c σ (.app KCore.intAdd [.var 4, .dv KCore.Srt.int (.int 1)]) (some (int 6)) :=
  .hook (rs := [some (int 5), some (int 1)]) (by decide +kernel) (by decide +kernel)
    (.cons .var (.cons .dv .nil)) (fun vs hv => by cases hv; decide +kernel) (fun h => by cases h)

theorem acct_eval : EvalTerm c σ (.app Sym.«<acct>» [.app Sym.«<id>» [.var 0],
    .app Sym.«<bal>» [.app KCore.intAdd [.var 4, .dv KCore.Srt.int (.int 1)]]]) (some (acct 1 6)) :=
  .ctor (rs := [some (idc 1), some (.ctor Sym.«<bal>» [int 6])]) (by decide +kernel)
    (.cons id_eval (.cons (.ctor (rs := [some (int 6)]) (by decide +kernel) (.cons add_eval .nil)) .nil))

/-- The entry for account 1, a parameter implemented by the map's element. -/
theorem elem_eval : EvalTerm c σ (.app Sym.«AcctCellMapItem» [.app Sym.«<id>» [.var 0],
    .app Sym.«<acct>» [.app Sym.«<id>» [.var 0],
      .app Sym.«<bal>» [.app KCore.intAdd [.var 4, .dv KCore.Srt.int (.int 1)]]]]) (some (accts [(1, 6)])) :=
  .param (rs := [some (idc 1), some (acct 1 6)]) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (.cons id_eval (.cons acct_eval .nil)) (by decide +kernel)

/-- The entry joined with Rest, by the map's concatenation. -/
theorem map_eval : EvalTerm c σ (.app Sym.«_AcctCellMap_» [.app Sym.«AcctCellMapItem» [.app Sym.«<id>» [.var 0],
    .app Sym.«<acct>» [.app Sym.«<id>» [.var 0],
      .app Sym.«<bal>» [.app KCore.intAdd [.var 4, .dv KCore.Srt.int (.int 1)]]]], .var 5])
    (some (accts [(1, 6), (2, 7)])) :=
  .param (rs := [some (accts [(1, 6)]), some (accts [(2, 7)])]) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (.cons elem_eval (.cons .var .nil)) (by decide +kernel)

/-- The right side's value under σ: account 1's balance 5 + 1. -/
theorem rhs_eval : EvalTerm c σ rhs (some final) :=
  .ctor (rs := [some (.ctor Sym.«<k>» [.ctor KCore.dotk []]), some stack, some sum,
      some (.ctor Sym.«<accts>» [accts [(1, 6), (2, 7)]]), some counter]) (by decide +kernel)
    (.cons (.ctor (rs := [some (.ctor KCore.dotk [])]) (by decide +kernel) (.cons .var .nil))
    (.cons .var (.cons .var
    (.cons (.ctor (rs := [some (accts [(1, 6), (2, 7)])]) (by decide +kernel) (.cons map_eval .nil))
    (.cons .var .nil)))))

/-- Every rule has priority 50, so no rule of a smaller one competes. -/
theorem prios : c.rules.all (·.prio == 50) = true := by decide +kernel

theorem start_sorted : c.sortOf start = some topCellSort := by decide +kernel
theorem final_sorted : c.sortOf final = some topCellSort := by decide +kernel

/-- **`bump(1)` steps** the two-account configuration to the one with account 1's balance 6. -/
theorem bump_step : Step c ⟨start, start_sorted⟩ ⟨final, final_sorted⟩ :=
  .rule bump (List.mem_of_getElem? rule3) σ
    (fun i s h => by
      match i, h with
      | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h =>
        simp only [bump, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h
        subst h
        exact ⟨_, rfl, by decide +kernel⟩
      | _ + 7, h => simp [bump] at h)
    lhs_match (fun t h => by cases h) .top rhs_eval (fun t h => by cases h) .top
    (fun r' hr' hlt => by
      have := List.all_eq_true.mp prios r' hr'
      simp only [beq_iff_eq] at this
      simp [bump, this] at hlt)

#eval show Lean.CoreM Unit from do
  for n in [``rule3, ``mapp, ``lhs_match, ``rhs_eval, ``bump_step] do
    let axs ← Lean.collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end Colls.Course
