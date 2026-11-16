/-
  Terms of a sort, for writing a definition's configurations and programs.

  `Tm s` is a ground term meant to have sort `s`; nothing checks it (the sort of a term is
  `Semantics.sortOf`, which depends on the definition). Its use is to let Lean insert the
  injections the sorts require: a package's generated `Syntax` module declares, for each
  subsort `a < b` of its definition, a coercion `Tm a → Tm b` that is the injection
  (`injNormal a b`), and gives each constructor a function on `Tm` of its argument and result
  sorts. A `KItem` used as a `K` is the one-item sequence (`kseq i dotk`), in every definition.
-/
import KcoreSpec.Hooks
import KcoreSpec.Evaluation

set_option autoImplicit false

namespace KCore

/-- A ground term written at sort `s`. -/
structure Tm (s : Srt) where
  val : GroundTerm

namespace Tm

/-- The injection from `a` into `b`: `inj{a, b}`, collapsing an injection already there. -/
def inj {a b : Srt} (t : Tm a) : Tm b := ⟨injNormal a b t.val⟩

/-- The sequence of an item before a rest. -/
def kseq (i : Tm Srt.kitem) (k : Tm Srt.k) : Tm Srt.k := ⟨.ctor KCore.kseq [i.val, k.val]⟩

/-- The empty sequence. -/
def dotk : Tm Srt.k := ⟨.ctor KCore.dotk []⟩

/-- A `KItem` as a `K`: the sequence of the one item. -/
instance : Coe (Tm Srt.kitem) (Tm Srt.k) := ⟨fun i => kseq i dotk⟩

def int (i : Int) : Tm Srt.int := ⟨KCore.int i⟩
def bool (b : Bool) : Tm Srt.bool := ⟨KCore.bool b⟩
/-- An identifier token (`Id`). -/
def ident (x : String) : Tm Srt.ident := ⟨.dv Srt.ident (.tok x)⟩
/-- A string token (`String`). -/
def str (x : String) : Tm Srt.string := ⟨.dv Srt.string (.tok x)⟩

/-- The map of the library's `Map` sort with these entries: each inserted in key order, a later
entry replacing an earlier one of the same key. -/
def map (es : List (Tm Srt.kitem × Tm Srt.kitem)) : Tm Srt.map :=
  ⟨.map Srt.map (es.foldl (fun m e => insertE e.1.val e.2.val m) [])⟩

@[simp] theorem inj_val {a b : Srt} (t : Tm a) : (inj t : Tm b).val = injNormal a b t.val := rfl
@[simp] theorem kseq_val (i : Tm Srt.kitem) (k : Tm Srt.k) :
    (kseq i k).val = .ctor KCore.kseq [i.val, k.val] := rfl
@[simp] theorem dotk_val : dotk.val = .ctor KCore.dotk [] := rfl

end Tm

end KCore
