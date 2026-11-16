/-
  The statements a generated package states, pinned on peano: the types of `coreOK_defn`,
  `sound_hyp`, `complete_hyp`, `fnHyp_defn`, `sound_defn` and `complete_defn` as `kcore gen --core`
  writes them, each checked by its proof term at the type written out, and their axioms exactly
  `propext`, `Classical.choice`, `Quot.sound`. Over peano's text generated with `--core` under the
  namespace `PinPeano` (test/pins-peano.sh generates, builds and checks it):

      gen/gen.sh examples/peano/Peano/definition.kore .lake/pins/peano PinPeano --core
      gen/build.sh .lake/pins/peano
      LEAN_PATH=.lake/pins/peano/.lake/build/lib/lean:$(lake env printenv LEAN_PATH) lean test/PinsPeano.lean
-/
import PinPeano.Sound
import PinPeano.FnHyp

set_option autoImplicit false

namespace PinPeano.Pins

open KCore PinPeano

example : defn.sem.coreOK = true := coreOK_defn

example : FnHyp defn.sem → SoundC defn.sem := sound_hyp

example : ∀ ref : OutFn, FnHyp defn.sem → CompleteC defn.sem ref := complete_hyp

example : FnHyp defn.sem := fnHyp_defn

example : SoundC defn.sem := sound_defn

example : ∀ ref : OutFn, CompleteC defn.sem ref := complete_defn

/-- info: 'PinPeano.coreOK_defn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PinPeano.coreOK_defn

/-- info: 'PinPeano.sound_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PinPeano.sound_hyp

/-- info: 'PinPeano.complete_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PinPeano.complete_hyp

/-- info: 'PinPeano.fnHyp_defn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PinPeano.fnHyp_defn

/-- info: 'PinPeano.sound_defn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PinPeano.sound_defn

/-- info: 'PinPeano.complete_defn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms PinPeano.complete_defn

end PinPeano.Pins
