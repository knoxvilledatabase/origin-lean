/-
Extracted from Analysis/SpecialFunctions/Complex/Circle.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `Circle.exp` and the restriction of `Complex.arg`
to the unit circle. These two maps define a partial equivalence between `Circle` and `ℝ`, see
`Circle.argPartialEquiv` and `Circle.argEquiv`, that sends the whole circle to `(-π, π]`.
-/

open Complex Function Set

open Real

namespace Circle

theorem injective_arg : Injective fun z : Circle => arg z := fun z w h =>
  Subtype.ext <| ext_norm_arg (z.norm_coe.trans w.norm_coe.symm) h
