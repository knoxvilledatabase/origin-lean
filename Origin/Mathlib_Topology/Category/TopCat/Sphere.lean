/-
Extracted from Topology/Category/TopCat/Sphere.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopCat.Basic

noncomputable section

/-!
# Euclidean spheres

This files defines the `n`-sphere `𝕊 n` and the `n`-disk `𝔻` as objects in `TopCat`.
The parameter `n` is in `ℤ` so as to facilitate the definition of
CW-complexes (see the file `Topology.CWComplex`).

-/

universe u

namespace TopCat

noncomputable def sphere (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| (n + 1).toNat) 1

noncomputable def disk (n : ℤ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ <| Fin <| n.toNat) 1

scoped prefix:arg "𝕊 " => sphere

scoped prefix:arg "𝔻 " => disk

end TopCat
