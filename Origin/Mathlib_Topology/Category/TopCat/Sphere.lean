/-
Extracted from Topology/Category/TopCat/Sphere.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Euclidean spheres

This file defines the `n`-sphere `𝕊 n`, the `n`-disk `𝔻 n`, its boundary `∂𝔻 n` and its interior
`𝔹 n` as objects in `TopCat`.

-/

universe u

namespace TopCat

open CategoryTheory

noncomputable def disk (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

noncomputable def diskBoundary (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

noncomputable def sphere (n : ℕ) : TopCat.{u} :=
  diskBoundary (n + 1)

noncomputable def ball (n : ℕ) : TopCat.{u} :=
  TopCat.of <| ULift <| Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1

scoped prefix:arg "𝔻 " => disk

scoped prefix:arg "∂𝔻 " => diskBoundary

scoped prefix:arg "𝕊 " => sphere

scoped prefix:arg "𝔹 " => ball

def diskBoundaryInclusion (n : ℕ) : ∂𝔻 n ⟶ 𝔻 n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, le_of_eq hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }

def ballInclusion (n : ℕ) : 𝔹 n ⟶ 𝔻 n :=
  ofHom
    { toFun := fun ⟨p, hp⟩ ↦ ⟨p, Metric.ball_subset_closedBall hp⟩
      continuous_toFun := ⟨fun t ⟨s, ⟨r, hro, hrs⟩, hst⟩ ↦ by
        rw [isOpen_induced_iff, ← hst, ← hrs]
        tauto⟩ }

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): {n

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): {n

-- INSTANCE (free from Core): (n

-- INSTANCE (free from Core): (n

end TopCat
