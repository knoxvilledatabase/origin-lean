/-
Extracted from Geometry/Manifold/PoincareConjecture.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Util.Superscript

/-!
# Statement of the generalized Poincaré conjecture

https://en.wikipedia.org/wiki/Generalized_Poincar%C3%A9_conjecture

The mathlib notation `≃ₕ` stands for a homotopy equivalence, `≃ₜ` stands for a homeomorphism,
and `≃ₘ⟮𝓡 n, 𝓡 n⟯` stands for a diffeomorphism, where `𝓡 n` is the `n`-dimensional Euclidean
space viewed as a model space.
-/

open scoped Manifold

open Metric (sphere)

local macro:max "ℝ"n:superscript(term) : term => `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

local macro:max "𝕊"n:superscript(term) : term =>
  `(sphere (0 : EuclideanSpace ℝ (Fin ($(⟨n.raw[0]⟩) + 1))) 1)

variable (M : Type*) [TopologicalSpace M]

open ContinuousMap

proof_wanted ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere [T2Space M]

    (n : ℕ) [ChartedSpace ℝⁿ M] : M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₜ 𝕊ⁿ)

proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three

    [T2Space M] [ChartedSpace ℝ³ M] [SimplyConnectedSpace M] [CompactSpace M] :

    Nonempty (M ≃ₜ 𝕊³)

proof_wanted SimplyConnectedSpace.nonempty_diffeomorph_sphere_three

    [T2Space M] [ChartedSpace ℝ³ M] [SmoothManifoldWithCorners (𝓡 3) M]

    [SimplyConnectedSpace M] [CompactSpace M] :

    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)

def ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere (n : ℕ) : Prop :=
  ∀ (_ : ChartedSpace ℝⁿ M) (_ : SmoothManifoldWithCorners (𝓡 n) M),
    M ≃ₕ 𝕊ⁿ → Nonempty (M ≃ₘ⟮𝓡 n, 𝓡 n⟯ 𝕊ⁿ)

proof_wanted exists_homeomorph_isEmpty_diffeomorph_sphere_seven :

    ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace ℝ⁷ M)

      (_ : SmoothManifoldWithCorners (𝓡 7) M) (_homeo : M ≃ₜ 𝕊⁷),

      IsEmpty (M ≃ₘ⟮𝓡 7, 𝓡 7⟯ 𝕊⁷)

proof_wanted exists_open_nonempty_homeomorph_isEmpty_diffeomorph_euclideanSpace_four :

    ∃ M : TopologicalSpace.Opens ℝ⁴, Nonempty (M ≃ₜ ℝ⁴) ∧ IsEmpty (M ≃ₘ⟮𝓡 4, 𝓡 4⟯ ℝ⁴)
