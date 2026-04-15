/-
Extracted from Topology/Algebra/Module/WeakBilin.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

## Main definitions

The main definition is the type `WeakBilin B`.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `WeakBilin B` is a type synonym for `E`.
* The instance `WeakBilin.instTopologicalSpace` is the weak topology induced by the bilinear form
  `B`.

## Main results

We establish that `WeakBilin B` has the following structure:
* `WeakBilin.instContinuousAdd`: The addition in `WeakBilin B` is continuous.
* `WeakBilin.instContinuousSMul`: The scalar multiplication in `WeakBilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `fun x => B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## Notations

No new notation is introduced.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/

noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 E F : Type*}

section WeakTopology

@[nolint unusedArguments]
def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E

namespace WeakBilin

instance instAddCommMonoid [CommSemiring 𝕜] [a : AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommMonoid (WeakBilin B) := a

instance instModule [CommSemiring 𝕜] [AddCommMonoid E] [m : Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Module 𝕜 (WeakBilin B) := m

instance instAddCommGroup [CommSemiring 𝕜] [a : AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B) := a

instance (priority := 100) instModule' [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E]
    [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] [m : Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Module 𝕝 (WeakBilin B) := m

instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommMonoid F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) := s

section Semiring

variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E]

variable [AddCommMonoid F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance instTopologicalSpace : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

theorem coeFn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
  continuous_induced_dom

theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
  (continuous_pi_iff.mp (coeFn_continuous B)) y

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

theorem isEmbedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
    IsEmbedding fun (x : WeakBilin B) y => B x y :=
  Function.Injective.isEmbedding_induced <| LinearMap.coe_injective.comp hB

alias embedding := isEmbedding

theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, (isEmbedding hB).tendsto_nhds_iff]
  rfl

instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine
    cast (congr_arg _ ?_)
      (((coeFn_continuous B).comp continuous_fst).add ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine cast (congr_arg _ ?_) (continuous_fst.smul ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, LinearMap.map_smulₛₗ, RingHom.id_apply,
    LinearMap.smul_apply]

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]

variable [AddCommGroup E] [Module 𝕜 E]

variable [AddCommGroup F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance instTopologicalAddGroup [ContinuousAdd 𝕜] : TopologicalAddGroup (WeakBilin B) where
  toContinuousAdd := by infer_instance
  continuous_neg := by
    refine continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => ?_)
    refine cast (congr_arg _ ?_) (eval_continuous B (-y))
    ext x
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

end Ring

end WeakBilin

end WeakTopology
