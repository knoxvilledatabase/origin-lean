/-
Extracted from Topology/Algebra/Module/WeakDual.lean
Genuine: 13 | Conflates: 0 | Dissolved: 0 | Infrastructure: 27
-/
import Origin.Core
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.WeakBilin

/-!
# Weak dual topology

We continue in the setting of `Mathlib.Topology.Algebra.Module.WeakBilin`,
which defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

In this file, we consider two special cases.
In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-* topology,
`WeakDual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `WeakSpace 𝕜 E := E`.

## Main definitions

The main definitions are the types `WeakDual 𝕜 E` and `WeakSpace 𝕜 E`,
with the respective topology instances on it.

* `WeakDual 𝕜 E` is a type synonym for `Dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `WeakDual.instTopologicalSpace` is the weak-* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `WeakSpace 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

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

def topDualPairing (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜] : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜

theorem topDualPairing_apply [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜] (v : E →L[𝕜] 𝕜)
    (x : E) : topDualPairing 𝕜 E v x = v x :=
  rfl

def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)

namespace WeakDual

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]

variable [ContinuousConstSMul 𝕜 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

instance instAddCommMonoid : AddCommMonoid (WeakDual 𝕜 E) :=
  WeakBilin.instAddCommMonoid (topDualPairing 𝕜 E)

instance instModule : Module 𝕜 (WeakDual 𝕜 E) :=
  WeakBilin.instModule (topDualPairing 𝕜 E)

instance instTopologicalSpace : TopologicalSpace (WeakDual 𝕜 E) :=
  WeakBilin.instTopologicalSpace (topDualPairing 𝕜 E)

instance instContinuousAdd : ContinuousAdd (WeakDual 𝕜 E) :=
  WeakBilin.instContinuousAdd (topDualPairing 𝕜 E)

instance instInhabited : Inhabited (WeakDual 𝕜 E) :=
  ContinuousLinearMap.inhabited

instance instFunLike : FunLike (WeakDual 𝕜 E) E 𝕜 :=
  ContinuousLinearMap.funLike

instance instContinuousLinearMapClass : ContinuousLinearMapClass (WeakDual 𝕜 E) 𝕜 E 𝕜 :=
  ContinuousLinearMap.continuousSemilinearMapClass

instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.mulAction

instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.distribMulAction

instance instModule' (R) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  ContinuousLinearMap.module

instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) :=
  ⟨fun m =>
    continuous_induced_rng.2 <| (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng.2 <|
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  continuous_induced_dom

theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coeFn_continuous y

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)

instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
   (WeakBilin.isEmbedding ContinuousLinearMap.coe_injective).t2Space

end Semiring

section Ring

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]

variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]

instance instAddCommGroup : AddCommGroup (WeakDual 𝕜 E) :=
  WeakBilin.instAddCommGroup (topDualPairing 𝕜 E)

instance instTopologicalAddGroup : TopologicalAddGroup (WeakDual 𝕜 E) :=
  WeakBilin.instTopologicalAddGroup (topDualPairing 𝕜 E)

end Ring

end WeakDual

def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip

section Semiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]

variable [ContinuousConstSMul 𝕜 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

namespace WeakSpace

instance instAddCommMonoid : AddCommMonoid (WeakSpace 𝕜 E) :=
  WeakBilin.instAddCommMonoid (topDualPairing 𝕜 E).flip

instance instModule : Module 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instModule (topDualPairing 𝕜 E).flip

instance instTopologicalSpace : TopologicalSpace (WeakSpace 𝕜 E) :=
  WeakBilin.instTopologicalSpace (topDualPairing 𝕜 E).flip

instance instContinuousAdd : ContinuousAdd (WeakSpace 𝕜 E) :=
  WeakBilin.instContinuousAdd (topDualPairing 𝕜 E).flip

instance instModule' [CommSemiring 𝕝] [Module 𝕝 E] : Module 𝕝 (WeakSpace 𝕜 E) :=
  WeakBilin.instModule' (topDualPairing 𝕜 E).flip

instance instIsScalarTower [CommSemiring 𝕝] [Module 𝕝 𝕜] [Module 𝕝 E] [IsScalarTower 𝕝 𝕜 E] :
    IsScalarTower 𝕝 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instIsScalarTower (topDualPairing 𝕜 E).flip

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }

theorem map_apply (f : E →L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
  rfl

@[simp]
theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
  rfl

end WeakSpace

variable (𝕜 E) in

def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

variable (𝕜 E) in

def toWeakSpaceCLM : E →L[𝕜] WeakSpace 𝕜 E where
  __ := toWeakSpace 𝕜 E
  cont := by
    apply WeakBilin.continuous_of_continuous_eval
    exact ContinuousLinearMap.continuous

variable (𝕜 E) in

@[simp]
theorem toWeakSpaceCLM_eq_toWeakSpace (x : E) :
    toWeakSpaceCLM 𝕜 E x = toWeakSpace 𝕜 E x := by rfl

theorem toWeakSpaceCLM_bijective :
    Function.Bijective (toWeakSpaceCLM 𝕜 E) :=
  (toWeakSpace 𝕜 E).bijective

theorem isOpenMap_toWeakSpace_symm : IsOpenMap (toWeakSpace 𝕜 E).symm :=
  IsOpenMap.of_inverse (toWeakSpaceCLM 𝕜 E).cont
    (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

theorem WeakSpace.isOpen_of_isOpen (V : Set E)
    (hV : IsOpen ((toWeakSpaceCLM 𝕜 E) '' V : Set (WeakSpace 𝕜 E))) : IsOpen V := by
  simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV

theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
    {x : WeakDual 𝕜 E} :
    Tendsto f l (𝓝 x) ↔
      ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

end Semiring

section Ring

namespace WeakSpace

variable [CommRing 𝕜] [TopologicalSpace 𝕜] [TopologicalAddGroup 𝕜] [ContinuousConstSMul 𝕜 𝕜]

variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]

instance instAddCommGroup : AddCommGroup (WeakSpace 𝕜 E) :=
  WeakBilin.instAddCommGroup (topDualPairing 𝕜 E).flip

instance instTopologicalAddGroup : TopologicalAddGroup (WeakSpace 𝕜 E) :=
  WeakBilin.instTopologicalAddGroup (topDualPairing 𝕜 E).flip

end WeakSpace

end Ring
