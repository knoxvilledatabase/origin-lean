/-
Extracted from Topology/Algebra/MulAction.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous monoid action

In this file we define class `ContinuousSMul`. We say `ContinuousSMul M X` if `M` acts on `X` and
the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `ContinuousSMul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `Units.continuousSMul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `Homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `Continuous.smul`
or `Filter.Tendsto.smul` that provide dot-syntax access to `ContinuousSMul`.
-/

open Topology Pointwise

open Filter

class ContinuousSMul (M X : Type*) [SMul M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The scalar multiplication `(•)` is continuous. -/
  continuous_smul : Continuous fun p : M × X => p.1 • p.2

export ContinuousSMul (continuous_smul)

class ContinuousVAdd (M X : Type*) [VAdd M X] [TopologicalSpace M] [TopologicalSpace X] :
    Prop where
  /-- The additive action `(+ᵥ)` is continuous. -/
  continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2

export ContinuousVAdd (continuous_vadd)

attribute [to_additive] ContinuousSMul

attribute [continuity, fun_prop] continuous_smul continuous_vadd

section Main

variable {M X Y α : Type*} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]

section SMul

variable [SMul M X] [ContinuousSMul M X]

lemma IsScalarTower.continuousSMul {M : Type*} (N : Type*) {α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace α] [ContinuousSMul M N] [ContinuousSMul N α] : ContinuousSMul M α :=
  { continuous_smul := by
      suffices Continuous (fun p : M × α ↦ (p.1 • (1 : N)) • p.2) by simpa
      fun_prop }
