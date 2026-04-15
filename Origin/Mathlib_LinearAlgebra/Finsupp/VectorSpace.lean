/-
Extracted from LinearAlgebra/Finsupp/VectorSpace.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

-/

noncomputable section

open Set LinearMap Module Submodule

universe u v w

namespace DFinsupp

variable {ι : Type*} {R : Type*} {M : ι → Type*}

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

noncomputable def basis {η : ι → Type*} (b : ∀ i, Basis (η i) R (M i)) :
    Basis (Σ i, η i) R (Π₀ i, M i) :=
  .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)

variable (R M) in

-- INSTANCE (free from Core): _root_.Module.Free.dfinsupp

variable [DecidableEq ι] {φ : ι → Type*} (f : ∀ i, φ i → M i)

open Finsupp (linearCombination)

theorem linearIndependent_single (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2) := by
  classical
  have : linearCombination R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) =
    DFinsupp.mapRange.linearMap (fun i ↦ linearCombination R (f i)) ∘ₗ
    (sigmaFinsuppLequivDFinsupp R).toLinearMap := by ext; simp
  rw [LinearIndependent, this]
  exact ((DFinsupp.mapRange_injective _ fun _ ↦ map_zero _).mpr hf).comp (Equiv.injective _)

lemma linearIndependent_single_iff :
    LinearIndependent R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) ↔
      ∀ i, LinearIndependent R (f i) :=
  ⟨fun h i ↦ (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

end DFinsupp

namespace Finsupp

section Semiring

variable {R : Type*} {M : Type*} {ι : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem linearIndependent_single {φ : ι → Type*} (f : ∀ i, φ i → M)
    (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2) := by
  classical
  convert (DFinsupp.linearIndependent_single _ hf).map_injOn
    _ (finsuppLequivDFinsupp R).symm.injective.injOn
  simp

lemma linearIndependent_single_iff {φ : ι → Type*} {f : ∀ i, φ i → M} :
    LinearIndependent R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) ↔
      ∀ i, LinearIndependent R (f i) :=
  ⟨fun h i ↦ (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

open LinearMap Submodule

open scoped Classical in

protected def basis {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) : Basis (Σ i, φ i) R (ι →₀ M) :=
  .ofRepr <| (finsuppLequivDFinsupp R).trans <|
    (DFinsupp.mapRange.linearEquiv fun i ↦ (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm
