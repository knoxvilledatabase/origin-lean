/-
Extracted from LinearAlgebra/BilinearForm/DualLattice.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Dual submodule with respect to a bilinear form.

## Main definitions and results
- `BilinForm.dualSubmodule`: The dual submodule with respect to a bilinear form.
- `BilinForm.dualSubmodule_span_of_basis`: The dual of a lattice is spanned by the dual basis.

## TODO
Properly develop the material in the context of lattices.
-/

open LinearMap (BilinForm)

open Module

variable {R S M} [CommRing R] [Field S] [AddCommGroup M]

variable [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

namespace LinearMap

namespace BilinForm

variable (B : BilinForm S M)

def dualSubmodule (N : Submodule R M) : Submodule R M where
  carrier := { x | ∀ y ∈ N, B x y ∈ (1 : Submodule R S) }
  add_mem' {a b} ha hb y hy := by simpa using add_mem (ha y hy) (hb y hy)
  zero_mem' y _ := by rw [B.zero_left]; exact zero_mem _
  smul_mem' r a ha y hy := by
    convert (1 : Submodule R S).smul_mem r (ha y hy)
    rw [← IsScalarTower.algebraMap_smul S r a]
    simp only [algebraMap_smul, map_smul_of_tower, LinearMap.smul_apply]

lemma le_flip_dualSubmodule {N₁ N₂ : Submodule R M} :
    N₁ ≤ B.flip.dualSubmodule N₂ ↔ N₂ ≤ B.dualSubmodule N₁ := by
  change (∀ (x : M), x ∈ N₁ → _) ↔ ∀ (x : M), x ∈ N₂ → _
  simp only [mem_dualSubmodule, Submodule.mem_one, flip_apply]
  exact forall₂_comm

noncomputable

def dualSubmoduleParing {N : Submodule R M} (x : B.dualSubmodule N) (y : N) : R :=
  (Submodule.mem_one.mp <| x.prop y y.prop).choose
