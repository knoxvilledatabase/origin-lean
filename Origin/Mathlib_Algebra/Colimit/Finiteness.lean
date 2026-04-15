/-
Extracted from Algebra/Colimit/Finiteness.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Modules as direct limits of finitely generated submodules

We show that every module is the direct limit of its finitely generated submodules.

## Main definitions

* `Module.fgSystem`: the directed system of finitely generated submodules of a module.

* `Module.fgSystem.equiv`: the isomorphism between a module and the direct limit of its
  finitely generated submodules.
-/

namespace Module

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

def fgSystem (N₁ N₂ : {N : Submodule R M // N.FG}) (le : N₁ ≤ N₂) : N₁ →ₗ[R] N₂ :=
  Submodule.inclusion le

open DirectLimit

namespace fgSystem

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [DecidableEq (Submodule R M)]

open Submodule in

noncomputable def equiv : DirectLimit _ (fgSystem R M) ≃ₗ[R] M :=
  .ofBijective (lift _ _ _ _ (fun _ ↦ Submodule.subtype _) fun _ _ _ _ ↦ rfl)
    ⟨lift_injective _ _ fun _ ↦ Subtype.val_injective, fun x ↦
      ⟨of _ _ _ _ ⟨_, fg_span_singleton x⟩ ⟨x, subset_span <| by rfl⟩, lift_of ..⟩⟩

variable {R M}

lemma equiv_comp_of (N : {N : Submodule R M // N.FG}) :
    (equiv R M).toLinearMap ∘ₗ of _ _ _ _ N = N.1.subtype := by
  ext; simp [equiv]

end fgSystem

end Module
