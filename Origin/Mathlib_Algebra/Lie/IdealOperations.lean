/-
Extracted from Algebra/Lie/IdealOperations.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideal operations for Lie algebras

Given a Lie module `M` over a Lie algebra `L`, there is a natural action of the Lie ideals of `L`
on the Lie submodules of `M`. In the special case that `M = L` with the adjoint action, this
provides a pairing of Lie ideals which is especially important. For example, it can be used to
define solvability / nilpotency of a Lie algebra via the derived / lower-central series.

## Main definitions

  * `LieSubmodule.hasBracket`
  * `LieSubmodule.lieIdeal_oper_eq_linear_span`
  * `LieIdeal.map_bracket_le`
  * `LieIdeal.comap_bracket_le`

## Notation

Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M` and a Lie
ideal `I ⊆ L`, we introduce the notation `⁅I, N⁆` for the Lie submodule of `M` corresponding to
the action defined in this file.

## Tags

lie algebra, ideal operation
-/

universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]

variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)

variable (f : M →ₗ⁅R,L⁆ M₂)

section LieIdealOperations

theorem map_comap_le : map f (comap f N₂) ≤ N₂ :=
  (N₂ : Set M₂).image_preimage_subset f

theorem map_comap_eq (hf : N₂ ≤ f.range) : map f (comap f N₂) = N₂ := by
  rw [SetLike.ext'_iff]
  exact Set.image_preimage_eq_of_subset hf

theorem le_comap_map : N ≤ comap f (map f N) :=
  (N : Set M).subset_preimage_image f

theorem comap_map_eq (hf : f.ker = ⊥) : comap f (map f N) = N := by
  rw [SetLike.ext'_iff]
  exact (N : Set M).preimage_image_eq (f.ker_eq_bot.mp hf)
