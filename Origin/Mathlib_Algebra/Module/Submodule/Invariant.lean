/-
Extracted from Algebra/Module/Submodule/Invariant.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The lattice of invariant submodules

In this file we defined the type `Module.End.invtSubmodule`, associated to a linear endomorphism of
a module. Its utility stems primarily from those occasions on which we wish to take advantage of the
lattice structure of invariant submodules.

See also `Mathlib/Algebra/Polynomial/Module/AEval.lean`.

-/

open Submodule (span)

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

def invtSubmodule : Sublattice (Submodule R M) where
  carrier := {p : Submodule R M | p ≤ p.comap f}
  supClosed' p hp q hq := sup_le_iff.mpr
    ⟨le_trans hp <| Submodule.comap_mono le_sup_left,
    le_trans hq <| Submodule.comap_mono le_sup_right⟩
  infClosed' p hp q hq := by
    simp only [Set.mem_setOf_eq, Submodule.comap_inf, le_inf_iff]
    exact ⟨inf_le_of_left_le hp, inf_le_of_right_le hq⟩

theorem mem_invtSubmodule_iff_map_le {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ p.map f ≤ p := Submodule.map_le_iff_le_comap.symm

alias ⟨_, _root_.Set.Mapsto.mem_invtSubmodule⟩ := mem_invtSubmodule_iff_mapsTo

lemma mem_invtSubmodule_symm_iff_le_map {f : M ≃ₗ[R] M} {p : Submodule R M} :
    p ∈ invtSubmodule f.symm ↔ p ≤ p.map (f : M →ₗ[R] M) :=
  (mem_invtSubmodule_iff_map_le _).trans (f.toEquiv.symm.subset_symm_image _ _).symm

lemma invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add :
    f.invtSubmodule ⊓ g.invtSubmodule ≤ (f + g).invtSubmodule :=
  fun p ⟨hfp, hgp⟩ _ hx ↦ p.add_mem (hfp hx) (hgp hx)

section CommRing

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M] [Module S M]
  [DistribSMul S R] [SMulCommClass R S M] [IsScalarTower S R M] (f : End R M)

lemma invtSubmodule_le_invtSubmodule_smul (c : S) : f.invtSubmodule ≤ (c • f).invtSubmodule :=
  fun p hfp _ hx ↦ p.smul_of_tower_mem c (hfp hx)
