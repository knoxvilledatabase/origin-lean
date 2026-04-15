/-
Extracted from Algebra/Module/Submodule/Bilinear.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Images of pairs of submodules under bilinear maps

This file provides `Submodule.map₂`, which is later used to implement `Submodule.mul`.

## Main results

* `Submodule.map₂_eq_span_image2`: the image of two submodules under a bilinear map is the span of
  their `Set.image2`.

## Notes

This file is quite similar to the n-ary section of `Mathlib/Data/Set/Basic.lean` and to
`Mathlib/Order/Filter/NAry.lean`. Please keep them in sync.

## TODO

Generalize this file to semilinear maps.
-/

universe uι u v

open Set

open Pointwise

namespace Submodule

variable {ι : Sort uι} {R M N P : Type*}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

def map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) : Submodule R P :=
  ⨆ s : p, q.map (f s)

theorem apply_mem_map₂ (f : M →ₗ[R] N →ₗ[R] P) {m : M} {n : N} {p : Submodule R M}
    {q : Submodule R N} (hm : m ∈ p) (hn : n ∈ q) : f m n ∈ map₂ f p q :=
  (le_iSup _ ⟨m, hm⟩ : _ ≤ map₂ f p q) ⟨n, hn, by rfl⟩

theorem map₂_le {f : M →ₗ[R] N →ₗ[R] P} {p : Submodule R M} {q : Submodule R N}
    {r : Submodule R P} : map₂ f p q ≤ r ↔ ∀ m ∈ p, ∀ n ∈ q, f m n ∈ r :=
  ⟨fun H _m hm _n hn => H <| apply_mem_map₂ _ hm hn, fun H =>
    iSup_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩

variable (R) in

theorem map₂_span_span (f : M →ₗ[R] N →ₗ[R] P) (s : Set M) (t : Set N) :
    map₂ f (span R s) (span R t) = span R (Set.image2 (fun m n => f m n) s t) := by
  apply le_antisymm
  · rw [map₂_le]
    apply @span_induction R M _ _ _ s
    on_goal 1 =>
      intro a ha
      apply @span_induction R N _ _ _ t
      · intro b hb
        exact subset_span ⟨_, ‹_›, _, ‹_›, rfl⟩
    all_goals
      intros
      simp only [*, add_mem, smul_mem, zero_mem, map_zero, map_add,
        LinearMap.zero_apply, LinearMap.add_apply, LinearMap.smul_apply, map_smul]
  · rw [span_le, image2_subset_iff]
    intro a ha b hb
    exact apply_mem_map₂ _ (subset_span ha) (subset_span hb)
