/-
Extracted from RingTheory/Finiteness/Nilpotent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Nilpotent maps on finite modules

-/

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem Module.End.isNilpotent_iff_of_finite [Module.Finite R M] {f : End R M} :
    IsNilpotent f ↔ ∀ m : M, ∃ n : ℕ, (f ^ n) m = 0 := by
  refine ⟨fun ⟨n, hn⟩ m ↦ ⟨n, by simp [hn]⟩, fun h ↦ ?_⟩
  rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
  choose g hg using h
  use Finset.sup S g
  ext m
  have hm : m ∈ Submodule.span R S := by simp [hS]
  induction hm using Submodule.span_induction with
  | mem x hx => exact pow_map_zero_of_le (Finset.le_sup hx) (hg x)
  | zero => simp
  | add => simp_all
  | smul => simp_all

namespace Matrix

open scoped Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {A : Matrix ι ι R}
