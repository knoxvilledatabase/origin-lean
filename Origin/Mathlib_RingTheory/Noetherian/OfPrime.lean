/-
Extracted from RingTheory/Noetherian/OfPrime.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Noetherian rings and prime ideals

## Main results

- `IsNoetherianRing.of_prime`: a ring where all prime ideals are finitely generated is a noetherian
  ring

## References

- [cohen1950]: *Commutative rings with restricted minimum condition*, I. S. Cohen, Theorem 2
-/

variable {R : Type*} [CommRing R]

namespace Ideal

open Set Finset

theorem isOka_fg : IsOka (FG (R := R)) where
  top := ⟨{1}, by simp⟩
  oka {I a} hsup hcolon := by
    classical
    obtain ⟨_, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hsup
    obtain ⟨_, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hcolon
    rw [submodule_span_eq] at hf
    have H k : ∃ r : R, ∃ p ∈ I, r * a + p = f k := by
      apply mem_span_singleton_sup.1
      rw [sup_comm, ← hf]
      exact mem_span_range_self
    choose! r p p_mem_I Hf using H
    refine ⟨image p univ ∪ image (a • i) univ, le_antisymm ?_ (fun y hy ↦ ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨p_mem_I, fun _ ↦ mul_comm a _ ▸ mem_colon_span_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      obtain ⟨s, H⟩ := mem_span_range_iff_exists_fun.1 (hf ▸ Ideal.mem_sup_left hy)
      simp_rw [← Hf] at H
      ring_nf at H
      rw [sum_add_distrib, ← sum_mul, add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ ↦ mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm, ← smul_eq_mul, range_smul, ← submodule_span_eq, Submodule.span_smul, hi]
      exact smul_mem_smul_set <| mem_colon_span_singleton.2 <|
        (I.add_mem_iff_right <| I.sum_mem (fun _ _ ↦ mul_mem_left _ _ <| p_mem_I _)).1 (H ▸ hy)

end Ideal

open Ideal

theorem IsNoetherianRing.of_prime_ne_bot (H : ∀ I : Ideal R, I.IsPrime → I ≠ ⊥ → I.FG) :
    IsNoetherianRing R :=
  .of_prime fun I hi ↦ (eq_or_ne I ⊥).elim (· ▸ Submodule.fg_bot) <| H _ hi
