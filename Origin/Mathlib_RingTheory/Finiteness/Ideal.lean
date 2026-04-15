/-
Extracted from RingTheory/Finiteness/Ideal.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finitely generated ideals

Lemmas about finiteness of ideal operations.
-/

open Function (Surjective)

open Finsupp

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R →+* S)
    (g : S →+* A) (hf : (RingHom.ker f).FG) (hg : (RingHom.ker g).FG)
    (hsur : Function.Surjective f) :
    (RingHom.ker (g.comp f)).FG := by
  letI : Algebra R S := RingHom.toAlgebra f
  letI : Algebra R A := RingHom.toAlgebra (g.comp f)
  letI : Algebra S A := RingHom.toAlgebra g
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact Submodule.fg_ker_comp f₁ g₁ hf
    (Submodule.FG.restrictScalars_of_surjective hg hsur) hsur

theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
    ∃ n : ℕ, I.radical ^ n ≤ I := by
  suffices hJ : ∀ J : Ideal R, J.FG → J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I by
    simpa using hJ I.radical h
  intro J hJ hJK
  induction J, hJ using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := hJK (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
  | sup J K _ _ hJ hK =>
    obtain ⟨n, hn⟩ := hJ fun x hx => hJK <| mem_sup_left hx
    obtain ⟨m, hm⟩ := hK fun x hx => hJK <| mem_sup_right hx
    use n + m
    rw [← add_eq_sup, add_pow, sum_eq_sup, Finset.sup_le_iff]
    refine fun i _ => mul_le_right.trans ?_
    obtain h | h := le_or_gt n i
    · exact mul_le_right.trans ((pow_le_pow_right h).trans hn)
    · exact mul_le_left.trans ((pow_le_pow_right (by lia)).trans hm)

theorem exists_pow_le_of_le_radical_of_fg_radical {R : Type*} [CommSemiring R] {I J : Ideal R}
    (hIJ : I ≤ J.radical) (hJ : J.radical.FG) :
    ∃ k : ℕ, I ^ k ≤ J := by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  exact ⟨k, (pow_right_mono hIJ k).trans hk⟩

theorem _root_.Submodule.FG.smul {I : Ideal R} [I.IsTwoSided] {N : Submodule R M}
    (hI : I.FG) (hN : N.FG) : (I • N).FG := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨t, rfl⟩ := hN
  classical rw [Submodule.span_smul_span, ← s.coe_smul]
  exact ⟨_, rfl⟩

theorem FG.mul {I J : Ideal R} [I.IsTwoSided] (hI : I.FG) (hJ : J.FG) : (I * J).FG :=
  Submodule.FG.smul hI hJ

theorem FG.pow {I : Ideal R} [I.IsTwoSided] {n : ℕ} (hI : I.FG) : (I ^ n).FG :=
  n.rec (by rw [I.pow_zero, one_eq_top]; exact fg_top R) fun n ih ↦ by
    rw [IsTwoSided.pow_succ]
    exact hI.mul ih

end Ideal
