/-
Extracted from NumberTheory/DirichletCharacter/Orthogonality.lean
Genuine: 5 of 7 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Orthogonality relations for Dirichlet characters

Let `n` be a positive natural number. The main result of this file is
`DirichletCharacter.sum_char_inv_mul_char_eq`, which says that when `a : ZMod n` is a unit
and `b : ZMod n`, then the sum `∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b` vanishes
when `a ≠ b` and has the value `n.totient` otherwise. This requires `R` to have
enough roots of unity (e.g., `R` could be an algebraically closed field of characteristic zero).
-/

namespace DirichletCharacter

noncomputable instance fintype {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} :
    Fintype (DirichletCharacter R n) := .ofFinite _

variable (R : Type*) [CommRing R] (n : ℕ) [NeZero n]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

lemma mulEquiv_units : Nonempty (DirichletCharacter R n ≃* (ZMod n)ˣ) :=
  MulChar.mulEquiv_units ..

lemma card_eq_totient_of_hasEnoughRootsOfUnity :
    Nat.card (DirichletCharacter R n) = n.totient := by
  rw [← ZMod.card_units_eq_totient n, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulEquiv_units R n).some.toEquiv

variable {n}

-- DISSOLVED: exists_apply_ne_one_of_hasEnoughRootsOfUnity

variable [IsDomain R]

theorem sum_characters_eq_zero ⦃a : ZMod n⦄ (ha : a ≠ 1) :
    ∑ χ : DirichletCharacter R n, χ a = 0 := by
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity R ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' ↦ rfl

theorem sum_characters_eq (a : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a = if a = 1 then (n.totient : R) else 0 := by
  split_ifs with ha
  · simpa only [ha, map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card]
      using congrArg Nat.cast <| card_eq_totient_of_hasEnoughRootsOfUnity R n
  · exact sum_characters_eq_zero R ha

theorem sum_char_inv_mul_char_eq {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    ∑ χ : DirichletCharacter R n, χ a⁻¹ * χ b = if a = b then (n.totient : R) else 0 := by
  simp only [← map_mul, sum_characters_eq, ZMod.inv_mul_eq_one_of_isUnit ha]

end DirichletCharacter
