/-
Extracted from LinearAlgebra/Projectivization/Cardinality.lean
Genuine: 6 of 10 | Dissolved: 2 | Infrastructure: 2
-/
import Origin.Core

/-!
# Cardinality of projective spaces

We compute the cardinality of `ℙ k V` if `k` is a finite field.

-/

namespace Projectivization

open scoped LinearAlgebra.Projectivization

variable (k V : Type*) [DivisionRing k] [AddCommGroup V] [Module k V]

-- DISSOLVED: equivQuotientOrbitRel

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: nonZeroEquivProjectivizationProdUnits

-- INSTANCE (free from Core): isEmpty_of_subsingleton

-- INSTANCE (free from Core): finite_of_finite

lemma finite_iff_of_finite [Finite k] : Finite (ℙ k V) ↔ Finite V := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  let e := nonZeroEquivProjectivizationProdUnits k V
  have : Finite { v : V // v ≠ 0 } := Finite.of_equiv _ e.symm
  let eq : { v : V // v ≠ 0 } ⊕ Unit ≃ V :=
    ⟨(Sum.elim Subtype.val (fun _ ↦ 0)), fun v ↦ if h : v = 0 then Sum.inr () else Sum.inl ⟨v, h⟩,
      by intro x; aesop, by intro x; aesop⟩
  exact Finite.of_equiv _ eq

lemma card : Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1) := by
  nontriviality V
  cases finite_or_infinite k with
  | inr h =>
    have : Infinite V := Module.Free.infinite k V
    simp
  | inl h =>
  cases finite_or_infinite V with
  | inr h =>
    have := not_iff_not.mpr (finite_iff_of_finite k V)
    push Not at this
    have : Infinite (ℙ k V) := by rwa [this]
    simp
  | inl h =>
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (ℙ k V) := Fintype.ofFinite (ℙ k V)
  haveI : Fintype k := Fintype.ofFinite k
  have hV : Fintype.card { v : V // v ≠ 0 } = Fintype.card V - 1 := by simp
  simp_rw [← Fintype.card_eq_nat_card, ← Fintype.card_units (α := k), ← hV]
  rw [Fintype.card_congr (nonZeroEquivProjectivizationProdUnits k V), Fintype.card_prod]

lemma card' [Finite V] : Nat.card V = Nat.card (ℙ k V) * (Nat.card k - 1) + 1 := by
  rw [← card k V]
  have : Nat.card V > 0 := Nat.card_pos
  lia

end

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

lemma card'' [Finite k] : Nat.card (ℙ k V) = (Nat.card V - 1) / (Nat.card k - 1) := by
  have : 1 < Nat.card k := Finite.one_lt_card
  rw [card k, Nat.mul_div_cancel]
  lia

lemma card_of_finrank [Finite k] {n : ℕ} (h : Module.finrank k V = n) :
    Nat.card (ℙ k V) = ∑ i ∈ Finset.range n, Nat.card k ^ i := by
  wlog hf : Finite V
  · have : Infinite (ℙ k V) := by
      contrapose! hf
      rwa [finite_iff_of_finite] at hf
    have : n = 0 := by
      rw [← h]
      apply Module.finrank_of_not_finite
      contrapose hf
      simpa using Module.finite_of_finite k
    simp [this]
  have : 1 < Nat.card k := Finite.one_lt_card
  refine Nat.mul_right_cancel (m := Nat.card k - 1) (by lia) ?_
  let e : V ≃ₗ[k] (Fin n → k) := LinearEquiv.ofFinrankEq _ _ (by simpa)
  have hc : Nat.card V = Nat.card k ^ n := by simp [Nat.card_congr e.toEquiv, Nat.card_fun]
  zify
  conv_rhs => rw [Int.natCast_sub this.le, Int.natCast_one, geom_sum_mul]
  rw [← Int.natCast_mul, ← card k V, hc]
  simp

lemma card_of_finrank_two [Finite k] (h : Module.finrank k V = 2) :
    Nat.card (ℙ k V) = Nat.card k + 1 := by
  simp [card_of_finrank k V h]

end Projectivization
