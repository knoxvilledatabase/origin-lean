/-
Extracted from Order/PiLex.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lexicographic order on Pi types

This file defines the lexicographic and colexicographic orders for Pi types.

* In the lexicographic order, `a` is less than `b` if `a i = b i` for all `i` up to some point
  `k`, and `a k < b k`.
* In the colexicographic order, `a` is less than `b` if `a i = b i` for all `i` above some point
  `k`, and `a k < b k`.

## Notation

* `Πₗ i, α i`: Pi type equipped with the lexicographic order. Type synonym of `Π i, α i`.

## See also

Related files are:
* `Data.Finset.Colex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.
-/

assert_not_exists Monoid

variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

namespace Pi

protected def Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

notation3 (prettyPrint := false) "Πₗ " (...) ", " r:(scoped p => Lex (∀ i, p i)) => r

theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min {i | x i < y i} h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩

theorem lex_lt_of_lt [∀ i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt

theorem lex_iff_of_unique [Unique ι] [∀ i, LT (β i)] {r} [Std.Irrefl r] {x y : ∀ i, β i} :
    Pi.Lex r (· < ·) x y ↔ x default < y default := by
  simp [Pi.Lex, Unique.forall_iff, Unique.exists_iff, irrefl]

theorem trichotomous_lex [∀ i, Std.Trichotomous (α := β i) s] (wf : WellFounded r) :
    Std.Trichotomous (Pi.Lex r @s) :=
  { trichotomous a b hab hba := by
      by_contra! h
      rw [Function.ne_iff] at h
      let i := wf.min {i | a i ≠ b i} h
      have hri j (hr : r j i) : a j = b j := not_not.mp (wf.not_lt_min _ · hr)
      have := Std.Trichotomous.trichotomous (a i) (b i) (hab ⟨i, hri, ·⟩)
      exact hba ⟨i, (hri · · |>.symm), Not.imp_symm this <| wf.min_mem {i | a i ≠ b i} h⟩ }
