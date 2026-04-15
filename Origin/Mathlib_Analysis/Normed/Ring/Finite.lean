/-
Extracted from Analysis/Normed/Ring/Finite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite order elements in normed rings.

A finite order element in a normed ring has norm 1.

The values of additive characters on finite cancellative monoids have norm 1.

-/

variable {α β : Type*}

section NormedRing

variable [NormedRing α] [NormMulClass α] [NormOneClass α] {a : α}

protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
  ((normHom : α →*₀ ℝ).toMonoidHom.isOfFinOrder ha).eq_one <| norm_nonneg _

example [Monoid β] (φ : β →* α) {x : β} {k : ℕ+} (h : x ^ (k : ℕ) = 1) :

    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one
