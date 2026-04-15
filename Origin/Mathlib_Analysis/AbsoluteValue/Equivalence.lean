/-
Extracted from Analysis/AbsoluteValue/Equivalence.lean
Genuine: 13 of 15 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Equivalence of real-valued absolute values

Two absolute values `v₁, v₂ : AbsoluteValue R ℝ` are *equivalent* if there exists a
positive real number `c` such that `v₁ x ^ c = v₂ x` for all `x : R`.
-/

namespace AbsoluteValue

section OrderedSemiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S]
  (v w : AbsoluteValue R S)

def IsEquiv : Prop := ∀ x y, v x ≤ v y ↔ w x ≤ w y

theorem IsEquiv.refl : v.IsEquiv v := fun _ _ ↦ .rfl

variable {v w}

theorem IsEquiv.rfl : v.IsEquiv v := fun _ _ ↦ .rfl

theorem IsEquiv.symm (h : v.IsEquiv w) : w.IsEquiv v := fun _ _ ↦ (h _ _).symm

theorem IsEquiv.trans {u : AbsoluteValue R S} (h₁ : v.IsEquiv w)
    (h₂ : w.IsEquiv u) : v.IsEquiv u := fun _ _ ↦ (h₁ _ _).trans (h₂ _ _)

-- INSTANCE (free from Core): :

theorem IsEquiv.lt_iff_lt (h : v.IsEquiv w) {x y : R} : v x < v y ↔ w x < w y :=
  lt_iff_lt_of_le_iff_le' (h y x) (h x y)

theorem IsEquiv.eq_iff_eq (h : v.IsEquiv w) {x y : R} : v x = v y ↔ w x = w y := by
  simp [le_antisymm_iff, h x y, h y x]

variable [IsDomain S] [Nontrivial R]

theorem IsEquiv.lt_one_iff (h : v.IsEquiv w) {x : R} :
    v x < 1 ↔ w x < 1 := by
  simpa only [map_one] using h.lt_iff_lt (y := 1)

theorem IsEquiv.one_lt_iff (h : v.IsEquiv w) {x : R} :
    1 < v x ↔ 1 < w x := by
  simpa only [map_one] using h.lt_iff_lt (x := 1)

theorem IsEquiv.le_one_iff (h : v.IsEquiv w) {x : R} :
    v x ≤ 1 ↔ w x ≤ 1 := by
  simpa only [map_one] using h x 1

theorem IsEquiv.one_le_iff (h : v.IsEquiv w) {x : R} :
    1 ≤ v x ↔ 1 ≤ w x := by
  simpa only [map_one] using h 1 x

theorem IsEquiv.eq_one_iff (h : v.IsEquiv w) {x : R} : v x = 1 ↔ w x = 1 := by
  simpa only [map_one] using h.eq_iff_eq (x := x) (y := 1)

theorem IsEquiv.isNontrivial_congr {w : AbsoluteValue R S} (h : v.IsEquiv w) :
    v.IsNontrivial ↔ w.IsNontrivial :=
  not_iff_not.1 <| by aesop (add simp [not_isNontrivial_iff, h.eq_one_iff])

alias ⟨IsEquiv.isNontrivial, _⟩ := IsEquiv.isNontrivial_congr

end OrderedSemiring

section LinearOrderedSemifield

variable {R S : Type*} [Field R] [Semifield S] [LinearOrder S] {v w : AbsoluteValue R S}
