/-
Extracted from Algebra/Homology/ComplexShapeSigns.lean
Genuine: 16 of 16 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! Signs in constructions on homological complexes

In this file, we shall introduce various typeclasses which will allow
the construction of the total complex of a bicomplex and of the
monoidal category structure on categories of homological complexes (TODO).

The most important definition is that of `TotalComplexShape c₁ c₂ c₁₂` given
three complex shapes `c₁`, `c₂`, `c₁₂`: it allows the definition of a total
complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂` (at least
when suitable coproducts exist).

In particular, we construct an instance of `TotalComplexShape c c c` when `c : ComplexShape I`
and `I` is an additive monoid equipped with a group homomorphism `ε' : Multiplicative I → ℤˣ`
satisfying certain properties (see `ComplexShape.TensorSigns`).

-/

assert_not_exists Field TwoSidedIdeal

variable {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₃ : ComplexShape I₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)

class TotalComplexShape where
  /-- a map on indices -/
  π : I₁ × I₂ → I₁₂
  /-- the sign of the horizontal differential in the total complex -/
  ε₁ : I₁ × I₂ → ℤˣ
  /-- the sign of the vertical differential in the total complex -/
  ε₂ : I₁ × I₂ → ℤˣ
  rel₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂]

abbrev π (i : I₁ × I₂) : I₁₂ := TotalComplexShape.π c₁ c₂ c₁₂ i

abbrev ε₁ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₁ c₁ c₂ c₁₂ i

abbrev ε₂ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₂ c₁ c₂ c₁₂ i

variable {c₁}

lemma rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) :=
  TotalComplexShape.rel₁ h i₂

lemma next_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  c₁₂.next_eq' (rel_π₁ c₂ c₁₂ h i₂)

lemma prev_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₁ c₂ c₁₂ h i₂)

variable (c₁) {c₂}

lemma rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) :=
  TotalComplexShape.rel₂ i₁ h

lemma next_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  c₁₂.next_eq' (rel_π₂ c₁ c₁₂ i₁ h)

lemma prev_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₂ c₁ c₁₂ i₁ h)

variable {c₁}

lemma ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ =
      - ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  TotalComplexShape.ε₂_ε₁ h₁ h₂

lemma ε₁_ε₂ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ =
      - ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  Eq.trans (mul_one _).symm (by
    rw [← Int.units_mul_self (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂')), mul_assoc]
    conv_lhs =>
      arg 2
      rw [← mul_assoc, ε₂_ε₁ c₁₂ h₁ h₂]
    rw [neg_mul, neg_mul, neg_mul, mul_neg, neg_inj, ← mul_assoc, ← mul_assoc,
      Int.units_mul_self, one_mul])

variable {I : Type*} [AddMonoid I] (c : ComplexShape I)

class TensorSigns where
  /-- the signs which appear in the vertical differential of the total complex -/
  ε' : Multiplicative I →* ℤˣ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε'_succ (p q : I) (hpq : c.Rel p q) : ε' q = - ε' p

variable [TensorSigns c]

abbrev ε (i : I) : ℤˣ := TensorSigns.ε' c i

lemma rel_add {p q : I} (hpq : c.Rel p q) (r : I) : c.Rel (p + r) (q + r) :=
  TensorSigns.rel_add _ _ _ hpq

lemma add_rel (r : I) {p q : I} (hpq : c.Rel p q) : c.Rel (r + p) (r + q) :=
  TensorSigns.add_rel _ _ _ hpq
