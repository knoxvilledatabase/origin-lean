/-
Extracted from Algebra/Order/Ring/Defs.lean
Genuine: 8 of 26 | Dissolved: 2 | Infrastructure: 16
-/
import Origin.Core

/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`Semiring`, `CommSemiring`, `Ring`, `CommRing`)
* an order class (`PartialOrder`, `LinearOrder`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `OrderedSemiring`: Semiring with a partial order such that `+` and `*` respect `≤`.
* `StrictOrderedSemiring`: Nontrivial semiring with a partial order such that `+` and `*` respects
  `<`.
* `OrderedCommSemiring`: Commutative semiring with a partial order such that `+` and `*` respect
  `≤`.
* `StrictOrderedCommSemiring`: Nontrivial commutative semiring with a partial order such that `+`
  and `*` respect `<`.
* `OrderedRing`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `OrderedCommRing`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedSemiring`: Nontrivial semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `LinearOrderedCommSemiring`: Nontrivial commutative semiring with a linear order such that `+`
  respects `≤` and `*` respects `<`.
* `LinearOrderedRing`: Nontrivial ring with a linear order such that `+` respects `≤` and `*`
  respects `<`.
* `LinearOrderedCommRing`: Nontrivial commutative ring with a linear order such that `+` respects
  `≤` and `*` respects `<`.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `OrderedSemiring`
  - `OrderedAddCommMonoid` & multiplication & `*` respects `≤`
  - `Semiring` & partial order structure & `+` respects `≤` & `*` respects `≤`
* `StrictOrderedSemiring`
  - `OrderedCancelAddCommMonoid` & multiplication & `*` respects `<` & nontriviality
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommSemiring`
  - `OrderedSemiring` & commutativity of multiplication
  - `CommSemiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommSemiring`
  - `StrictOrderedSemiring` & commutativity of multiplication
  - `OrderedCommSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedRing`
  - `OrderedSemiring` & additive inverses
  - `OrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedRing`
  - `StrictOrderedSemiring` & additive inverses
  - `OrderedSemiring` & `+` respects `<` & `*` respects `<` & nontriviality
* `OrderedCommRing`
  - `OrderedRing` & commutativity of multiplication
  - `OrderedCommSemiring` & additive inverses
  - `CommRing` & partial order structure & `+` respects `≤` & `*` respects `<`
* `StrictOrderedCommRing`
  - `StrictOrderedCommSemiring` & additive inverses
  - `StrictOrderedRing` & commutativity of multiplication
  - `OrderedCommRing` & `+` respects `<` & `*` respects `<` & nontriviality
* `LinearOrderedSemiring`
  - `StrictOrderedSemiring` & totality of the order
  - `LinearOrderedAddCommMonoid` & multiplication & nontriviality & `*` respects `<`
* `LinearOrderedCommSemiring`
  - `StrictOrderedCommSemiring` & totality of the order
  - `LinearOrderedSemiring` & commutativity of multiplication
* `LinearOrderedRing`
  - `StrictOrderedRing` & totality of the order
  - `LinearOrderedSemiring` & additive inverses
  - `LinearOrderedAddCommGroup` & multiplication & `*` respects `<`
  - `Ring` & `IsDomain` & linear order structure
* `LinearOrderedCommRing`
  - `StrictOrderedCommRing` & totality of the order
  - `LinearOrderedRing` & commutativity of multiplication
  - `LinearOrderedCommSemiring` & additive inverses
  - `CommRing` & `IsDomain` & linear order structure
-/

assert_not_exists MonoidHom

open Function

universe u

variable {R : Type u}

class IsOrderedRing (R : Type*) [Semiring R] [PartialOrder R] extends
    IsOrderedAddMonoid R, ZeroLEOneClass R, PosMulMono R, MulPosMono R where

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): 200]

-- INSTANCE (free from Core): 200]

class IsStrictOrderedRing (R : Type*) [Semiring R] [PartialOrder R] extends
    IsOrderedCancelAddMonoid R, ZeroLEOneClass R, Nontrivial R, PosMulStrictMono R,
    MulPosStrictMono R where

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): 200]

-- INSTANCE (free from Core): 200]

-- INSTANCE (free from Core): [Semiring

lemma IsOrderedRing.of_mul_nonneg [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ZeroLEOneClass R] (mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b) :
    IsOrderedRing R where
  mul_le_mul_of_nonneg_left a ha b c hbc := by
    simpa only [mul_sub, sub_nonneg] using mul_nonneg _ _ ha (sub_nonneg.2 hbc)
  mul_le_mul_of_nonneg_right a ha b c hbc := by
    simpa only [sub_mul, sub_nonneg] using mul_nonneg _ _ (sub_nonneg.2 hbc) ha

lemma IsStrictOrderedRing.of_mul_pos [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ZeroLEOneClass R] [Nontrivial R] (mul_pos : ∀ a b : R, 0 < a → 0 < b → 0 < a * b) :
    IsStrictOrderedRing R where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simpa only [mul_sub, sub_pos] using mul_pos _ _ ha (sub_pos.2 hbc)
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [sub_mul, sub_pos] using mul_pos _ _ (sub_pos.2 hbc) ha

-- INSTANCE (free from Core): (priority

section IsStrictOrderedRing

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

-- INSTANCE (free from Core): (priority

-- DISSOLVED: AddMonoidWithOne.toCharZero

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end IsStrictOrderedRing

section LinearOrder

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end LinearOrder

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/

section OrderedRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R] {a b c : R}

lemma one_add_le_one_sub_mul_one_add (h : a + b + b * c ≤ c) : 1 + a ≤ (1 - b) * (1 + c) := by
  rw [one_sub_mul, mul_one_add, le_sub_iff_add_le, add_assoc, ← add_assoc a]
  gcongr

lemma one_add_le_one_add_mul_one_sub (h : a + c + b * c ≤ b) : 1 + a ≤ (1 + b) * (1 - c) := by
  rw [mul_one_sub, one_add_mul, le_sub_iff_add_le, add_assoc, ← add_assoc a]
  gcongr

lemma one_sub_le_one_sub_mul_one_add (h : b + b * c ≤ a + c) : 1 - a ≤ (1 - b) * (1 + c) := by
  rw [one_sub_mul, mul_one_add, sub_le_sub_iff, add_assoc, add_comm c]
  gcongr

lemma one_sub_le_one_add_mul_one_sub (h : c + b * c ≤ a + b) : 1 - a ≤ (1 + b) * (1 - c) := by
  rw [mul_one_sub, one_add_mul, sub_le_sub_iff, add_assoc, add_comm b]
  gcongr

-- DISSOLVED: IsOrderedRing.toCharZero

-- INSTANCE (free from Core): [Nontrivial

-- INSTANCE (free from Core): [Nontrivial

end OrderedRing
