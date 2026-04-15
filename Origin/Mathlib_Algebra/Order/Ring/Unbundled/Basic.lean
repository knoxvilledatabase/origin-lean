/-
Extracted from Algebra/Order/Ring/Unbundled/Basic.lean
Genuine: 46 of 47 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic facts for ordered rings and semirings

This file develops the basics of ordered (semi)rings in an unbundled fashion for later use with
the bundled classes from `Mathlib/Algebra/Order/Ring/Defs.lean`.

The set of typeclass variables here comprises
* an algebraic class (`Semiring`, `CommSemiring`, `Ring`, `CommRing`)
* an order class (`PartialOrder`, `LinearOrder`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`+` respects `<`" means "strict monotonicity of addition"
* "`*` respects `≤`" means "monotonicity of multiplication by a nonnegative number".
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses found in `Algebra.Order.Ring.Defs`

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
* `CanonicallyOrderedCommSemiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

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

## Generality

Each section is labelled with a corresponding bundled ordered ring typeclass in mind. Mixins for
relating the order structures and ring structures are added as needed.

TODO: the mixin assumptions can be relaxed in most cases

-/

assert_not_exists IsOrderedMonoid MonoidHom

open Function

universe u

variable {R : Type u} {α : Type*}

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/

theorem add_one_le_two_mul [LE R] [NonAssocSemiring R] [AddLeftMono R] {a : R}
    (a1 : 1 ≤ a) : a + 1 ≤ 2 * a :=
  calc
    a + 1 ≤ a + a := by gcongr
    _ = 2 * a := (two_mul _).symm

section OrderedSemiring

variable [Semiring R] [Preorder R] {a b c d : R}

theorem add_le_mul_two_add [ZeroLEOneClass R] [MulPosMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
  calc
    a + (2 + b) ≤ a + (a + a * b) := by
      gcongr; exact le_mul_of_one_le_left b0 <| one_le_two.trans a2
    _ ≤ a * (2 + b) := by rw [mul_add, mul_two, add_assoc]

theorem mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ ≤ d * a := by gcongr; exact hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

theorem mul_le_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ ≤ a * d := by gcongr; exact hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

theorem mul_nonneg_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

theorem mul_le_mul_of_nonneg_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (hc : 0 ≤ c) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| by gcongr; assumption

theorem mul_le_mul_of_nonneg_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd

theorem mul_le_mul_of_nonpos_of_nonneg [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hac : a ≤ c) (hdb : d ≤ b) (hc : c ≤ 0) (hb : 0 ≤ b) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_right hac hb).trans <| mul_le_mul_of_nonpos_left hdb hc

theorem mul_le_mul_of_nonpos_of_nonneg' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd

theorem mul_le_mul_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≤ 0) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonpos_left hdb hc

theorem mul_le_mul_of_nonpos_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≤ 0) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_left hdb ha).trans <| mul_le_mul_of_nonpos_right hca hd

theorem le_mul_of_le_one_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b ≤ 0) (h : a ≤ 1) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

theorem mul_le_of_one_le_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b ≤ 0) (h : 1 ≤ a) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

theorem le_mul_of_le_one_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : b ≤ 1) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

theorem mul_le_of_one_le_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : 1 ≤ b) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

section Monotone

variable [Preorder α] {f g : α → R}

theorem antitone_mul_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone (a * ·) := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

theorem antitone_mul_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone fun x => x * a := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

theorem Monotone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => a * f x :=
  (antitone_mul_left ha).comp_monotone hf

theorem Monotone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => f x * a :=
  (antitone_mul_right ha).comp_monotone hf

theorem Antitone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => a * f x :=
  (antitone_mul_left ha).comp hf

theorem Antitone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => f x * a :=
  (antitone_mul_right ha).comp hf

theorem Antitone.mul_monotone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Monotone g) (hf₀ : ∀ x, f x ≤ 0)
    (hg₀ : ∀ x, 0 ≤ g x) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)

theorem Monotone.mul_antitone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (hg : Antitone g) (hf₀ : ∀ x, 0 ≤ f x)
    (hg₀ : ∀ x, g x ≤ 0) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

theorem Antitone.mul [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Antitone g) (hf₀ : ∀ x, f x ≤ 0) (hg₀ : ∀ x, g x ≤ 0) :
    Monotone (f * g) := fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

end Monotone

end OrderedSemiring

section OrderedCommRing

section StrictOrderedSemiring

variable [Semiring R] [PartialOrder R] {a b c d : R}

-- DISSOLVED: lt_two_mul_self

theorem mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : c * a < c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ < d * a := mul_lt_mul_of_pos_left h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

theorem mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : a * c < b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ < a * d := mul_lt_mul_of_pos_right h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

theorem mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b : R} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

theorem lt_mul_of_lt_one_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

theorem mul_lt_of_one_lt_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

theorem lt_mul_of_lt_one_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

theorem mul_lt_of_one_lt_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

section Monotone

variable [Preorder α] {f : α → R}

theorem strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti (a * ·) := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha

theorem strictAnti_mul_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

theorem StrictMono.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => a * f x :=
  (strictAnti_mul_left ha).comp_strictMono hf

theorem StrictMono.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => f x * a :=
  (strictAnti_mul_right ha).comp_strictMono hf

theorem StrictAnti.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => a * f x :=
  (strictAnti_mul_left ha).comp hf

theorem StrictAnti.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => f x * a :=
  (strictAnti_mul_right ha).comp hf

end Monotone

lemma mul_add_mul_le_mul_add_mul [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  gcongr
  assumption

lemma mul_add_mul_le_mul_add_mul' [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hba : b ≤ a) (hdc : d ≤ c) : a * d + b * c ≤ a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

variable [AddLeftReflectLT R]

lemma mul_add_mul_lt_mul_add_mul [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  gcongr
  exact hd

lemma mul_add_mul_lt_mul_add_mul' [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hba : b < a) (hdc : d < c) : a * d + b * c < a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

end StrictOrderedSemiring

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
    [MulPosStrictMono R] [PosMulStrictMono R]
    (hab : 0 ≤ a * b) : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine Decidable.or_iff_not_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_ge hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)

theorem nonneg_of_mul_nonneg_left [MulPosStrictMono R]
    (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
  le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_ge h

theorem nonneg_of_mul_nonneg_right [PosMulStrictMono R]
    (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
  le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_ge h

theorem nonpos_of_mul_nonpos_left [PosMulStrictMono R]
    (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
  le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_ge h

theorem nonpos_of_mul_nonpos_right [PosMulStrictMono R]
    (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
  le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_ge h
