/-
Extracted from RingTheory/Multiplicity.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multiplicity of a divisor

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `emultiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
  number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
  `n`.
* `multiplicity a b`: a `ℕ`-valued version of `multiplicity`, defaulting for `1` instead of `⊤`.
  The reason for using `1` as a default value instead of `0` is to have `multiplicity_eq_zero_iff`.
* `FiniteMultiplicity a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/

assert_not_exists Field

variable {α β : Type*}

open Nat

abbrev FiniteMultiplicity [Monoid α] (a b : α) : Prop :=
  ∃ n : ℕ, ¬a ^ (n + 1) ∣ b

open scoped Classical in

noncomputable def emultiplicity [Monoid α] (a b : α) : ℕ∞ :=
  if h : FiniteMultiplicity a b then Nat.find h else ⊤

noncomputable def multiplicity [Monoid α] (a b : α) : ℕ :=
  (emultiplicity a b).untopD 1

section Monoid

variable [Monoid α] [Monoid β] {a b : α}
