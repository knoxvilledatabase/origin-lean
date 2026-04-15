/-
Extracted from Algebra/Order/Floor/Div.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Flooring, ceiling division

This file defines division rounded up and down.

The setup is an ordered monoid `α` acting on an ordered monoid `β`. If `a : α`, `b : β`, we would
like to be able to "divide" `b` by `a`, namely find `c : β` such that `a • c = b`.
This is of course not always possible, but in some cases at least there is a least `c` such that
`b ≤ a • c` and a greatest `c` such that `a • c ≤ b`. We call the first one the "ceiling division
of `b` by `a`" and the second one the "flooring division of `b` by `a`"

If `α` and `β` are both `ℕ`, then one can check that our flooring and ceiling divisions really are
the floor and ceil of the exact division.
If `α` is `ℕ` and `β` is the functions `ι → ℕ`, then the flooring and ceiling divisions are taken
pointwise.

In order theory terms, those operations are respectively the right and left adjoints to the map
`b ↦ a • b`.

## Main declarations

* `FloorDiv`: Typeclass for the existence of a flooring division, denoted `b ⌊/⌋ a`.
* `CeilDiv`: Typeclass for the existence of a ceiling division, denoted `b ⌈/⌉ a`.

Note in both cases we only allow dividing by positive inputs. We enforce the following junk values:
* `b ⌊/⌋ a = b ⌈/⌉ a = 0` if `a ≤ 0`
* `0 ⌊/⌋ a = 0 ⌈/⌉ a = 0`

## Notation

* `b ⌊/⌋ a` for the flooring division of `b` by `a`
* `b ⌈/⌉ a` for the ceiling division of `b` by `a`

## TODO

* `norm_num` extension
* Prove `⌈a / b⌉ = a ⌈/⌉ b` when `a, b : ℕ`
-/

variable {ι α β : Type*}

section OrderedAddCommMonoid

variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

class FloorDiv where
  /-- Flooring division. If `a > 0`, then `b ⌊/⌋ a` is the greatest `c` such that `a • c ≤ b`. -/
  floorDiv : β → α → β
  /-- Do not use this. Use `gc_floorDiv_smul` or `gc_floorDiv_mul` instead. -/
  protected floorDiv_gc ⦃a⦄ : 0 < a → GaloisConnection (a • ·) (floorDiv · a)
  /-- Do not use this. Use `floorDiv_nonpos` instead. -/
  protected floorDiv_nonpos ⦃a⦄ : a ≤ 0 → ∀ b, floorDiv b a = 0
  /-- Do not use this. Use `zero_floorDiv` instead. -/
  protected zero_floorDiv (a) : floorDiv 0 a = 0

class CeilDiv where
  /-- Ceiling division. If `a > 0`, then `b ⌈/⌉ a` is the least `c` such that `b ≤ a • c`. -/
  ceilDiv : β → α → β
  /-- Do not use this. Use `gc_smul_ceilDiv` or `gc_mul_ceilDiv` instead. -/
  protected ceilDiv_gc ⦃a⦄ : 0 < a → GaloisConnection (ceilDiv · a) (a • ·)
  /-- Do not use this. Use `ceilDiv_nonpos` instead. -/
  protected ceilDiv_nonpos ⦃a⦄ : a ≤ 0 → ∀ b, ceilDiv b a = 0
  /-- Do not use this. Use `zero_ceilDiv` instead. -/
  protected zero_ceilDiv (a) : ceilDiv 0 a = 0
