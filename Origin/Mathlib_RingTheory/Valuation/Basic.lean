/-
Extracted from RingTheory/Valuation/Basic.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative monoid with zero, that in addition satisfies the following two axioms:
* `v 0 = 0`
* `∀ x y, v (x + y) ≤ max (v x) (v y)`

`Valuation R Γ₀` is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `Units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `IsEquiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : Valuation R Γ₁` and `v₂ : Valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

## Main definitions

* `Valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `Valuation.IsNontrivial` is the class of non-trivial valuations, namely those for which there
  is an element in the ring whose valuation is `≠ 0` and `≠ 1`.
* `Valuation.IsEquiv`, the heterogeneous equivalence relation on valuations
* `Valuation.supp`, the support of a valuation
* `orderMonoidIso` is the ordered isomorphism between the value groups of two equivalent valuations.

* `AddValuation R Γ₀`, the type of additive valuations on `R` with values in a
  linearly ordered additive commutative group with a top element, `Γ₀`.

## Implementation Details

`AddValuation R Γ₀` is implemented as `Valuation R (Multiplicative Γ₀)ᵒᵈ`.

## Notation

In the `WithZero` locale, `Mᵐ⁰` is a shorthand for `WithZero (Multiplicative M)`.

## TODO

If ever someone extends `Valuation`, we should fully comply with `DFunLike` by migrating the
boilerplate lemmas to `ValuationClass`.
-/

open Function Ideal

noncomputable section

variable {K F R : Type*} [DivisionRing K]

variable (F R) (Γ₀ : Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]

structure Valuation extends R →*₀ Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)

class ValuationClass (F) (R Γ₀ : outParam Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]
    [FunLike F R Γ₀] : Prop
  extends MonoidWithZeroHomClass F R Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max (f : F) (x y : R) : f (x + y) ≤ max (f x) (f y)

export ValuationClass (map_add_le_max)

-- INSTANCE (free from Core): [FunLike

end

namespace Valuation

variable {Γ₀ : Type*} {Γ'₀ : Type*} {Γ''₀ : Type*}

section Basic

variable [Ring R]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  [LinearOrderedCommMonoidWithZero Γ''₀]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
