/-
Extracted from SetTheory/Ordinal/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Ordinals

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `Ordinal`: the type of ordinals (in a given universe)
* `Ordinal.type r`: given a well-founded order `r`, this is the corresponding ordinal
* `Ordinal.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r ⟨o, h⟩`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `Ordinal.card o`: the cardinality of an ordinal `o`.
* `Ordinal.lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `Ordinal.liftInitialSeg`.
  For a version registering that it is a principal segment embedding if `u < v`, see
  `Ordinal.liftPrincipalSeg`.
* `Ordinal.omega0` or `ω` is the order type of `ℕ`. It is called this to match `Cardinal.aleph0`
  and so that the omega function can be named `Ordinal.omega`. This definition is universe
  polymorphic: `Ordinal.omega0.{u} : Ordinal.{u}` (contrast with `ℕ : Type`, which lives in
  a specific universe). In some cases the universe level has to be given explicitly.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
  The main properties of addition (and the other operations on ordinals) are stated and proved in
  `Mathlib/SetTheory/Ordinal/Arithmetic.lean`.
  Here, we only introduce it and prove its basic properties to deduce the fact that the order on
  ordinals is total (and well founded).
* `succ o` is the successor of the ordinal `o`.
* `Cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

A conditionally complete linear order with bot structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notation

* `ω` is a notation for the first infinite ordinal in the scope `Ordinal`.
-/

assert_not_exists Module Field

noncomputable section

open Function Cardinal Set Equiv Order

open scoped Cardinal InitialSeg

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Definition of ordinals -/

structure WellOrder : Type (u + 1) where
  /-- The underlying type of the order. -/
  α : Type u
  /-- The underlying relation of the order. -/
  r : α → α → Prop
  /-- The proposition that `r` is a well-ordering for `α`. -/
  wo : IsWellOrder α r

attribute [instance] WellOrder.wo

namespace WellOrder

-- INSTANCE (free from Core): inhabited

end WellOrder

-- INSTANCE (free from Core): Ordinal.isEquivalent
