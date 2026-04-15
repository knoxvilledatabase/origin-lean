/-
Extracted from Algebra/BigOperators/Finprod.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite products and sums over types and sets

We define products and sums over types and subsets of types, with no finiteness hypotheses.
All infinite products and sums are defined to be junk values (i.e. one or zero).
This approach is sometimes easier to use than `Finset.sum`,
when issues arise with `Finset` and `Fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
  Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
  it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∏ᶠ i, f i` and `∏ᶠ i : α, f i` for `finprod f`

This notation works for functions `f : p → M`, where `p : Prop`, so the following works:

* `∑ᶠ i ∈ s, f i`, where `f : α → M`, `s : Set α` : sum over the set `s`;
* `∑ᶠ n < 5, f n`, where `f : ℕ → M` : same as `f 0 + f 1 + f 2 + f 3 + f 4`;
* `∏ᶠ (n >= -2) (hn : n < 3), f n`, where `f : ℤ → M` : same as `f (-2) * f (-1) * f 0 * f 1 * f 2`.

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `Finset` and
`Fintype`. By sticking solely to `Set.Finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
functions. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

We did not add `IsFinite (X : Type) : Prop`, because it is simply `Nonempty (Fintype X)`.

## Tags

finsum, finprod, finite sum, finite product
-/

open Function Set

/-!
### Definition and relation to `Finset.sum` and `Finset.prod`
-/

section sort

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

open Classical in

noncomputable irreducible_def finsum (lemma := finsum_def') [AddCommMonoid M] (f : α → M) : M :=
  if h : HasFiniteSupport (f ∘ PLift.down) then ∑ i ∈ h.toFinset, f i.down else 0

open Classical in
