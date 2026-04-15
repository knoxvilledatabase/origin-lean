/-
Extracted from Data/Finsupp/MonomialOrder.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Monomial orders

## Monomial orders

A *monomial order* is well ordering relation on a type of the form `σ →₀ ℕ` which
is compatible with addition and for which `0` is the smallest element.
Since several monomial orders may have to be used simultaneously, one cannot
get them as instances.

In this formalization, they are presented as a structure `MonomialOrder` which encapsulates
`MonomialOrder.toSyn`, an additive and monotone isomorphism to a linearly ordered cancellative
additive commutative monoid.
The entry `MonomialOrder.wf` asserts that `MonomialOrder.syn` is well founded.

The terminology comes from commutative algebra and algebraic geometry, especially Gröbner bases,
where `c : σ →₀ ℕ` are exponents of monomials.

Given a monomial order `m : MonomialOrder σ`, we provide the notation
`c ≼[m] d` and `c ≺[m] d` to compare `c d : σ →₀ ℕ` with respect to `m`.
It is activated using `open scoped MonomialOrder`.

## Examples

Commutative algebra defines many monomial orders, with different usefulness ranges.
In this file, we provide the basic example of lexicographic ordering.
For the graded lexicographic ordering, see `Mathlib/Data/Finsupp/MonomialOrder/DegLex.lean`

* `MonomialOrder.lex` : the lexicographic ordering on `σ →₀ ℕ`.
For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `Lex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.lex_le_iff`
and `MonomialOrder.lex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

## Note

In algebraic geometry, when the finitely many variables are indexed by integers,
it is customary to order them using the opposite order : `MvPolynomial.X 0 > MvPolynomial.X 1 > … `

-/

structure MonomialOrder (σ : Type*) where
  /-- The synonym type -/
  syn : Type*
  /-- `syn` is an additive commutative monoid -/
  acm : AddCommMonoid syn := by infer_instance
  /-- `syn` is linearly ordered -/
  lo : LinearOrder syn := by infer_instance
  /-- `syn` is a linearly ordered cancellative additive commutative monoid -/
  iocam : IsOrderedCancelAddMonoid syn := by infer_instance
  /-- the additive equivalence from `σ →₀ ℕ` to `syn` -/
  toSyn : (σ →₀ ℕ) ≃+ syn
  /-- `toSyn` is monotone -/
  toSyn_monotone : Monotone toSyn
  /-- `syn` is a well ordering -/
  wf : WellFoundedLT syn := by infer_instance

attribute [instance] MonomialOrder.acm MonomialOrder.lo MonomialOrder.iocam MonomialOrder.wf

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)

lemma le_add_right (a b : σ →₀ ℕ) :
    m.toSyn a ≤ m.toSyn a + m.toSyn b := by
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

-- INSTANCE (free from Core): orderBot
