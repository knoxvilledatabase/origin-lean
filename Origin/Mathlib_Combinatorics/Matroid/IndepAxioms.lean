/-
Extracted from Combinatorics/Matroid/IndepAxioms.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matroid Independence and Basis axioms

Matroids in mathlib are defined axiomatically in terms of bases,
but can be described just as naturally via their collections of independent sets,
and in fact such a description, being more 'verbose', can often be useful.
As well as this, the definition of a `Matroid` uses an unwieldy 'maximality'
axiom that can be dropped in cases where there is some finiteness assumption.

This file provides several ways to do define a matroid in terms of its independence or base
predicates, using axiom sets that are appropriate in different settings,
and often much simpler than the general definition.
It also contains `simp` lemmas and typeclasses as appropriate.

All the independence axiom sets need nontriviality (the empty set is independent),
monotonicity (subsets of independent sets are independent),
and some form of 'augmentation' axiom, which allows one to enlarge a non-maximal independent set.
This augmentation axiom is still required when there are finiteness assumptions, but is simpler.
It just states that if `I` is a finite independent set and `J` is a larger finite
independent set, then there exists `e ∈ J \ I` for which `insert e I` is independent.
This is the axiom that appears in most of the definitions.

## Implementation Details

To facilitate building a matroid from its independent sets, we define a structure `IndepMatroid`
which has a ground set `E`, an independence predicate `Indep`, and some axioms as its fields.
This structure is another encoding of the data in a `Matroid`; the function `IndepMatroid.matroid`
constructs a `Matroid` from an `IndepMatroid`.

This is convenient because if one wants to define `M : Matroid α` from a known independence
predicate `Ind`, it is easier to define an `M' : IndepMatroid α` so that `M'.Indep = Ind` and
then set `M = M'.matroid` than it is to directly define `M` with the base axioms.
The simp lemma `IndepMatroid.matroid_indep_iff` is important here; it shows that `M.Indep = Ind`,
so the `Matroid` constructed is the right one, and the intermediate `IndepMatroid` can be
made essentially invisible by the simplifier when working with `M`.

Because of this setup, we don't define any API for `IndepMatroid`, as it would be
a redundant copy of the existing API for `Matroid.Indep`.
(In particular, one could define a natural equivalence `e : IndepMatroid α ≃ Matroid α`
with `e.toFun = IndepMatroid.matroid`, but this would be pointless, as there is no need
for the inverse of `e`).

## Main definitions


* `IndepMatroid α` is a matroid structure on `α` described in terms of its independent sets
  in full generality, using infinite versions of the axioms.

* `IndepMatroid.matroid` turns `M' : IndepMatroid α` into `M : Matroid α` with `M'.Indep = M.Indep`.

* `IndepMatroid.ofFinitary` constructs an `IndepMatroid` whose associated `Matroid` is `Finitary`
  in the special case where independence of a set is determined only by that of its
  finite subsets. This construction uses Zorn's lemma.

* `IndepMatroid.ofFinitaryCardAugment` is a variant of `IndepMatroid.ofFinitary` where the
  augmentation axiom resembles the finite augmentation axiom.

* `IndepMatroid.ofBdd` constructs an `IndepMatroid` in the case where there is some known
  absolute upper bound on the size of an independent set. This uses the infinite version of
  the augmentation axiom; the corresponding `Matroid` is `RankFinite`.

* `IndepMatroid.ofBddAugment` is the same as the above, but with a finite augmentation axiom.

* `IndepMatroid.ofFinite` constructs an `IndepMatroid` from a finite ground set in terms of
  its independent sets.

* `IndepMatroid.ofFinset` constructs an `IndepMatroid α` whose corresponding matroid is `Finitary`
  from an independence predicate on `Finset α`.

* `Matroid.ofExistsMatroid` constructs a 'copy' of a matroid that is known only
  existentially, but whose independence predicate is known explicitly.

* `Matroid.ofExistsFiniteIsBase` constructs a matroid from its bases, if it is known that one
  of them is finite. This gives a `RankFinite` matroid.

* `Matroid.ofIsBaseOfFinite` constructs a `Finite` matroid from its bases.
-/

assert_not_exists Field

open Set Matroid

variable {α : Type*}

section IndepMatroid

structure IndepMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The independence predicate -/
  (Indep : Set α → Prop)
  (indep_empty : Indep ∅)
  (indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
  (indep_aug : ∀ ⦃I B⦄, Indep I → ¬ Maximal Indep I →
    Maximal Indep B → ∃ x ∈ B \ I, Indep (insert x I))
  (indep_maximal : ∀ X, X ⊆ E → ExistsMaximalSubsetProperty Indep X)
  (subset_ground : ∀ I, Indep I → I ⊆ E)

namespace IndepMatroid
