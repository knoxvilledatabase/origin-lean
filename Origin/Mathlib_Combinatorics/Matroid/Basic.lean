/-
Extracted from Combinatorics/Matroid/Basic.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Matroids

A `Matroid` is a structure that combinatorially abstracts
the notion of linear independence and dependence;
matroids have connections with graph theory, discrete optimization,
additive combinatorics and algebraic geometry.
Mathematically, a matroid `M` is a structure on a set `E` comprising a
collection of subsets of `E` called the bases of `M`,
where the bases are required to obey certain axioms.

This file gives a definition of a matroid `M` in terms of its bases,
and some API relating independent sets (subsets of bases) and the notion of a
basis of a set `X` (a maximal independent subset of `X`).

## Main definitions

* a `Matroid α` on a type `α` is a structure comprising a 'ground set'
  and a suitably behaved 'base' predicate.

Given `M : Matroid α` ...

* `M.E` denotes the ground set of `M`, which has type `Set α`
* For `B : Set α`, `M.IsBase B` means that `B` is a base of `M`.
* For `I : Set α`, `M.Indep I` means that `I` is independent in `M`
    (that is, `I` is contained in a base of `M`).
* For `D : Set α`, `M.Dep D` means that `D` is contained in the ground set of `M`
    but isn't independent.
* For `I : Set α` and `X : Set α`, `M.IsBasis I X` means that `I` is a maximal independent
    subset of `X`.
* `M.Finite` means that `M` has finite ground set.
* `M.Nonempty` means that the ground set of `M` is nonempty.
* `RankFinite M` means that the bases of `M` are finite.
* `RankInfinite M` means that the bases of `M` are infinite.
* `RankPos M` means that the bases of `M` are nonempty.
* `Finitary M` means that a set is independent if and only if all its finite subsets are
    independent.

* `aesop_mat` : a tactic designed to prove `X ⊆ M.E` for some set `X` and matroid `M`.

## Implementation details

There are a few design decisions worth discussing.

### Finiteness
  The first is that our matroids are allowed to be infinite.
  Unlike with many mathematical structures, this isn't such an obvious choice.
  Finite matroids have been studied since the 1930's,
  and there was never controversy as to what is and isn't an example of a finite matroid -
  in fact, surprisingly many apparently different definitions of a matroid
  give rise to the same class of objects.

  However, generalizing different definitions of a finite matroid
  to the infinite in the obvious way (i.e. by simply allowing the ground set to be infinite)
  gives a number of different notions of 'infinite matroid' that disagree with each other,
  and that all lack nice properties.
  Many different competing notions of infinite matroid were studied through the years;
  in fact, the problem of which definition is the best was only really solved in 2013,
  when Bruhn et al. [2] showed that there is a unique 'reasonable' notion of an infinite matroid
  (these objects had previously defined by Higgs under the name 'B-matroid').
  These are defined by adding one carefully chosen axiom to the standard set,
  and adapting existing axioms to not mention set cardinalities;
  they enjoy nearly all the nice properties of standard finite matroids.

  Even though at least 90% of the literature is on finite matroids,
  B-matroids are the definition we use, because they allow for additional generality,
  nearly all theorems are still true and just as easy to state,
  and (hopefully) the more general definition will prevent the need for a costly future refactor.
  The disadvantage is that developing API for the finite case is harder work
  (for instance, it is harder to prove that something is a matroid in the first place,
  and one must deal with `ℕ∞` rather than `ℕ`).
  For serious work on finite matroids, we provide the typeclasses
  `[M.Finite]` and `[RankFinite M]` and associated API.

### Cardinality
  Just as with bases of a vector space,
  all bases of a finite matroid `M` are finite and have the same cardinality;
  this cardinality is an important invariant known as the 'rank' of `M`.
  For infinite matroids, bases are not in general equicardinal;
  in fact the equicardinality of bases of infinite matroids is independent of ZFC [3].
  What is still true is that either all bases are finite and equicardinal,
  or all bases are infinite. This means that the natural notion of 'size'
  for a set in matroid theory is given by the function `Set.encard`, which
  is the cardinality as a term in `ℕ∞`. We use this function extensively
  in building the API; it is preferable to both `Set.ncard` and `Finset.card`
  because it allows infinite sets to be handled without splitting into cases.

### The ground `Set`
  A last place where we make a consequential choice is making the ground set of a matroid
  a structure field of type `Set α` (where `α` is the type of 'possible matroid elements')
  rather than just having a type `α` of all the matroid elements.
  This is because of how common it is to simultaneously consider
  a number of matroids on different but related ground sets.
  For example, a matroid `M` on ground set `E` can have its structure
  'restricted' to some subset `R ⊆ E` to give a smaller matroid `M ↾ R` with ground set `R`.
  A statement like `(M ↾ R₁) ↾ R₂ = M ↾ R₂` is mathematically obvious.
  But if the ground set of a matroid is a type, this doesn't typecheck,
  and is only true up to canonical isomorphism.
  Restriction is just the tip of the iceberg here;
  one can also 'contract' and 'delete' elements and sets of elements
  in a matroid to give a smaller matroid,
  and in practice it is common to make statements like `M₁.E = M₂.E ∩ M₃.E` and
  `((M ⟋ e) ↾ R) ⟋ C = M ⟋ (C ∪ {e}) ↾ R`.
  Such things are a nightmare to work with unless `=` is actually propositional equality
  (especially because the relevant coercions are usually between sets and not just elements).

  So the solution is that the ground set `M.E` has type `Set α`,
  and there are elements of type `α` that aren't in the matroid.
  The tradeoff is that for many statements, one now has to add
  hypotheses of the form `X ⊆ M.E` to make sure than `X` is actually 'in the matroid',
  rather than letting a 'type of matroid elements' take care of this invisibly.
  It still seems that this is worth it.
  The tactic `aesop_mat` exists specifically to discharge such goals
  with minimal fuss (using default values).
  The tactic works fairly well, but has room for improvement.

  A related decision is to not have matroids themselves be a typeclass.
  This would make things be notationally simpler
  (having `Base` in the presence of `[Matroid α]` rather than `M.Base` for a term `M : Matroid α`)
  but is again just too awkward when one has multiple matroids on the same type.
  In fact, in regular written mathematics,
  it is normal to explicitly indicate which matroid something is happening in,
  so our notation mirrors common practice.

### Notation
  We use a few nonstandard conventions in theorem names that are related to the above.
  First, we mirror common informal practice by referring explicitly to the `ground` set rather
  than the notation `E`. (Writing `ground` everywhere in a proof term would be unwieldy, and
  writing `E` in theorem names would be unnatural to read.)

  Second, because we are typically interested in subsets of the ground set `M.E`,
  using `Set.compl` is inconvenient, since `Xᶜ ⊆ M.E` is typically false for `X ⊆ M.E`.
  On the other hand (especially when duals arise), it is common to complement
  a set `X ⊆ M.E` *within* the ground set, giving `M.E \ X`.
  For this reason, we use the term `compl` in theorem names to refer to taking a set difference
  with respect to the ground set, rather than a complement within a type. The lemma
  `compl_isBase_dual` is one of the many examples of this.

  Finally, in theorem names, matroid predicates that apply to sets
  (such as `Base`, `Indep`, `IsBasis`) are typically used as suffixes rather than prefixes.
  For instance, we have `ground_indep_iff_isBase` rather than `indep_ground_iff_isBase`.

## References

* [J. Oxley, Matroid Theory][oxley2011]
* [H. Bruhn, R. Diestel, M. Kriesell, R. Pendavingh, P. Wollan, Axioms for infinite matroids,
  Adv. Math 239 (2013), 18-46][bruhnDiestelKriesellPendavinghWollan2013]
* [N. Bowler, S. Geschke, Self-dual uniform matroids on infinite sets,
  Proc. Amer. Math. Soc. 144 (2016), 459-471][bowlerGeschke2015]
-/

assert_not_exists Field

open Set

def Matroid.ExchangeProperty {α : Type*} (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

def Matroid.ExistsMaximalSubsetProperty {α : Type*} (P : Set α → Prop) (X : Set α) : Prop :=
  ∀ I, P I → I ⊆ X → ∃ J, I ⊆ J ∧ Maximal (fun K ↦ P K ∧ K ⊆ X) J

structure Matroid (α : Type*) where
  /-- `M` has a ground set `E`. -/
  (E : Set α)
  /-- `M` has a predicate `Base` defining its bases. -/
  (IsBase : Set α → Prop)
  /-- `M` has a predicate `Indep` defining its independent sets. -/
  (Indep : Set α → Prop)
  /-- The `Indep`endent sets are those contained in `Base`s. -/
  (indep_iff' : ∀ ⦃I⦄, Indep I ↔ ∃ B, IsBase B ∧ I ⊆ B)
  /-- There is at least one `Base`. -/
  (exists_isBase : ∃ B, IsBase B)
  /-- For any bases `B`, `B'` and `e ∈ B \ B'`, there is some `f ∈ B' \ B` for which `B-e+f`
  is a base. -/
  (isBase_exchange : Matroid.ExchangeProperty IsBase)
  /-- Every independent subset `I` of a set `X` for is contained in a maximal independent
  subset of `X`. -/
  (maximality : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  /-- Every base is contained in the ground set. -/
  (subset_ground : ∀ B, IsBase B → B ⊆ E)

attribute [local ext] Matroid

namespace Matroid

variable {α : Type*} {M : Matroid α}

-- INSTANCE (free from Core): (M
