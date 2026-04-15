/-
Extracted from Algebra/Order/Quantale.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theory of quantales

Quantales are the non-commutative generalization of locales/frames and as such are linked
to point-free topology and order theory. Applications are found throughout logic,
quantum mechanics, and computer science (see e.g. [Vickers1989] and [Mulvey1986]).

The most general definition of quantale occurring in literature, is that a quantale is a semigroup
distributing over a complete sup-semilattice. In our definition below, we use the fact that
every complete sup-semilattice is in fact a complete lattice, and make constructs defined for
those immediately available. Another view could be to define a quantale as a complete idempotent
semiring, i.e. a complete semiring in which + and sup coincide. However, we will often encounter
additive quantales, i.e. quantales in which the semigroup operator is thought of as addition, in
which case the link with semirings will lead to confusion notationally.

In this file, we follow the basic definition set out on the wikipedia page on quantales,
using a mixin typeclass to make the special cases of unital, commutative, idempotent,
integral, and involutive quantales easier to add on later.

## Main definitions

* `IsQuantale` and `IsAddQuantale` : Typeclass mixin for a (additive) semigroup distributing
  over a complete lattice, i.e satisfying `x * (sSup s) = ⨆ y ∈ s, x * y` and
  `(sSup s) * y = ⨆ x ∈ s, x * y`;

* `Quantale` and `AddQuantale` : Structures serving as a typeclass alias, so one can write
  `variable? [Quantale α]` instead of `variable [Semigroup α] [CompleteLattice α] [IsQuantale α]`,
  and similarly for the additive variant.

* `leftMulResiduation`, `rightMulResiduation`, `leftAddResiduation`, `rightAddResiduation` :
  Defining the left- and right- residuations of the semigroup (see notation below).

* Finally, we provide basic distributivity laws for sSup into iSup and sup, monotonicity of
  the semigroup operator, and basic equivalences for left- and right-residuation.

## Notation

* `x ⇨ₗ y` : `sSup {z | z * x ≤ y}`, the `leftMulResiduation` of `y` over `x`;

* `x ⇨ᵣ y` : `sSup {z | x * z ≤ y}`, the `rightMulResiduation` of `y` over `x`;

## References

<https://en.wikipedia.org/wiki/Quantale>
<https://encyclopediaofmath.org/wiki/Quantale>
<https://ncatlab.org/nlab/show/quantale>

-/

open Function

class IsAddQuantale (α : Type*) [AddSemigroup α] [CompleteLattice α] where
  /-- Addition is distributive over join in a quantale -/
  protected add_sSup_distrib (x : α) (s : Set α) : x + sSup s = ⨆ y ∈ s, x + y
  /-- Addition is distributive over join in a quantale -/
  protected sSup_add_distrib (s : Set α) (y : α) : sSup s + y = ⨆ x ∈ s, x + y
