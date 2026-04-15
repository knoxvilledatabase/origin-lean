/-
Extracted from Algebra/Order/Monoid/Unbundled/Defs.lean
Genuine: 24 of 24 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Covariants and contravariants

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `Ordered[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `CovariantClass` and
`ContravariantClass`:

* `CovariantClass` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `ContravariantClass` models the implication `a * b < a * c → b < c`.

Since `Co(ntra)variantClass` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`Ordered[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[OrderedCancelMonoid M]`, into three typeclasses, e.g.
`[CancelMonoid M] [PartialOrder M] [CovariantClass M M (Function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several `Co(ntra)variantClass` assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[CovariantClass M M (*) (≤)] [ContravariantClass M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `CovariantClass` uses the `(≤)`-relation, while
`ContravariantClass` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[Semigroup α] [PartialOrder α] [ContravariantClass α α (*) (≤)] → LeftCancelSemigroup α
```
holds -- note the `Co*ntra*` assumption on the `(≤)`-relation.

## Formalization notes

We stick to the convention of using `Function.swap (*)` (or `Function.swap (+)`), for the
typeclass assumptions, since `Function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use.

-/

open Function

section Variants

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (M N)

def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

class CovariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
  `(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)` -/
  protected elim : Covariant M N μ r

class ContravariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
  pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
  `r` also holds for the pair `(n₁, n₂)`. -/
  protected elim : Contravariant M N μ r

abbrev MulLeftMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (· * ·) (· ≤ ·)

abbrev MulRightMono [Mul M] [LE M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· ≤ ·)

abbrev AddLeftMono [Add M] [LE M] : Prop :=
  CovariantClass M M (· + ·) (· ≤ ·)

abbrev AddRightMono [Add M] [LE M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· ≤ ·)

attribute [to_additive existing] MulLeftMono MulRightMono

abbrev MulLeftStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (· * ·) (· < ·)

abbrev MulRightStrictMono [Mul M] [LT M] : Prop :=
  CovariantClass M M (swap (· * ·)) (· < ·)

abbrev AddLeftStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (· + ·) (· < ·)

abbrev AddRightStrictMono [Add M] [LT M] : Prop :=
  CovariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftStrictMono MulRightStrictMono

abbrev MulLeftReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (· * ·) (· < ·)

abbrev MulRightReflectLT [Mul M] [LT M] : Prop :=
  ContravariantClass M M (swap (· * ·)) (· < ·)

abbrev AddLeftReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (· + ·) (· < ·)

abbrev AddRightReflectLT [Add M] [LT M] : Prop :=
  ContravariantClass M M (swap (· + ·)) (· < ·)

attribute [to_additive existing] MulLeftReflectLT MulRightReflectLT

abbrev MulLeftReflectLE [Mul M] [LE M] : Prop :=
  ContravariantClass M M (· * ·) (· ≤ ·)

abbrev MulRightReflectLE [Mul M] [LE M] : Prop :=
  ContravariantClass M M (swap (· * ·)) (· ≤ ·)

abbrev AddLeftReflectLE [Add M] [LE M] : Prop :=
  ContravariantClass M M (· + ·) (· ≤ ·)

abbrev AddRightReflectLE [Add M] [LE M] : Prop :=
  ContravariantClass M M (swap (· + ·)) (· ≤ ·)

attribute [to_additive existing] MulLeftReflectLE MulRightReflectLE

theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩

section flip

variable {M N μ r}

theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) :=
  fun a _ _ ↦ h a

theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) :=
  fun a _ _ ↦ h a

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab
