/-
Extracted from GroupTheory/CoprodI.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The coproduct (a.k.a. the free product) of groups or monoids

Given an `ι`-indexed family `M` of monoids,
we define their coproduct (a.k.a. free product) `Monoid.CoprodI M`.
As usual, we use the suffix `I` for an indexed (co)product,
leaving `Coprod` for the coproduct of two monoids.

When `ι` and all `M i` have decidable equality,
the free product bijects with the type `Monoid.CoprodI.Word M` of reduced words.
This bijection is constructed
by defining an action of `Monoid.CoprodI M` on `Monoid.CoprodI.Word M`.

When `M i` are all groups, `Monoid.CoprodI M` is also a group
(and the coproduct in the category of groups).

## Main definitions

- `Monoid.CoprodI M`: the free product, defined as a quotient of a free monoid.
- `Monoid.CoprodI.of {i} : M i →* Monoid.CoprodI M`.
- `Monoid.CoprodI.lift : (∀ {i}, M i →* N) ≃ (Monoid.CoprodI M →* N)`: the universal property.
- `Monoid.CoprodI.Word M`: the type of reduced words.
- `Monoid.CoprodI.Word.equiv M : Monoid.CoprodI M ≃ word M`.
- `Monoid.CoprodI.NeWord M i j`: an inductive description of non-empty words
  with first letter from `M i` and last letter from `M j`,
  together with an API (`singleton`, `append`, `head`, `tail`, `to_word`, `Prod`, `inv`).
  Used in the proof of the Ping-Pong-lemma.
- `Monoid.CoprodI.lift_injective_of_ping_pong`: The Ping-Pong-lemma,
  proving injectivity of the `lift`. See the documentation of that theorem for more information.

## Remarks

There are many answers to the question "what is the coproduct of a family `M` of monoids?",
and they are all equivalent but not obviously equivalent.
We provide two answers.
The first, almost tautological answer is given by `Monoid.CoprodI M`,
which is a quotient of the type of words in the alphabet `Σ i, M i`.
It's straightforward to define and easy to prove its universal property.
But this answer is not completely satisfactory,
because it's difficult to tell when two elements `x y : Monoid.CoprodI M` are distinct
since `Monoid.CoprodI M` is defined as a quotient.

The second, maximally efficient answer is given by `Monoid.CoprodI.Word M`.
An element of `Monoid.CoprodI.Word M` is a word in the alphabet `Σ i, M i`,
where the letter `⟨i, 1⟩` doesn't occur and no adjacent letters share an index `i`.
Since we only work with reduced words, there is no need for quotienting,
and it is easy to tell when two elements are distinct.
However it's not obvious that this is even a monoid!

We prove that every element of `Monoid.CoprodI M` can be represented by a unique reduced word,
i.e. `Monoid.CoprodI M` and `Monoid.CoprodI.Word M` are equivalent types.
This means that `Monoid.CoprodI.Word M` can be given a monoid structure,
and it lets us tell when two elements of `Monoid.CoprodI M` are distinct.

There is also a completely tautological, maximally inefficient answer
given by `MonCat.Colimits.ColimitType`.
Whereas `Monoid.CoprodI M` at least ensures that
(any instance of) associativity holds by reflexivity,
in this answer associativity holds because of quotienting.
Yet another answer, which is constructively more satisfying,
could be obtained by showing that `Monoid.CoprodI.Rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/

open Set

variable {ι : Type*} (M : ι → Type*) [∀ i, Monoid (M i)]

inductive Monoid.CoprodI.Rel : FreeMonoid (Σ i, M i) → FreeMonoid (Σ i, M i) → Prop
  | of_one (i : ι) : Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, 1⟩) 1
  | of_mul {i : ι} (x y : M i) :
    Monoid.CoprodI.Rel (FreeMonoid.of ⟨i, x⟩ * FreeMonoid.of ⟨i, y⟩) (FreeMonoid.of ⟨i, x * y⟩)

def Monoid.CoprodI : Type _ := (conGen (Monoid.CoprodI.Rel M)).Quotient

deriving Monoid, Inhabited

namespace Monoid.CoprodI
