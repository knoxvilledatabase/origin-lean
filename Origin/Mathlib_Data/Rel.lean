/-
Extracted from Data/Rel.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relations as sets of pairs

This file provides API to regard relations between `α` and `β`  as sets of pairs `Set (α × β)`.

This is in particular useful in the study of uniform spaces, which are topological spaces equipped
with a *uniformity*, namely a filter of pairs `α × α` whose elements can be viewed as "proximity"
relations.

## Main declarations

* `SetRel α β`: Type of relations between `α` and `β`.
* `SetRel.inv`: Turn `R : SetRel α β` into `R.inv : SetRel β α` by swapping the arguments.
* `SetRel.dom`: Domain of a relation. `a ∈ R.dom` iff there exists `b` such that `a ~[R] b`.
* `SetRel.cod`: Codomain of a relation. `b ∈ R.cod` iff there exists `a` such that `a ~[R] b`.
* `SetRel.id`: The identity relation `SetRel α α`.
* `SetRel.comp`: SetRelation composition. Note that the arguments order follows the category theory
  convention, namely `(R ○ S) a c ↔ ∃ b, a ~[R] b ∧ b ~[S] z`.
* `SetRel.image`: Image of a set under a relation. `b ∈ image R s` iff there exists `a ∈ s`
  such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.image = Set.image f`.
* `SetRel.preimage`: Preimage of a set under a relation. `a ∈ preimage R t` iff there exists
  `b ∈ t` such that `a ~[R] b`.
  If `R` is the graph of `f` (`a ~[R] b ↔ f a = b`), then `R.preimage = Set.preimage f`.
* `SetRel.core`: Core of a set. For `t : Set β`, `a ∈ R.core t` iff all `b` related to `a` are in
  `t`.
* `SetRel.restrictDomain`: Domain-restriction of a relation to a subtype.
* `Function.graph`: Graph of a function as a relation.

## Implementation notes

There is tension throughout the library between considering relations between `α` and `β` simply as
`α → β → Prop`, or as a bundled object `SetRel α β` with dedicated operations and API.

The former approach is used almost everywhere as it is very lightweight and has arguably native
support from core Lean features, but it cracks at the seams whenever one starts talking about
operations on relations. For example:
* composition of relations `R : α → β → Prop`, `S : β → γ → Prop` is
  `SetRelation.Comp R S := fun a c ↦ ∃ b, R a b ∧ S b c`
* map of a relation `R : α → β → Prop` under `f : α → γ`, `g : β → δ` is
  `SetRelation.map R f g := fun c d ↦ ∃ a b, r a b ∧ f a = c ∧ g b = d`.

The latter approach is embodied by `SetRel α β`, with dedicated notation like `○` for composition.

Previously, `SetRel` suffered from the leakage of its definition as
```
def SetRel (α β : Type*) := α → β → Prop
```
The fact that `SetRel` wasn't an `abbrev` confuses automation.
But simply making it an `abbrev` would
have killed the point of having a separate less see-through type to perform relation operations on,
so we instead redefined
```
def SetRel (α β : Type*) := Set (α × β) → Prop
```
This extra level of indirection guides automation correctly and prevents (some kinds of) leakage.

Simultaneously, uniform spaces need a theory of relations on a type `α` as elements of
`Set (α × α)`, and the new definition of `SetRel` fulfills this role quite well.
-/

variable {α β γ δ : Type*} {ι : Sort*}

abbrev SetRel (α β : Type*) := Set (α × β)

namespace SetRel

variable {R R₁ R₂ : SetRel α β} {S : SetRel β γ} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {u : Set γ}
  {a a₁ a₂ : α} {b : β} {c : γ}

scoped notation:50 a:50 " ~[" R "] " b:50 => (a, b) ∈ R

variable (R) in

def inv (R : SetRel α β) : SetRel β α := Prod.swap ⁻¹' R
