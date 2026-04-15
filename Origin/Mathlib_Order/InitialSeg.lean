/-
Extracted from Order/InitialSeg.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Initial and principal segments

This file defines initial and principal segment embeddings. Though these definitions make sense for
arbitrary relations, they're intended for use with well orders.

An initial segment is simply a lower set, i.e. if `x` belongs to the range, then any `y < x` also
belongs to the range. A principal segment is a set of the form `Set.Iio x` for some `x`.

An initial segment embedding `r ≼i s` is an order embedding `r ↪ s` such that its range is an
initial segment. Likewise, a principal segment embedding `r ≺i s` has a principal segment for a
range.

## Main definitions

* `InitialSeg r s`: Type of initial segment embeddings of `r` into `s`, denoted by `r ≼i s`.
* `PrincipalSeg r s`: Type of principal segment embeddings of `r` into `s`, denoted by `r ≺i s`.

The lemmas `Ordinal.type_le_iff` and `Ordinal.type_lt_iff` tell us that `≼i` corresponds to the `≤`
relation on ordinals, while `≺i` corresponds to the `<` relation. This prompts us to think of
`PrincipalSeg` as a "strict" version of `InitialSeg`.

## Notation

These notations belong to the `InitialSeg` locale.

* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
* `α ≤i β` is an abbreviation for `(· < ·) ≼i (· < ·)`.
* `α <i β` is an abbreviation for `(· < ·) ≺i (· < ·)`.
-/

/-! ### Initial segment embeddings -/

universe u

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

open Function

structure InitialSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The order embedding is an initial segment -/
  mem_range_of_rel' : ∀ a b, s b (toRelEmbedding a) → b ∈ Set.range toRelEmbedding
