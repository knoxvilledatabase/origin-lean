/-
Extracted from RingTheory/Regular/RegularSequence.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Regular sequences and weakly regular sequences

The notion of a regular sequence is fundamental in commutative algebra.
Properties of regular sequences encode information about singularities of a
ring and regularity of a sequence can be tested homologically.
However the notion of a regular sequence is only really sensible for Noetherian local rings.

TODO: Koszul regular sequences, `H_1`-regular sequences, quasi-regular sequences, depth.

## Tags

module, regular element, regular sequence, commutative algebra
-/

universe u v

open scoped Pointwise

variable {R S M M₂ M₃ M₄ : Type*}

namespace Ideal

variable [Semiring R] [Semiring S]

abbrev ofList (rs : List R) := span { r | r ∈ rs }
