/-
Extracted from Combinatorics/SetFamily/Shadow.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Shadows

This file defines shadows of a set family. The shadow of a set family is the set family of sets we
get by removing any element from any set of the original family. If one pictures `Finset α` as a big
hypercube (each dimension being membership of a given element), then taking the shadow corresponds
to projecting each finset down once in all available directions.

## Main definitions

* `Finset.shadow`: The shadow of a set family. Everything we can get by removing a new element from
  some set.
* `Finset.upShadow`: The upper shadow of a set family. Everything we can get by adding an element
  to some set.

## Notation

We define notation in scope `FinsetFamily`:
* `∂ 𝒜`: Shadow of `𝒜`.
* `∂⁺ 𝒜`: Upper shadow of `𝒜`.

We also maintain the convention that `a, b : α` are elements of the ground type, `s, t : Finset α`
are finsets, and `𝒜, ℬ : Finset (Finset α)` are finset families.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, set family
-/

open Finset Nat

variable {α : Type*}

namespace Finset

section Shadow

variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)} {s t : Finset α} {a : α} {k r : ℕ}

def shadow (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  𝒜.sup fun s => s.image (erase s)
