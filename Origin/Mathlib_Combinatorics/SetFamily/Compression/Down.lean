/-
Extracted from Combinatorics/SetFamily/Compression/Down.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Down-compressions

This file defines down-compression.

Down-compressing `𝒜 : Finset (Finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `Finset.nonMemberSubfamily`: `𝒜.nonMemberSubfamily a` is the subfamily of sets not containing
  `a`.
* `Finset.memberSubfamily`: `𝒜.memberSubfamily a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `Down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `Down.compress a 𝒜` in scope `SetFamily`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/

variable {α : Type*} [DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finset α} {a : α}

namespace Finset

def nonMemberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) := {s ∈ 𝒜 | a ∉ s}

def memberSubfamily (a : α) (𝒜 : Finset (Finset α)) : Finset (Finset α) :=
  {s ∈ 𝒜 | a ∈ s}.image fun s => erase s a
