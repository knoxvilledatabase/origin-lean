/-
Extracted from InformationTheory/Hamming.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hammingDist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hammingNorm x`: the Hamming norm of `x`, the number of non-zero entries.
* `Hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `Hamming.toHamming`, `Hamming.ofHamming`: functions for casting between `Hamming β` and
  `Π i, β i`.
* the Hamming norm forms a normed group on `Hamming β`.
-/

section HammingDistNorm

open Finset Function

variable {α ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)]

variable {γ : ι → Type*} [∀ i, DecidableEq (γ i)]

def hammingDist (x y : ∀ i, β i) : ℕ := #{i | x i ≠ y i}
