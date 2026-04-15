/-
Extracted from RingTheory/KrullDimension/Module.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Krull Dimension of Module

In this file we define `Module.supportDim R M` for an `R`-module `M` as
the krull dimension of its support. It is equal to the krull dimension of `R / Ann M` when
`M` is finitely generated.

-/

variable (R : Type*) [CommRing R]

variable (M : Type*) [AddCommGroup M] [Module R M] (N : Type*) [AddCommGroup N] [Module R N]

namespace Module

open Order

noncomputable def supportDim : WithBot ℕ∞ :=
  krullDim (Module.support R M)
