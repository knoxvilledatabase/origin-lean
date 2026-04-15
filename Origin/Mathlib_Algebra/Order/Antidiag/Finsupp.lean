/-
Extracted from Algebra/Order/Antidiag/Finsupp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Antidiagonal of finitely supported functions as finsets

This file defines the finset of finitely functions summing to a specific value on a finset. Such
finsets should be thought of as the "antidiagonals" in the space of finitely supported functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.finsuppAntidiag s n` is the finset of all finitely supported functions `f : ι →₀ μ` with
support contained in `s` and such that the sum of its values equals `n : μ`.

We define it using `Finset.piAntidiag s n`, the corresponding antidiagonal in `ι → μ`.

## Main declarations

* `Finset.finsuppAntidiag s n`: Finset of all finitely supported functions `f : ι →₀ μ` with support
  contained in `s` and such that the sum of its values equals `n : μ`.

-/

assert_not_exists Field

open Finsupp Function

variable {ι μ μ' : Type*}

namespace Finset

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

def finsuppAntidiag (s : Finset ι) (n : μ) : Finset (ι →₀ μ) :=
  (piAntidiag s n).attach.map ⟨fun f ↦ ⟨s.filter (f.1 · ≠ 0), f.1, by
    simpa using (mem_piAntidiag.1 f.2).2⟩, fun _ _ hfg ↦ Subtype.ext (congr_arg (⇑) hfg)⟩
