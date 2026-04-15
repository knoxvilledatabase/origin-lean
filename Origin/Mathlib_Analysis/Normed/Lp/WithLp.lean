/-
Extracted from Analysis/Normed/Lp/WithLp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # The `WithLp` type synonym

`WithLp p V` is a copy of `V` with exactly the same vector space structure, but with the Lp norm
instead of any existing norm on `V`; recall that by default `ι → R` and `R × R` are equipped with
a norm defined as the supremum of the norms of their components.

This file defines the vector space structure for all types `V`; the norm structure is built for
different specializations of `V` in downstream files.

Note that this should not be used for infinite products, as in these cases the "right" Lp spaces is
not the same as the direct product of the spaces. See the docstring in `Mathlib/Analysis/PiLp` for
more details.

## Main definitions

* `WithLp p V`: a copy of `V` to be equipped with an L`p` norm.
* `WithLp.toLp`: the canonical inclusion from `V` to `WithLp p V`.
* `WithLp.ofLp`: the canonical inclusion from `WithLp p V` to `V`.
* `WithLp.linearEquiv p K V`: the canonical `K`-module isomorphism between `WithLp p V` and `V`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type (`ProdLp`, `PiLp`, etc), and allows all the structure-copying code
to be shared.

TODO: is it safe to copy across the topology and uniform space structure too for all reasonable
choices of `V`?
-/

open scoped ENNReal

structure WithLp (p : ℝ≥0∞) (V : Type*) where
  /-- Converts an element of `V` to an element of `WithLp p V`. -/
  toLp (p) ::
  /-- Converts an element of `WithLp p V` to an element of `V`. -/
  ofLp : V

section Notation

open Lean.PrettyPrinter.Delaborator
