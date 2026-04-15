/-
Extracted from AlgebraicTopology/SimplicialSet/StdSimplex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The standard simplex

We define the standard simplices `Δ[n]` as simplicial sets.
See files `SimplicialSet.Boundary` and `SimplicialSet.Horn`
for their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open Simplicial`.)

-/

universe u

open CategoryTheory Limits Simplicial Opposite

namespace SSet

def stdSimplex : CosimplicialObject SSet.{u} := uliftYoneda
