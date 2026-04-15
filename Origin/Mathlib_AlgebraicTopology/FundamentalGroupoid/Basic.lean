/-
Extracted from AlgebraicTopology/FundamentalGroupoid/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

open CategoryTheory

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)
