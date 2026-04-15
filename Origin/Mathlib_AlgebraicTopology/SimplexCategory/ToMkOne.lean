/-
Extracted from AlgebraicTopology/SimplexCategory/ToMkOne.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Morphisms to `⦋1⦌`

We define a bijective map `SimplexCategory.toMk₁ : Fin (n + 2) → `⦋n⦌ ⟶ ⦋1⦌`.
This is used in the file `Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne`
in the study of simplices in the simplicial set `Δ[1]`.

-/

universe u

open CategoryTheory Simplicial

namespace SimplexCategory

def toMk₁ {n : ℕ} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋1⦌ :=
  Hom.mk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs <;> grind }
