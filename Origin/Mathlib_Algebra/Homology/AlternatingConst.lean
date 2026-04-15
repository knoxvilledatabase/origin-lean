/-
Extracted from Algebra/Homology/AlternatingConst.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The alternating constant complex

Given an object `X : C` and endomorphisms `φ, ψ : X ⟶ X` such that `φ ∘ ψ = ψ ∘ φ = 0`, this file
defines the periodic chain and cochain complexes
`... ⟶ X --φ--> X --ψ--> X --φ--> X --ψ--> 0` and `0 ⟶ X --ψ--> X --φ--> X --ψ--> X --φ--> ...`
(or more generally for any complex shape `c` on `ℕ` where `c.Rel i j` implies `i` and `j` have
different parity). We calculate the homology of these periodic complexes.

In particular, we show `... ⟶ X --𝟙--> X --0--> X --𝟙--> X --0--> X ⟶ 0` is homotopy equivalent
to the single complex where `X` is in degree `0`.

-/

universe v u

open CategoryTheory Limits

namespace ComplexShape

lemma up_nat_odd_add {i j : ℕ} (h : (ComplexShape.up ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

lemma down_nat_odd_add {i j : ℕ} (h : (ComplexShape.down ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

end ComplexShape

namespace HomologicalComplex

open ShortComplex

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)
