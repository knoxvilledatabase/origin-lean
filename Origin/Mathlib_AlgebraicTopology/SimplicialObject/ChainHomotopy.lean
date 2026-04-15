/-
Extracted from AlgebraicTopology/SimplicialObject/ChainHomotopy.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Simplicial homotopies induce chain homotopies

Given a simplicial homotopy between morphisms of simplicial objects in a preadditive category,
we construct a chain homotopy between the induced morphisms on the alternating face map complexes.

Concretely, if `H : Homotopy f g` gives maps
`H.h i : X _⦋n⦌ ⟶ Y _⦋n+1⦌` indexed by `i : Fin (n + 1)`, we define the degree-`n` component
of the chain homotopy as the opposite of alternating sum `∑ i, (-1)^i • H.h i`.
-/

universe v u

open CategoryTheory CategoryTheory.SimplicialObject

open SimplexCategory Simplicial Opposite AlgebraicTopology

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable {X Y : SimplicialObject C} {f g : X ⟶ Y}

variable (H : Homotopy f g)

namespace ToChainHomotopy

noncomputable def hom (p q : ℕ) : X _⦋p⦌ ⟶ Y _⦋q⦌ :=
  if h : p + 1 = q then
    -∑ k : Fin (p + 1), ((-1 : ℤ) ^ (k : ℕ)) • H.h k ≫ eqToHom (by simp [h])
  else 0
