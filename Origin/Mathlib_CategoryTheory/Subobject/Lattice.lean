/-
Extracted from CategoryTheory/Subobject/Lattice.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The lattice of subobjects

We provide the `SemilatticeInf` with `OrderTop (Subobject X)` instance when `[HasPullback C]`,
and the `SemilatticeSup (Subobject X)` instance when `[HasImages C] [HasBinaryCoproducts C]`.
-/

universe w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

section Top

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): {X

def leTop (f : MonoOver X) : f ⟶ ⊤ :=
  homMk f.arrow (comp_id _)
