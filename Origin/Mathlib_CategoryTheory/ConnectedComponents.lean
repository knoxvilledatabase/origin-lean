/-
Extracted from CategoryTheory/ConnectedComponents.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Connected components of a category

Defines a type `ConnectedComponents J` indexing the connected components of a category, and the
full subcategories giving each connected component: `Component j : Type u₁`.
We show that each `Component j` is in fact connected.

We show every category can be expressed as a disjoint union of its connected components, in
particular `Decomposed J` is the category (definitionally) given by the sigma-type of the connected
components of `J`, and it is shown that this is equivalent to `J`.
-/

universe v₁ v₂ v₃ u₁ u₂

noncomputable section

open CategoryTheory.Category

namespace CategoryTheory

-- INSTANCE (free from Core): 100]

variable {J : Type u₁} [Category.{v₁} J]

def ConnectedComponents (J : Type u₁) [Category.{v₁} J] : Type u₁ :=
  Quotient (Zigzag.setoid J)

def Functor.mapConnectedComponents {K : Type u₂} [Category.{v₂} K] (F : J ⥤ K)
    (x : ConnectedComponents J) : ConnectedComponents K :=
  x |> Quotient.lift (Quotient.mk (Zigzag.setoid _) ∘ F.obj)
    (fun _ _ ↦ Quot.sound ∘ zigzag_obj_of_zigzag F)
