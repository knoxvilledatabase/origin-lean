/-
Extracted from CategoryTheory/GradedObject/Monoidal.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The monoidal category structures on graded objects

Assuming that `C` is a monoidal category and that `I` is an additive monoid,
we introduce a partially defined tensor product on the category `GradedObject I C`:
given `X₁` and `X₂` two objects in `GradedObject I C`, we define
`GradedObject.Monoidal.tensorObj X₁ X₂` under the assumption `HasTensor X₁ X₂`
that the coproduct of `X₁ i ⊗ X₂ j` for `i + j = n` exists for any `n : I`.

Under suitable assumptions about the existence of coproducts and the
preservation of certain coproducts by the tensor products in `C`, we
obtain a monoidal category structure on `GradedObject I C`.
In particular, if `C` has finite coproducts to which the tensor
product commutes, we obtain a monoidal category structure on `GradedObject ℕ C`.

-/

universe u

namespace CategoryTheory

open Limits MonoidalCategory Category

variable {I : Type u} [AddMonoid I] {C : Type*} [Category* C] [MonoidalCategory C]

namespace GradedObject

abbrev HasTensor (X₁ X₂ : GradedObject I C) : Prop :=
  HasMap (((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂) (fun ⟨i, j⟩ => i + j)

lemma hasTensor_of_iso {X₁ X₂ Y₁ Y₂ : GradedObject I C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) [HasTensor X₁ X₂] :
    HasTensor Y₁ Y₂ := by
  let e : ((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂ ≅
    ((mapBifunctor (curriedTensor C) I I).obj Y₁).obj Y₂ := isoMk _ _
      (fun ⟨i, j⟩ ↦ (eval i).mapIso e₁ ⊗ᵢ (eval j).mapIso e₂)
  exact hasMap_of_iso e _

namespace Monoidal

noncomputable abbrev tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] :
    GradedObject I C :=
  mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂

variable (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]

noncomputable def ιTensorObj (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    X₁ i₁ ⊗ X₂ i₂ ⟶ tensorObj X₁ X₂ i₁₂ :=
  ιMapBifunctorMapObj (curriedTensor C) _ _ _ _ _ _ h

variable {X₁ X₂}
