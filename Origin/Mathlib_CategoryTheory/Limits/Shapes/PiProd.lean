/-
Extracted from CategoryTheory/Limits/Shapes/PiProd.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!

# A product as a binary product

We write a product indexed by `I` as a binary product of the products indexed by a subset of `I`
and its complement.

-/

namespace CategoryTheory.Limits

variable {C I : Type*} [Category C] {X Y : I → C}
  (f : (i : I) → X i ⟶ Y i) (P : I → Prop) [∀ i, Decidable (P i)]
  [HasProduct X] [HasProduct Y]
  [HasProduct (fun (i : {x : I // P x}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) ↦ X i.val)]
  [HasProduct (fun (i : {x : I // P x}) ↦ Y i.val)]
  [HasProduct (fun (i : {x : I // ¬ P x}) ↦ Y i.val)]

variable (X) in

noncomputable def Pi.binaryFanOfProp : BinaryFan (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) ↦ X i.val)) :=
  BinaryFan.mk (P := ∏ᶜ X) (Pi.map' Subtype.val fun _ ↦ 𝟙 _)
    (Pi.map' Subtype.val fun _ ↦ 𝟙 _)

variable (X) in

noncomputable def Pi.binaryFanOfPropIsLimit : IsLimit (Pi.binaryFanOfProp X P) :=
  BinaryFan.isLimitMk
    (fun s ↦ Pi.lift fun b ↦ if h : P b then
      s.π.app ⟨WalkingPair.left⟩ ≫ Pi.π (fun (i : {x : I // P x}) ↦ X i.val) ⟨b, h⟩ else
      s.π.app ⟨WalkingPair.right⟩ ≫ Pi.π (fun (i : {x : I // ¬ P x}) ↦ X i.val) ⟨b, h⟩)
    (by aesop) (by aesop)
    (fun _ _ h₁ h₂ ↦ Pi.hom_ext _ _ fun b ↦ by
      by_cases h : P b
      · simp [← h₁, dif_pos h]
      · simp [← h₂, dif_neg h])

lemma hasBinaryProduct_of_products : HasBinaryProduct (∏ᶜ (fun (i : {x : I // P x}) ↦ X i.val))
    (∏ᶜ (fun (i : {x : I // ¬ P x}) ↦ X i.val)) :=
  ⟨Pi.binaryFanOfProp X P, Pi.binaryFanOfPropIsLimit X P⟩

attribute [local instance] hasBinaryProduct_of_products

lemma Pi.map_eq_prod_map : Pi.map f =
    ((Pi.binaryFanOfPropIsLimit X P).conePointUniqueUpToIso (prodIsProd _ _)).hom ≫
      prod.map (Pi.map (fun (i : {x : I // P x}) ↦ f i.val))
      (Pi.map (fun (i : {x : I // ¬ P x}) ↦ f i.val)) ≫
        ((Pi.binaryFanOfPropIsLimit Y P).conePointUniqueUpToIso (prodIsProd _ _)).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  dsimp only [IsLimit.conePointUniqueUpToIso, binaryFanOfProp, prodIsProd]
  apply prod.hom_ext
  all_goals aesop_cat

end CategoryTheory.Limits
