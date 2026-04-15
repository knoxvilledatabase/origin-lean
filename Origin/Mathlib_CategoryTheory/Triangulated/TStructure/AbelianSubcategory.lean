/-
Extracted from CategoryTheory/Triangulated/TStructure/AbelianSubcategory.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Abelian subcategories of triangulated categories

Let `ι : A ⥤ C` be a fully faithful additive functor where `A` is
an additive category and `C` is a triangulated category. We show that `A`
is an abelian category if the following conditions are satisfied:
* For any object `X` and `Y` in `A`, there is no nonzero morphism
  `ι.obj X ⟶ (ι.obj Y)⟦n⟧` when `n < 0`.
* Any morphism `f₁ : X₁ ⟶ X₂` in `A` is admissible, i.e. when
  we complete `ι.obj f₁` in a distinguished triangle
  `ι.obj X₁ ⟶ ι.obj X₂ ⟶ X₃ ⟶ (ι.obj X₁)⟦1⟧`, there exists objects `K`
  and `Q`, and a distinguished triangle `(ι.obj K)⟦1⟧ ⟶ X₃ ⟶ (ι.obj Q) ⟶ ...`.

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*, 1.2][bbd-1982]

-/

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated ZeroObject

namespace Triangulated

variable {C A : Type*} [Category* C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category* A] {ι : A ⥤ C}

namespace AbelianSubcategory

variable (hι : ∀ ⦃X Y : A⦄ ⦃n : ℤ⦄ (f : ι.obj X ⟶ (ι.obj Y)⟦n⟧), n < 0 → f = 0)

set_option backward.isDefEq.respectTransparency false in

include hι in

omit [HasZeroObject C] [Pretriangulated C] in

lemma eq_zero_of_hom_shift_pos
    {X Y : A} {n : ℤ} (f : (ι.obj X)⟦n⟧ ⟶ ι.obj Y) (hn : 0 < n) :
    f = 0 :=
  (shiftFunctor C (-n)).map_injective (by
    rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app _), Functor.map_zero, comp_zero]
    exact hι _ (by lia))

variable {X₁ X₂ : A} {f₁ : X₁ ⟶ X₂} {X₃ : C} (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
  (hT : Triangle.mk (ι.map f₁) f₂ f₃ ∈ distTriang C) {K Q : A}
  (α : (ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃) (β : X₃ ⟶ (ι.obj Q)) {γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
  (hT' : Triangle.mk α β γ ∈ distTriang C)

variable [ι.Full]

noncomputable def ιK : K ⟶ X₁ := (ι ⋙ shiftFunctor C (1 : ℤ)).preimage (α ≫ f₃)

noncomputable def πQ : X₂ ⟶ Q := ι.preimage (f₂ ≫ β)

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]

  [Pretriangulated C] in
