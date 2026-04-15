/-
Extracted from CategoryTheory/Monoidal/DayConvolution.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Day convolution monoidal structure

Given functors `F G : C ⥤ V` between two monoidal categories,
this file defines a typeclass `DayConvolution` on functors `F` `G` that contains
a functor `F ⊛ G`, as well as the required data to exhibit `F ⊛ G` as a pointwise
left Kan extension of `F ⊠ G` (see `Mathlib/CategoryTheory/Monoidal/ExternalProduct/Basic.lean`
for the definition) along the tensor product of `C`.
Such a functor is called a Day convolution of `F` and `G`, and
although we do not show it yet, this operation defines a monoidal structure on `C ⥤ V`.

We also define a typeclass `DayConvolutionUnit` on a functor `U : C ⥤ V` that bundles the data
required to make it a unit for the Day convolution monoidal structure: said data is that of
a map `𝟙_ V ⟶ U.obj (𝟙_ C)` that exhibits `U` as a pointwise left Kan extension of
`fromPUnit (𝟙_ V)` along `fromPUnit (𝟙_ C)`.

The main way to assert that a given monoidal category structure on a category `D`
arises as a "Day convolution monoidal structure" is given by the typeclass
`LawfulDayConvolutionMonoidalCategoryStruct C V D`, which bundles the data and
equations needed to exhibit `D` as a monoidal full subcategory of `C ⥤ V` if
the latter were to have the Day convolution monoidal structure. The definition
`monoidalOfLawfulDayConvolutionMonoidalCategoryStruct` promotes (under suitable
assumptions on `V`) a `LawfulDayConvolutionMonoidalCategoryStruct C V D` to
a monoidal structure.


## References
- [nLab page: Day convolution](https://ncatlab.org/nlab/show/Day+convolution)

## TODOs (@robin-carlier)
- Type alias for `C ⥤ V` with a `LawfulDayConvolutionMonoidalCategoryStruct`.
- Characterization of lax monoidal functors out of a Day convolution monoidal category.
- Case `V = Type u` and its universal property.
- Fix the abuse of functor associativity that causes `erw [id_apply]` in a few places in this file.

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.MonoidalCategory

open scoped ExternalProduct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
  [MonoidalCategory C] [MonoidalCategory V]

class DayConvolution (F G : C ⥤ V) where
  /-- The chosen convolution between the functors. Denoted `F ⊛ G`. -/
  convolution : C ⥤ V
  /-- The chosen convolution between the functors. -/
  unit (F) (G) : F ⊠ G ⟶ tensor C ⋙ convolution
  /-- The transformation `unit` exhibits `F ⊛ G` as a pointwise left Kan extension
  of `F ⊠ G` along `tensor C`. -/
  isPointwiseLeftKanExtensionUnit (F G) :
    (Functor.LeftExtension.mk (convolution) unit).IsPointwiseLeftKanExtension

namespace DayConvolution

open scoped Prod

scoped infixr:80 " ⊛ " => convolution

variable (F G : C ⥤ V)

-- INSTANCE (free from Core): leftKanExtension

variable {F G}

def uniqueUpToIso (h : DayConvolution F G) (h' : DayConvolution F G) :
    h.convolution ≅ h'.convolution :=
  Functor.leftKanExtensionUnique h.convolution h.unit h'.convolution h'.unit
