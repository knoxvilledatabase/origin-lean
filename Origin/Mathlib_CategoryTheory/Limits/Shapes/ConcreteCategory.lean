/-
Extracted from CategoryTheory/Limits/Shapes/ConcreteCategory.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Limits in concrete categories

In this file, we combine the description of limits in `Types` and the API about
the preservation of products and pullbacks in order to describe these limits in a
concrete category `C`.

If `F : J → C` is a family of objects in `C`, we define a bijection
`Limits.Concrete.productEquiv F : ToType (∏ᶜ F) ≃ ∀ j, ToType (F j)`.

Similarly, if `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S` are two morphisms, the elements
in `pullback f₁ f₂` are identified by `Limits.Concrete.pullbackEquiv`
to compatible tuples of elements in `X₁ × X₂`.

Some results are also obtained for the terminal object, binary products,
wide-pullbacks, wide-pushouts, multiequalizers and cokernels.

-/

universe s w w' v u t r

namespace CategoryTheory.Limits.Concrete

open ConcreteCategory

variable {C : Type u} [Category.{v} C]

section Products

section ProductEquiv

variable {FC : C → C → Type*} {CC : C → Type max w v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]

variable [ConcreteCategory.{max w v} C FC] {J : Type w} (F : J → C)
  [HasProduct F] [PreservesLimit (Discrete.functor F) (forget C)]

noncomputable def productEquiv : ToType (∏ᶜ F) ≃ ∀ j, ToType (F j) :=
  ((PreservesProduct.iso (forget C) F) ≪≫ (Types.productIso.{w, v} fun j =>
    (ToType (F j)))).toEquiv
