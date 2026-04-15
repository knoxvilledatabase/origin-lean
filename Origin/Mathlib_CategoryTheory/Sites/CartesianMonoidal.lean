/-
Extracted from CategoryTheory/Sites/CartesianMonoidal.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Chosen finite products on sheaves

In this file, we put a `CartesianMonoidalCategory` instance on `A`-valued sheaves for a
`GrothendieckTopology` whenever `A` has a `CartesianMonoidalCategory` instance.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite Category Limits Sieve MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{v₂} A]

variable (J : GrothendieckTopology C)

variable [CartesianMonoidalCategory A]

namespace Sheaf

variable (X Y : Sheaf J A)

lemma tensorProd_isSheaf : Presheaf.IsSheaf J (X.obj ⊗ Y.obj) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (BinaryFan.mk (fst X.obj Y.obj) (snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (tensorProductIsBinaryProduct X.obj Y.obj)

lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cone.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun isTerminalTensorUnit
  · exact .empty _

-- INSTANCE (free from Core): :

example : CartesianMonoidalCategory (Sheaf J A) :=

  inferInstance
