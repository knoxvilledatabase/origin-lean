/-
Extracted from CategoryTheory/Sites/Point/IsMonoidalW.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Monoidal structure on sheaves using enough points

Let `(C, J)` be a site with a conservative family of points.
If `A` is a suitable monoidal category, we show that
the class of morphisms `J.W : MorphismProperty (Cᵒᵖ ⥤ A)`
is stable under tensor products, which allows to
check the assumptions of `Sheaf.monoidalCategory` in the
file `Mathlib/CategoryTheory/Sites/Monoidal.lean`,
i.e. this can be used in order to construct the monoidal
category structure on `Sheaf J A`.

-/

universe w v v' u u'

namespace CategoryTheory

open Limits GrothendieckTopology MonoidalCategory

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  {P : ObjectProperty (Point.{w} J)} (hP : P.IsConservativeFamilyOfPoints)
  (A : Type u') [Category.{v'} A] [MonoidalCategory A]
  [HasColimitsOfSize.{w, w} A] [HasProducts.{w} A]
  {FC : A → A → Type*} {CC : A → Type w}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} A FC]
  [HasWeakSheafify J A]
  [(forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

include hP in

lemma ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W
    [J.HasSheafCompose (forget A)] :
    (J.W (A := A)).IsMonoidal :=
  .mk' _ (fun f g hf hg ↦ by
    simp only [hP.W_iff (A := A)] at hf hg ⊢
    intro Φ
    rw [Functor.Monoidal.map_tensor]
    infer_instance)

-- INSTANCE (free from Core): [J.HasSheafCompose

end CategoryTheory
