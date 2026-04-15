/-
Extracted from Condensed/Light/Explicit.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.Condensed.Light.Module

/-!

# The explicit sheaf condition for light condensed sets

We give explicit description of light condensed sets:

* `LightCondensed.ofSheafLightProfinite`: A finite-product-preserving presheaf on `LightProfinite`,
  satisfying `EqualizerCondition`.

The property `EqualizerCondition` is defined in `Mathlib/CategoryTheory/Sites/RegularExtensive.lean`
and it says that for any effective epi `X ⟶ B` (in this case that is equivalent to being a
continuous surjection), the presheaf `F` exhibits `F(B)` as the equalizer of the two maps
`F(X) ⇉ F(X ×_B X)`

We also give variants for light condensed objects in concrete categories whose forgetful functor
reflects finite limits (resp. products), where it is enough to check the sheaf condition after
postcomposing with the forgetful functor.
-/

universe v u w

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

variable {A : Type*} [Category A]

namespace LightCondensed

@[simps]
noncomputable def ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : LightCondensed A where
  val := F
  cond := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ _ ↦ inferInstance⟩, hF⟩

@[simps]
noncomputable def ofSheafForgetLightProfinite
    [ConcreteCategory A] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : LightProfinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) : LightCondensed A where
  val := F
  cond := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ _ ↦ inferInstance⟩, hF⟩

theorem equalizerCondition (X : LightCondensed A) : EqualizerCondition X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp X.cond |>.2

noncomputable instance (X : LightCondensed A) : PreservesFiniteProducts X.val :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.val |>.mp X.cond |>.1

end LightCondensed

namespace LightCondSet

noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondSet :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

noncomputable abbrev ofSheafLightProfinite (F : LightProfinite.{u}ᵒᵖ ⥤ ModuleCat.{u} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondMod.{u} R :=
  LightCondensed.ofSheafLightProfinite F hF

end LightCondMod

namespace LightCondAb

noncomputable abbrev ofSheafLightProfinite (F : LightProfiniteᵒᵖ ⥤ ModuleCat ℤ)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : LightCondAb :=
  LightCondMod.ofSheafLightProfinite ℤ F hF

end LightCondAb
