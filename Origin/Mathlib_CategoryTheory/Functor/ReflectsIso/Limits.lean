/-
Extracted from CategoryTheory/Functor/ReflectsIso/Limits.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exactness of families of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a conservative family of functors (i.e. they jointly
reflect isomorphisms). Let `G : J ⥤ C` be a functor that has a limit that
is preserved by the functors `Fᵢ`. In this file, we show that a cone for `G`
is a limit if it is so after applying the functors `Fᵢ`.

-/

namespace CategoryTheory.JointlyReflectIsomorphisms

open Category Limits

variable {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]
  {F : ∀ i, C ⥤ D i} (hF : JointlyReflectIsomorphisms F)
  {J : Type*} [Category* J] {G : J ⥤ C}

noncomputable def jointlyReflectsLimit
    {c : Cone G} (hc : ∀ i, IsLimit ((F i).mapCone c))
    [HasLimit G] [∀ i, PreservesLimit G (F i)] :
    IsLimit c := by
  suffices IsIso (limit.lift _ c) from
    IsLimit.ofIsoLimit (limit.isLimit _)
      (Cone.ext (asIso (limit.lift _ c) :)).symm
  rw [hF.isIso_iff]
  intro i
  let H := isLimitOfPreserves (F i) (limit.isLimit G)
  let e := IsLimit.conePointUniqueUpToIso (hc i) H
  have : e.hom = (F i).map (limit.lift G c) :=
    H.hom_ext (fun j ↦ by
      simpa [← Functor.map_comp] using
        IsLimit.conePointUniqueUpToIso_hom_comp (hc i) H j)
  rw [← this]
  infer_instance

noncomputable def jointlyReflectsColimit
    {c : Cocone G} (hc : ∀ i, IsColimit ((F i).mapCocone c))
    [HasColimit G] [∀ i, PreservesColimit G (F i)] :
    IsColimit c := by
  suffices IsIso (colimit.desc _ c) from
    IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (colimit.desc _ c) :))
  rw [hF.isIso_iff]
  intro i
  let H := isColimitOfPreserves (F i) (colimit.isColimit G)
  let e := IsColimit.coconePointUniqueUpToIso H (hc i)
  have : e.hom = (F i).map (colimit.desc G c) :=
    H.hom_ext (fun j ↦ by
      simpa [← Functor.map_comp] using
        IsColimit.comp_coconePointUniqueUpToIso_hom H (hc i) j)
  rw [← this]
  infer_instance

end CategoryTheory.JointlyReflectIsomorphisms
