/-
Extracted from CategoryTheory/Comma/StructuredArrow/Final.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Finality on Costructured Arrow categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8(i)
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open Limits Functor CostructuredArrow

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]

variable {T : Type u₁} [SmallCategory T]

attribute [local instance] Grothendieck.final_map

set_option backward.isDefEq.respectTransparency false in

private lemma final_of_final_costructuredArrowToOver_small (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [∀ b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L := by
  rw [final_iff_isIso_colimit_pre]
  intro G
  have : ∀ (b : B), Final ((whiskerLeft R (preFunctor L (𝟭 T))).app b).toFunctor := fun b =>
    inferInstanceAs (Final (CostructuredArrow.toOver L (R.obj b)))
  let i : colimit (L ⋙ G) ≅ colimit G :=
    calc colimit (L ⋙ G) ≅ colimit <| grothendieckProj L ⋙ L ⋙ G :=
            colimitIsoColimitGrothendieck L (L ⋙ G)
      _ ≅ colimit <| Grothendieck.pre (functor L) R ⋙ grothendieckProj L ⋙ L ⋙ G :=
            (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ L ⋙ G)).symm
      _ ≅ colimit <| Grothendieck.map (whiskerLeft _ (preFunctor L (𝟭 T))) ⋙
            grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
              HasColimit.isoOfNatIso (NatIso.ofComponents (fun _ => Iso.refl _))
      _ ≅ colimit <| grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
            Final.colimitIso _ _
      _ ≅ colimit <| Grothendieck.pre (functor (𝟭 T)) R ⋙ grothendieckProj (𝟭 T) ⋙ G :=
            HasColimit.isoOfNatIso (Iso.refl _)
      _ ≅ colimit <| grothendieckProj (𝟭 T) ⋙ G :=
            Final.colimitIso _ _
      _ ≅ colimit G := (colimitIsoColimitGrothendieck (𝟭 T) G).symm
  convert Iso.isIso_hom i
  simp only [Iso.trans_def, comp_obj, grothendieckProj_obj, Grothendieck.pre_obj_base,
    Grothendieck.pre_obj_fiber, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, i]
  rw [← Iso.inv_comp_eq, Iso.eq_inv_comp]
  apply colimit.hom_ext (fun _ => by simp)

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

variable {T : Type u₃} [Category.{v₃} T]

set_option backward.isDefEq.respectTransparency false in

end Functor

end CategoryTheory
