/-
Extracted from CategoryTheory/Abelian/GrothendieckCategory/Subobject.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Subobjects in Grothendieck abelian categories

We study the complete lattice of subobjects of `X : C`
when `C` is a Grothendieck abelian category. In particular,
for a functor `F : J ⥤ MonoOver X` from a filtered category,
we relate the colimit of `F` (computed in `C`) and the
supremum of the subobjects corresponding to the objects
in the image of `F`.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits

namespace IsGrothendieckAbelian

attribute [local instance] IsFiltered.isConnected

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J] (F : J ⥤ MonoOver X)

variable [IsFiltered J] {c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)}
  (hc : IsColimit c) (f : c.pt ⟶ X) (hf : ∀ (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom)

include hc hf

set_option backward.isDefEq.respectTransparency false in

lemma mono_of_isColimit_monoOver : Mono f := by
  let α : F ⋙ MonoOver.forget _ ⋙ Over.forget _ ⟶ (Functor.const _).obj X :=
    { app j := (F.obj j).obj.hom }
  have := NatTrans.mono_of_mono_app α
  exact colim.map_mono' α hc (isColimitConstCocone J X) f (by simpa using hf)

set_option backward.isDefEq.respectTransparency false in

lemma subobjectMk_of_isColimit_eq_iSup :
    haveI := mono_of_isColimit_monoOver F hc f hf
    Subobject.mk f = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
  haveI := mono_of_isColimit_monoOver F hc f hf
  apply le_antisymm
  · rw [le_iSup_iff]
    intro s H
    induction s using Subobject.ind with | _ g
    let c' : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _) := Cocone.mk _
      { app j := Subobject.ofMkLEMk _ _ (H j)
        naturality j j' f := by
          dsimp
          simpa only [← cancel_mono g, Category.assoc, Subobject.ofMkLEMk_comp,
            Category.comp_id] using MonoOver.w (F.map f) }
    exact Subobject.mk_le_mk_of_comm (hc.desc c')
      (hc.hom_ext (fun j ↦ by rw [hc.fac_assoc c' j, hf, Subobject.ofMkLEMk_comp]))
  · rw [iSup_le_iff]
    intro j
    exact Subobject.mk_le_mk_of_comm (c.ι.app j) (hf j)

end

set_option backward.isDefEq.respectTransparency false in

noncomputable def isColimitMapCoconeOfSubobjectMkEqISup
    [IsFiltered J] (c : Cocone (F ⋙ MonoOver.forget _)) [Mono c.pt.hom]
    (h : Subobject.mk c.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom) :
    IsColimit ((Over.forget _).mapCocone c) := by
  let f : colimit (F ⋙ MonoOver.forget X ⋙ Over.forget X) ⟶ X :=
    colimit.desc _ (Cocone.mk X
      { app j := (F.obj j).obj.hom
        naturality {j j'} g := by simp [MonoOver.forget] })
  haveI := mono_of_isColimit_monoOver F (colimit.isColimit _) f (by simp [f])
  have := subobjectMk_of_isColimit_eq_iSup F (colimit.isColimit _) f (by simp [f])
  rw [← h] at this
  refine IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (Subobject.isoOfMkEqMk _ _ this) (fun j ↦ ?_))
  rw [← cancel_mono (c.pt.hom)]
  dsimp
  rw [Category.assoc, Subobject.ofMkLEMk_comp, Over.w]
  apply colimit.ι_desc

set_option backward.isDefEq.respectTransparency false in

end IsGrothendieckAbelian

end CategoryTheory
