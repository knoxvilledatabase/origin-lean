/-
Extracted from Algebra/Category/ModuleCat/Images.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of R-modules has images.

Note that we don't need to register any of the constructions here as instances, because we get them
from the fact that `ModuleCat R` is an abelian category.
-/

open CategoryTheory

open CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

attribute [local ext] Subtype.ext

def image : ModuleCat R :=
  ModuleCat.of R (LinearMap.range f.hom)

def image.ι : image f ⟶ H :=
  ofHom (LinearMap.range f.hom).subtype

-- INSTANCE (free from Core): :

def factorThruImage : G ⟶ image f :=
  ofHom f.hom.rangeRestrict

attribute [local simp] image.fac

variable {f}

noncomputable def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.I :=
  ofHom
  { toFun := (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : image f → F'.I)
    map_add' := fun x y => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_add]
      change (F'.e ≫ F'.m) _ = (F'.e ≫ F'.m) _ + (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl
    map_smul' := fun c x => by
      apply (mono_iff_injective F'.m).1
      · infer_instance
      rw [map_smul]
      change (F'.e ≫ F'.m) _ = _ • (F'.e ≫ F'.m) _
      simp_rw [F'.fac, (Classical.indefiniteDescription (fun z => f z = _) _).2]
      rfl }

theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

def monoFactorisation : MonoFactorisation f where
  I := image f
  m := image.ι f
  e := factorThruImage f

noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := image.lift
  lift_fac := image.lift_fac

noncomputable def imageIsoRange {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    Limits.image f ≅ ModuleCat.of R (LinearMap.range f.hom) :=
  IsImage.isoExt (Image.isImage f) (isImage f)
