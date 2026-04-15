/-
Extracted from CategoryTheory/Limits/Types/Images.lean
Genuine: 8 of 14 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Images in the category of types

In this file, it is shown that the category of types has categorical images,
and that these agree with the range of a function.

-/

universe v u

namespace CategoryTheory.Limits.Types

variable {α β : Type u} (f : α ⟶ β)

def Image : Type u :=
  Set.range f

-- INSTANCE (free from Core): [Inhabited

def Image.ι : Image f ⟶ β :=
  TypeCat.ofHom (Subtype.val)

-- INSTANCE (free from Core): :

variable {f}

noncomputable def Image.lift (F' : MonoFactorisation f) : Image f ⟶ F'.I :=
  TypeCat.ofHom (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : Image f → F'.I)

theorem Image.lift_fac (F' : MonoFactorisation f) : Image.lift F' ≫ F'.m = Image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

end

def monoFactorisation : MonoFactorisation f where
  I := Image f
  m := Image.ι f
  e := TypeCat.ofHom (Set.rangeFactorization f)

noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := Image.lift
  lift_fac := Image.lift_fac

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {F : ℕᵒᵖ ⥤ Type u} {c : Cone F}
  (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))

private noncomputable def limitOfSurjectionsSurjective.preimage
    (a : F.obj ⟨0⟩) : (n : ℕ) → F.obj ⟨n⟩
    | 0 => a
    | n + 1 => (hF n (preimage a n)).choose

include hF in

open limitOfSurjectionsSurjective in

set_option backward.isDefEq.respectTransparency false in

lemma surjective_π_app_zero_of_surjective_map
    (hc : IsLimit c)
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) := by
  let i := hc.conePointUniqueUpToIso (limitConeIsLimit F)
  have : c.π.app ⟨0⟩ = i.hom ≫ (limitCone F).π.app ⟨0⟩ := by simp [i]; rfl
  rw [this, types_comp]
  apply Function.Surjective.comp
  · exact surjective_π_app_zero_of_surjective_map_aux hF
  · rw [← epi_iff_surjective]
    infer_instance

end CategoryTheory.Limits.Types
