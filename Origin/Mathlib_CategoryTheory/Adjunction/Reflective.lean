/-
Extracted from CategoryTheory/Adjunction/Reflective.lean
Genuine: 10 of 13 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`Mathlib/CategoryTheory/Monad/Limits.lean`.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}

variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

class Reflective (R : D ⥤ C) extends R.Full, R.Faithful where
  /-- a choice of a left adjoint to `R` -/
  L : C ⥤ D
  /-- `R` is a right adjoint -/
  adj : L ⊣ R

variable (i : D ⥤ C)

def reflector [Reflective i] : C ⥤ D := Reflective.L (R := i)

def reflectorAdjunction [Reflective i] : reflector i ⊣ i := Reflective.adj

-- INSTANCE (free from Core): [Reflective

-- INSTANCE (free from Core): [Reflective

def Functor.fullyFaithfulOfReflective [Reflective i] : i.FullyFaithful :=
  (reflectorAdjunction i).fullyFaithfulROfIsIsoCounit

set_option backward.isDefEq.respectTransparency false in

theorem unit_obj_eq_map_unit [Reflective i] (X : C) :
    (reflectorAdjunction i).unit.app (i.obj ((reflector i).obj X)) =
      i.map ((reflector i).map ((reflectorAdjunction i).unit.app X)) := by
  rw [← cancel_mono (i.map ((reflectorAdjunction i).counit.app ((reflector i).obj X))),
    ← i.map_comp]
  simp

example [Reflective i] {B : D} : IsIso ((reflectorAdjunction i).unit.app (i.obj B)) :=

  inferInstance

variable {i}

theorem Functor.essImage.unit_isIso [Reflective i] {A : C} (h : i.essImage A) :
    IsIso ((reflectorAdjunction i).unit.app A) := by
  rwa [isIso_unit_app_iff_mem_essImage]

set_option backward.isDefEq.respectTransparency false in

theorem mem_essImage_of_unit_isSplitMono [Reflective i] {A : C}
    [IsSplitMono ((reflectorAdjunction i).unit.app A)] : i.essImage A := by
  let η : 𝟭 C ⟶ reflector i ⋙ i := (reflectorAdjunction i).unit
  haveI : IsIso (η.app (i.obj ((reflector i).obj A))) :=
    Functor.essImage.unit_isIso ((i.obj_mem_essImage _))
  have : Epi (η.app A) := by
    refine @epi_of_epi _ _ _ _ _ (retraction (η.app A)) (η.app A) ?_
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((reflector i).obj A)))
  haveI := isIso_of_epi_of_isSplitMono (η.app A)
  exact (reflectorAdjunction i).mem_essImage_of_unit_isIso A

-- INSTANCE (free from Core): Reflective.comp

def unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) :
    (A ⟶ i.obj B) ≃ (i.obj ((reflector i).obj A) ⟶ i.obj B) :=
  ((reflectorAdjunction i).homEquiv _ _).symm.trans
    (Functor.FullyFaithful.ofFullyFaithful i).homEquiv

theorem unitCompPartialBijectiveAux_symm_apply [Reflective i] {A : C} {B : D}
    (f : i.obj ((reflector i).obj A) ⟶ i.obj B) :
    (unitCompPartialBijectiveAux _ _).symm f = (reflectorAdjunction i).unit.app A ≫ f := by
  simp [unitCompPartialBijectiveAux, Adjunction.homEquiv_unit]

def unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : i.essImage B) :
    (A ⟶ B) ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
  calc
    (A ⟶ B) ≃ (A ⟶ i.obj (Functor.essImage.witness hB)) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj (Functor.essImage.witness hB)) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
      Iso.homCongr (Iso.refl _) (Functor.essImage.getIso hB)
