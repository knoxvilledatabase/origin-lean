/-
Extracted from Algebra/Category/ModuleCat/Sheaf/Free.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Free sheaves of modules

In this file, we construct the functor
`SheafOfModules.freeFunctor : Type u ⥤ SheafOfModules.{u} R` which sends
a type `I` to the coproduct of copies indexed by `I` of `unit R`.

## TODO

* In case the category `C` has a terminal object `X`, promote `freeHomEquiv`
into an adjunction between `freeFunctor` and the evaluation functor at `X`.
(Alternatively, assuming specific universe parameters, we could show that
`freeHomEquiv` is a left adjoint to `SheafOfModules.sectionsFunctor`.)

-/

universe u v' u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrp.{u}] [J.WEqualsLocallyBijective AddCommGrp.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrp.{u})]

namespace SheafOfModules

noncomputable def free (I : Type u) : SheafOfModules.{u} R := ∐ (fun (_ : I) ↦ unit R)

noncomputable def freeHomEquiv (M : SheafOfModules.{u} R) {I : Type u} :
    (free I ⟶ M) ≃ (I → M.sections) where
  toFun f i := M.unitHomEquiv (Sigma.ι (fun (_ : I) ↦ unit R) i ≫ f)
  invFun s := Sigma.desc (fun i ↦ M.unitHomEquiv.symm (s i))
  left_inv s := Sigma.hom_ext _ _ (by simp)
  right_inv f := by ext1 i; simp

lemma freeHomEquiv_comp_apply {M N : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (p : M ⟶ N) (i : I) :
    N.freeHomEquiv (f ≫ p) i = sectionsMap p (M.freeHomEquiv f i) := rfl

lemma freeHomEquiv_symm_comp {M N : SheafOfModules.{u} R} {I : Type u} (s : I → M.sections)
    (p : M ⟶ N) :
    M.freeHomEquiv.symm s ≫ p = N.freeHomEquiv.symm (fun i ↦ sectionsMap p (s i)) :=
  N.freeHomEquiv.injective (by ext; simp [freeHomEquiv_comp_apply])

noncomputable abbrev freeSection {I : Type u} (i : I) : (free (R := R) I).sections :=
  (free (R := R) I).freeHomEquiv (𝟙 (free I)) i

section

variable {I J : Type u} (f : I → J)

noncomputable def freeMap : free (R := R) I ⟶ free J :=
  (freeHomEquiv _).symm (fun i ↦ freeSection (f i))

@[simp]
lemma freeHomEquiv_freeMap :
    (freeHomEquiv _ (freeMap (R := R) f)) = freeSection.comp f :=
  (freeHomEquiv _).symm.injective (by simp; rfl)

@[simp]
lemma sectionMap_freeMap_freeSection (i : I) :
    sectionsMap (freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← freeHomEquiv_comp_apply]

end

noncomputable def freeFunctor : Type u ⥤ SheafOfModules.{u} R where
  obj := free
  map f := freeMap f
  map_id X := (freeHomEquiv _).injective (by ext1 i; simp)
  map_comp {I J K} f g := (freeHomEquiv _).injective (by ext1; simp [freeHomEquiv_comp_apply])

end SheafOfModules
