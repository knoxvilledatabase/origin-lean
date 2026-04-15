/-
Extracted from AlgebraicTopology/ModelCategory/FibrantObjectHomotopy.lean
Genuine: 14 of 27 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core

/-!
# The homotopy category of fibrant objects

Let `C` be a model category. By using the left homotopy relation,
we introduce the homotopy category `FibrantObject.HoCat C` of fibrant objects
in `C`, and we define a fibrant resolution functor
`FibrantObject.HoCat.resolution : C ⥤ FibrantObject.HoCat C`.

This file was obtained by dualizing the definitions in
`Mathlib/AlgebraicTopology/ModelCategory/CofibrantObjectHomotopy.lean`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace FibrantObject

variable (C) in

def homRel : HomRel (FibrantObject C) :=
  fun _ _ f g ↦ LeftHomotopyRel f.hom g.hom

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma homRel_equivalence_of_isCofibrant_src {X Y : FibrantObject C} [IsCofibrant X.obj] :
    Equivalence (homRel C (X := X) (Y := Y) · ·) :=
  (LeftHomotopyRel.equivalence _ _).comap (fun (f : X ⟶ Y) ↦ f.hom)

variable (C) in

abbrev HoCat := Quotient (FibrantObject.homRel C)

def toHoCat : FibrantObject C ⥤ HoCat C := Quotient.functor _

lemma toHoCat_obj_surjective : Function.Surjective (toHoCat (C := C)).obj :=
  fun ⟨_⟩ ↦ ⟨_, rfl⟩

-- INSTANCE (free from Core): :

lemma toHoCat_map_eq {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : homRel C f g) :
    toHoCat.map f = toHoCat.map g :=
  CategoryTheory.Quotient.sound _ h

lemma toHoCat_map_eq_iff {X Y : FibrantObject C} [IsCofibrant X.obj] (f g : X ⟶ Y) :
    toHoCat.map f = toHoCat.map g ↔ homRel C f g := by
  dsimp [toHoCat]
  rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
    HomRel.compClosure_eq_self, homRel_equivalence_of_isCofibrant_src.eqvGen_eq]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma weakEquivalence_toHoCat_map_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence (toHoCat.map f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  apply MorphismProperty.quotient_iff

variable (C) in

def toHoCatLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (FibrantObject C))
      (weakEquivalences (FibrantObject.HoCat C)) where
  functor := toHoCat
  map _ _ _ h := by
    simp only [← weakEquivalence_iff] at h
    simpa only [MorphismProperty.inverseImage_iff, ← weakEquivalence_iff,
      weakEquivalence_toHoCat_map_iff]

variable (C) in

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {D

lemma HoCat.exists_resolution (X : C) :
    ∃ (X' : C) (_ : IsFibrant X') (i : X ⟶ X'), Cofibration i ∧ WeakEquivalence i := by
  have h := MorphismProperty.factorizationData (trivialCofibrations C) (fibrations C)
    (terminal.from X)
  refine ⟨h.Z, ?_, h.i, inferInstance, inferInstance⟩
  rw [isFibrant_iff_of_isTerminal h.p terminalIsTerminal]
  infer_instance

noncomputable def HoCat.resolutionObj (X : C) : C :=
    (exists_resolution X).choose

-- INSTANCE (free from Core): (X

noncomputable def HoCat.iResolutionObj (X : C) : X ⟶ resolutionObj X :=
  (exists_resolution X).choose_spec.choose_spec.choose

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): (X

lemma HoCat.exists_resolution_map {X Y : C} (f : X ⟶ Y) :
    ∃ (g : resolutionObj X ⟶ resolutionObj Y),
      iResolutionObj X ≫ g = f ≫ iResolutionObj Y := by
  have sq : CommSq (f ≫ iResolutionObj Y) (iResolutionObj X)
    (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

noncomputable def HoCat.resolutionMap {X Y : C} (f : X ⟶ Y) :
    resolutionObj X ⟶ resolutionObj Y :=
  (exists_resolution_map f).choose
