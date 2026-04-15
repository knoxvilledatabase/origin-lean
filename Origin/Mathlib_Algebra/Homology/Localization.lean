/-
Extracted from Algebra/Homology/Localization.lean
Genuine: 17 of 20 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-! The category of homological complexes up to quasi-isomorphisms

Given a category `C` with homology and any complex shape `c`, we define
the category `HomologicalComplexUpToQuasiIso C c` which is the localized
category of `HomologicalComplex C c` with respect to quasi-isomorphisms.
When `C` is abelian, this will be the derived category of `C` in the
particular case of the complex shape `ComplexShape.up ℤ`.

Under suitable assumptions on `c` (e.g. chain complexes, or cochain
complexes indexed by `ℤ`), we shall show that `HomologicalComplexUpToQuasiIso C c`
is also the localized category of `HomotopyCategory C c` with respect to
the class of quasi-isomorphisms.

-/

open CategoryTheory Limits

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C]

lemma HomologicalComplex.homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => by
  rw [mem_quasiIso_iff] at hf
  dsimp
  infer_instance

variable [(HomologicalComplex.quasiIso C c).HasLocalization]

abbrev HomologicalComplexUpToQuasiIso := (HomologicalComplex.quasiIso C c).Localization'

variable {C c} in

abbrev HomologicalComplexUpToQuasiIso.Q :
    HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  (HomologicalComplex.quasiIso C c).Q'

namespace HomologicalComplexUpToQuasiIso

noncomputable def homologyFunctor (i : ι) : HomologicalComplexUpToQuasiIso C c ⥤ C :=
  Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

noncomputable def homologyFunctorFactors (i : ι) :
    Q ⋙ homologyFunctor C c i ≅ HomologicalComplex.homologyFunctor C c i :=
  Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

variable {C c}

lemma isIso_Q_map_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.quasiIso C c f := by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 ?_
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h

end HomologicalComplexUpToQuasiIso

end

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

lemma HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences
    [(HomologicalComplex.quasiIso C c).HasLocalization] :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQuasiIso.Q :=
  MorphismProperty.IsInvertedBy.of_le _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_le_quasiIso C c)

namespace HomotopyCategory

def quasiIso : MorphismProperty (HomotopyCategory C c) :=
  fun _ _ f => ∀ (i : ι), IsIso ((homologyFunctor C c i).map f)

variable {C c}

lemma quotient_map_mem_quasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    quasiIso C c ((quotient C c).map f) ↔ HomologicalComplex.quasiIso C c f := by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

variable (C c)

-- INSTANCE (free from Core): respectsIso_quasiIso

lemma homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i

set_option backward.isDefEq.respectTransparency false in

lemma quasiIso_eq_quasiIso_map_quotient :
    quasiIso C c = (HomologicalComplex.quasiIso C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_quasiIso_iff] at h
    exact ((quasiIso C c).arrow_mk_iso_iff e).1 h

end HomotopyCategory

class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category* C] [Preadditive C]
    [CategoryWithHomology C] : Prop where
  areEqualizedByLocalization {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    AreEqualizedByLocalization (HomologicalComplex.quasiIso C c) f g

namespace HomologicalComplexUpToQuasiIso

variable {C c}

variable [(HomologicalComplex.quasiIso C c).HasLocalization] [c.QFactorsThroughHomotopy C]

lemma Q_map_eq_of_homotopy {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    Q.map f = Q.map g :=
  (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q

def Qh : HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  CategoryTheory.Quotient.lift _ HomologicalComplexUpToQuasiIso.Q (by
    intro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)

variable (C c)

def quotientCompQhIso : HomotopyCategory.quotient C c ⋙ Qh ≅ Q := by
  apply Quotient.lift.isLift

set_option backward.isDefEq.respectTransparency false in

lemma Qh_inverts_quasiIso : (HomotopyCategory.quasiIso C c).IsInvertedBy Qh := by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff φ,
    ← HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2

-- INSTANCE (free from Core): :

noncomputable def homologyFunctorFactorsh (i : ι) :
    Qh ⋙ homologyFunctor C c i ≅ HomotopyCategory.homologyFunctor C c i :=
  Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)

set_option backward.isDefEq.respectTransparency false in
