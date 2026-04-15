/-
Extracted from Algebra/Homology/CochainComplexPlus.lean
Genuine: 6 of 15 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Bounded below cochain complexes

In this file, we consider the full subcategory `CochainComplex.Plus C`
of `CochainComplex C ℤ` consisting of bounded below cochain complexes
in a category `C`.

-/

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category* C]

protected def plus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ (n : ℤ), K.IsStrictlyGE n

-- INSTANCE (free from Core): [HasZeroMorphisms

abbrev Plus [HasZeroMorphisms C] :=
  (CochainComplex.plus C).FullSubcategory

namespace Plus

variable [HasZeroMorphisms C]

abbrev ι : Plus C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

-- INSTANCE (free from Core): (J

-- INSTANCE (free from Core): (J

-- INSTANCE (free from Core): [HasFiniteLimits

-- INSTANCE (free from Core): [HasFiniteColimits

variable {C} in

lemma mono_iff [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom :=
  ⟨fun _ ↦ inferInstanceAs (Mono ((ι C).map f)),
    fun _ ↦ Functor.mono_of_mono_map (ι C) (by assumption)⟩

def quasiIso [CategoryWithHomology C] : MorphismProperty (Plus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).inverseImage (ι C)

-- INSTANCE (free from Core): [CategoryWithHomology

-- INSTANCE (free from Core): [CategoryWithHomology

end

-- INSTANCE (free from Core): [Preadditive

end Plus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]
