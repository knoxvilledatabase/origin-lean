/-
Extracted from Algebra/Homology/HomotopyCategory.lean
Genuine: 4 of 19 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# The homotopy category

`HomotopyCategory V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type*} [Semiring R]
  {ι : Type*} (V : Type u) [Category.{v} V] [Preadditive V] (c : ComplexShape ι)

def homotopic : HomRel (HomologicalComplex V c) := fun _ _ f g => Nonempty (Homotopy f g)

-- INSTANCE (free from Core): homotopy_congruence

def HomotopyCategory :=
  CategoryTheory.Quotient (homotopic V c)

-- INSTANCE (free from Core): :

namespace HomotopyCategory

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def quotient : HomologicalComplex V c ⥤ HomotopyCategory V c :=
  CategoryTheory.Quotient.functor _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Linear

-- INSTANCE (free from Core): [Linear

open ZeroObject

-- INSTANCE (free from Core): [HasZeroObject

-- INSTANCE (free from Core): [HasZeroObject

-- INSTANCE (free from Core): {D

-- INSTANCE (free from Core): {D

variable {V c}

lemma quotient_obj_surjective (X : HomotopyCategory V c) :
    ∃ (K : HomologicalComplex V c), (quotient _ _).obj K = X :=
  ⟨_, rfl⟩
