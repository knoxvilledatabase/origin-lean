/-
Extracted from Algebra/Homology/HomotopyCategory/MappingCone.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # The mapping cone of a morphism of cochain complexes

In this file, we study the homotopy cofiber `HomologicalComplex.homotopyCofiber`
of a morphism `φ : F ⟶ G` of cochain complexes indexed by `ℤ`. In this case,
we redefine it as `CochainComplex.mappingCone φ`. The API involves definitions
- `mappingCone.inl φ : Cochain F (mappingCone φ) (-1)`,
- `mappingCone.inr φ : G ⟶ mappingCone φ`,
- `mappingCone.fst φ : Cocycle (mappingCone φ) F 1` and
- `mappingCone.snd φ : Cochain (mappingCone φ) G 0`.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits

universe v v'

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

variable {ι : Type*} [AddRightCancelSemigroup ι] [One ι]
    {F G : CochainComplex C ι} (φ : F ⟶ G)

-- INSTANCE (free from Core): [∀

end

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

noncomputable def mappingCone : CochainComplex C ℤ := homotopyCofiber φ

namespace mappingCone

open HomComplex
