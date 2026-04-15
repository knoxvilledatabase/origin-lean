/-
Extracted from CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.lean
Genuine: 1 of 7 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!

# AB axioms in sheaf categories

If `J` is a Grothendieck topology on a small category `C : Type v`,
and `A : Type u₁` (with `Category.{v} A`) is a Grothendieck abelian category,
then `Sheaf J A` is a Grothendieck abelian category.

-/

universe v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Limits

namespace Sheaf

variable {C : Type u} {A : Type u₁} {K : Type u₂}
  [Category.{v} C] [Category.{v₁} A] [Category.{v₂} K]
  (J : GrothendieckTopology C)

variable [HasWeakSheafify J A]

-- INSTANCE (free from Core): [HasFiniteLimits

-- INSTANCE (free from Core): [HasFiniteColimits

end

-- INSTANCE (free from Core): hasFilteredColimitsOfSize

-- INSTANCE (free from Core): hasExactColimitsOfShape

-- INSTANCE (free from Core): ab5ofSize

-- INSTANCE (free from Core): {C

attribute [local instance] hasSheafifyEssentiallySmallSite in

lemma isGrothendieckAbelian_of_essentiallySmall
    {C : Type u₂} [Category.{v₂} C] [EssentiallySmall.{v} C]
    (J : GrothendieckTopology C)
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [∀ (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A]
    [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] :
      IsGrothendieckAbelian.{v} (Sheaf J A) :=
  IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel C).inverse.sheafInducedTopologyEquivOfIsCoverDense J A)

end Sheaf

end CategoryTheory
