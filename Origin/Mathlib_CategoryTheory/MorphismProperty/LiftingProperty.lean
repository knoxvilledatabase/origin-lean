/-
Extracted from CategoryTheory/MorphismProperty/LiftingProperty.lean
Genuine: 7 of 15 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Left and right lifting properties

Given a morphism property `T`, we define the left and right lifting property with respect to `T`.

We show that the left lifting property is stable under retracts, cobase change, coproducts,
and composition, with dual statements for the right lifting property.

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (T : MorphismProperty C)

namespace MorphismProperty

def llp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty f g

def rlp : MorphismProperty C := fun _ _ f ↦
  ∀ ⦃X Y : C⦄ (g : X ⟶ Y) (_ : T g), HasLiftingProperty g f

lemma llp_of_isIso {A B : C} (i : A ⟶ B) [IsIso i] :
    T.llp i :=
  fun _ _ _ _ ↦ inferInstance

lemma rlp_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    T.rlp f :=
  fun _ _ _ _ ↦ inferInstance

-- INSTANCE (free from Core): llp_isStableUnderRetracts

-- INSTANCE (free from Core): rlp_isStableUnderRetracts

-- INSTANCE (free from Core): llp_isStableUnderCobaseChange

open IsPullback in

-- INSTANCE (free from Core): rlp_isStableUnderBaseChange

-- INSTANCE (free from Core): llp_isMultiplicative

-- INSTANCE (free from Core): rlp_isMultiplicative

-- INSTANCE (free from Core): llp_isStableUnderCoproductsOfShape

-- INSTANCE (free from Core): rlp_isStableUnderProductsOfShape

lemma le_llp_iff_le_rlp (T' : MorphismProperty C) :
    T ≤ T'.llp ↔ T' ≤ T.rlp :=
  ⟨fun h _ _ _ hp _ _ _ hi ↦ h _ hi _ hp,
    fun h _ _ _ hi _ _ _ hp ↦ h _ hp _ hi⟩

lemma gc_llp_rlp :
    GaloisConnection (OrderDual.toDual (α := MorphismProperty C) ∘ llp)
      (rlp ∘ OrderDual.ofDual) :=
  fun _ _ ↦ le_llp_iff_le_rlp _ _

lemma le_llp_rlp : T ≤ T.rlp.llp := by
  rw [le_llp_iff_le_rlp]
