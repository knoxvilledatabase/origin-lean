/-
Extracted from AlgebraicTopology/ModelCategory/IsCofibrant.lean
Genuine: 6 of 12 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Fibrant and cofibrant objects in a model category

Once a category `C` has been endowed with a `CategoryWithCofibrations C`
instance, it is possible to define the property `IsCofibrant X` for
any `X : C` as an abbreviation for `Cofibration (initial.to X : ⊥_ C ⟶ X)`.
(Fibrant objects are defined similarly.)

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C]

variable [CategoryWithCofibrations C] [HasInitial C]

abbrev IsCofibrant (X : C) : Prop := Cofibration (initial.to X)

lemma isCofibrant_iff_of_isInitial [(cofibrations C).RespectsIso]
    {A X : C} (i : A ⟶ X) (hA : IsInitial A) :
    IsCofibrant X ↔ Cofibration i := by
  simp only [cofibration_iff]
  apply (cofibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (IsInitial.uniqueUpToIso initialIsInitial hA) (Iso.refl _)

lemma isCofibrant_of_cofibration [(cofibrations C).IsStableUnderComposition]
    {X Y : C} (i : X ⟶ Y) [Cofibration i] [hX : IsCofibrant X] :
    IsCofibrant Y := by
  rw [isCofibrant_iff] at hX ⊢
  rw [Subsingleton.elim (initial.to Y) (initial.to X ≫ i)]
  infer_instance

variable (X Y : C) [(cofibrations C).IsStableUnderCobaseChange] [HasInitial C]
  [HasBinaryCoproduct X Y]

-- INSTANCE (free from Core): [hY

-- INSTANCE (free from Core): [HasInitial

end

end

variable [CategoryWithFibrations C] [HasTerminal C]

abbrev IsFibrant (X : C) : Prop := Fibration (terminal.from X)

lemma isFibrant_iff_of_isTerminal [(fibrations C).RespectsIso]
    {X Y : C} (p : X ⟶ Y) (hY : IsTerminal Y) :
    IsFibrant X ↔ Fibration p := by
  simp only [fibration_iff]
  symm
  apply (fibrations C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (IsTerminal.uniqueUpToIso hY terminalIsTerminal)

lemma isFibrant_of_fibration [(fibrations C).IsStableUnderComposition]
    {X Y : C} (p : X ⟶ Y) [Fibration p] [hY : IsFibrant Y] :
    IsFibrant X := by
  rw [isFibrant_iff] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]
  infer_instance

variable (X Y : C) [(fibrations C).IsStableUnderBaseChange] [HasTerminal C]
  [HasBinaryProduct X Y]

-- INSTANCE (free from Core): [hY

-- INSTANCE (free from Core): [HasTerminal

end

end

end HomotopicalAlgebra
