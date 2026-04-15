/-
Extracted from CategoryTheory/Limits/Shapes/Terminal.lean
Genuine: 16 of 18 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable (C)

abbrev HasTerminal :=
  HasLimitsOfShape (Discrete.{0} PEmpty) C

abbrev HasInitial :=
  HasColimitsOfShape (Discrete.{0} PEmpty) C

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

theorem hasTerminalChangeDiagram (h : HasLimit F₁) : HasLimit F₂ :=
  ⟨⟨⟨⟨limit F₁, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩

theorem hasTerminalChangeUniverse [h : HasLimitsOfShape (Discrete.{w} PEmpty) C] :
    HasLimitsOfShape (Discrete.{w'} PEmpty) C where
  has_limit _ := hasTerminalChangeDiagram C (h.1 (Functor.empty C))

theorem hasInitialChangeDiagram (h : HasColimit F₁) : HasColimit F₂ :=
  ⟨⟨⟨⟨colimit F₁, by cat_disch, by simp⟩,
    isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩

theorem hasInitialChangeUniverse [h : HasColimitsOfShape (Discrete.{w} PEmpty) C] :
    HasColimitsOfShape (Discrete.{w'} PEmpty) C where
  has_colimit _ := hasInitialChangeDiagram C (h.1 (Functor.empty C))

end Univ

abbrev terminal [HasTerminal C] : C :=
  limit (Functor.empty.{0} C)

abbrev initial [HasInitial C] : C :=
  colimit (Functor.empty.{0} C)

notation "⊤_ " C:20 => terminal C

notation "⊥_ " C:20 => initial C

variable {C}

theorem hasTerminal_of_unique (X : C) [∀ Y, Nonempty (Y ⟶ X)] [∀ Y, Subsingleton (Y ⟶ X)] :
    HasTerminal C where
  has_limit F := .mk ⟨_, (isTerminalEquivUnique F X).invFun fun _ ↦
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

theorem IsTerminal.hasTerminal {X : C} (h : IsTerminal X) : HasTerminal C :=
  { has_limit := fun F => HasLimit.mk ⟨⟨X, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }

theorem hasInitial_of_unique (X : C) [∀ Y, Nonempty (X ⟶ Y)] [∀ Y, Subsingleton (X ⟶ Y)] :
    HasInitial C where
  has_colimit F := .mk ⟨_, (isInitialEquivUnique F X).invFun fun _ ↦
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩

theorem IsInitial.hasInitial {X : C} (h : IsInitial X) : HasInitial C where
  has_colimit F :=
    HasColimit.mk ⟨⟨X, by cat_disch, by simp⟩, isColimitChangeEmptyCocone _ h _ (Iso.refl _)⟩

abbrev terminal.from [HasTerminal C] (P : C) : P ⟶ ⊤_ C :=
  limit.lift (Functor.empty C) (asEmptyCone P)

abbrev initial.to [HasInitial C] (P : C) : ⊥_ C ⟶ P :=
  colimit.desc (Functor.empty C) (asEmptyCocone P)

def terminalIsTerminal [HasTerminal C] : IsTerminal (⊤_ C) where
  lift _ := terminal.from _

def initialIsInitial [HasInitial C] : IsInitial (⊥_ C) where
  desc _ := initial.to _

-- INSTANCE (free from Core): uniqueToTerminal

-- INSTANCE (free from Core): uniqueFromInitial
