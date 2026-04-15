/-
Extracted from CategoryTheory/Limits/Preserves/Shapes/Terminal.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preserving terminal object

Constructions to relate the notions of preserving terminal objects and reflecting terminal objects
to concrete objects.

In particular, we show that `terminalComparison G` is an isomorphism iff `G` preserves terminal
objects.
-/

universe w v v₁ v₂ u u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable (X : C)

section Terminal

def isLimitMapConeEmptyConeEquiv :
    IsLimit (G.mapCone (asEmptyCone X)) ≃ IsTerminal (G.obj X) :=
  isLimitEmptyConeEquiv D _ _ (eqToIso rfl)

def IsTerminal.isTerminalObj [PreservesLimit (Functor.empty.{0} C) G] (l : IsTerminal X) :
    IsTerminal (G.obj X) :=
  isLimitMapConeEmptyConeEquiv G X (isLimitOfPreserves G l)

def IsTerminal.isTerminalOfObj [ReflectsLimit (Functor.empty.{0} C) G] (l : IsTerminal (G.obj X)) :
    IsTerminal X :=
  isLimitOfReflects G ((isLimitMapConeEmptyConeEquiv G X).symm l)

def IsTerminal.isTerminalIffObj [PreservesLimit (Functor.empty.{0} C) G]
    [ReflectsLimit (Functor.empty.{0} C) G] (X : C) :
    IsTerminal X ≃ IsTerminal (G.obj X) where
  toFun := IsTerminal.isTerminalObj G X
  invFun := IsTerminal.isTerminalOfObj G X
  left_inv := by cat_disch
  right_inv := by cat_disch

lemma preservesLimitsOfShape_pempty_of_preservesTerminal [PreservesLimit (Functor.empty.{0} C) G] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) G where
  preservesLimit := preservesLimit_of_iso_diagram G (Functor.emptyExt (Functor.empty.{0} C) _)

variable [HasTerminal C]

def isLimitOfHasTerminalOfPreservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    IsTerminal (G.obj (⊤_ C)) :=
  terminalIsTerminal.isTerminalObj G (⊤_ C)

theorem hasTerminal_of_hasTerminal_of_preservesLimit [PreservesLimit (Functor.empty.{0} C) G] :
    HasTerminal D := ⟨fun F => by
  haveI := HasLimit.mk ⟨_, isLimitOfHasTerminalOfPreservesLimit G⟩
  apply hasLimit_of_iso F.uniqueFromEmpty.symm⟩

variable [HasTerminal D]

lemma PreservesTerminal.of_iso_comparison [i : IsIso (terminalComparison G)] :
    PreservesLimit (Functor.empty.{0} C) G := by
  apply preservesLimit_of_preserves_limit_cone terminalIsTerminal
  apply (isLimitMapConeEmptyConeEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (Functor.empty.{0} D)) i

lemma preservesTerminal_of_isIso (f : G.obj (⊤_ C) ⟶ ⊤_ D) [i : IsIso f] :
    PreservesLimit (Functor.empty.{0} C) G := by
  rw [Subsingleton.elim f (terminalComparison G)] at i
  exact PreservesTerminal.of_iso_comparison G

lemma preservesTerminal_of_iso (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G :=
  preservesTerminal_of_isIso G f.hom

variable [PreservesLimit (Functor.empty.{0} C) G]

def PreservesTerminal.iso : G.obj (⊤_ C) ≅ ⊤_ D :=
  (isLimitOfHasTerminalOfPreservesLimit G).conePointUniqueUpToIso (limit.isLimit _)
