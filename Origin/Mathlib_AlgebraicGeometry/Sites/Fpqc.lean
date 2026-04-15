/-
Extracted from AlgebraicGeometry/Sites/Fpqc.lean
Genuine: 10 of 13 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Fpqc topology

In this file we define the fpqc topology and show it is subcanonical. It is the quasi-compact
topology for flat morphisms.

## Main declarations

- `fppfPrecoverage`: The precoverage given by jointly-surjective families of flat
  morphisms, locally of finite presentation.
- `fpqcPrecoverage`: The precoverage given by quasi-compact, jointly-surjective families of
  flat morphisms.
- The fpqc topology is subcanonical. This is available by `inferInstance`.

-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

def fppfPrecoverage : Precoverage Scheme.{u} :=
  precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
  deriving Precoverage.IsStableUnderBaseChange, Precoverage.IsStableUnderComposition

lemma zariskiPrecoverage_le_fppfPrecoverage :
    zariskiPrecoverage ≤ fppfPrecoverage :=
  precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩

lemma fppfPrecoverage_eq_inf :
    fppfPrecoverage = precoverage @Flat ⊓ precoverage @LocallyOfFinitePresentation := by
  grind [fppfPrecoverage, precoverage, precoverage, MorphismProperty.precoverage_inf]

abbrev fppfTopology : GrothendieckTopology Scheme.{u} :=
  fppfPrecoverage.toGrothendieck

def fpqcPrecoverage : Precoverage Scheme.{u} :=
  propQCPrecoverage @Flat
  deriving Precoverage.HasIsos, Precoverage.IsStableUnderBaseChange,
    Precoverage.IsStableUnderComposition

lemma fppfPrecoverage_le_fpqcPrecoverage : fppfPrecoverage ≤ fpqcPrecoverage := by
  rw [fpqcPrecoverage, propQCPrecoverage, le_inf_iff]
  refine ⟨?_, precoverage_mono fun X Y f ⟨hf, _⟩ ↦ inferInstance⟩
  exact precoverage_le_qcPrecoverage_of_isOpenMap fun X Y f ⟨_, _⟩ ↦ f.isOpenMap

lemma zariskiPrecoverage_le_fpqcPrecoverage : zariskiPrecoverage ≤ fpqcPrecoverage :=
  le_trans zariskiPrecoverage_le_fppfPrecoverage fppfPrecoverage_le_fpqcPrecoverage

abbrev fpqcTopology : GrothendieckTopology Scheme.{u} :=
  fpqcPrecoverage.toGrothendieck

lemma zariskiTopology_le_fpqcTopology : zariskiTopology ≤ fpqcTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fpqcPrecoverage

lemma fppfTopology_le_fpqcTopology : fppfTopology ≤ fpqcTopology :=
  Precoverage.toGrothendieck_mono fppfPrecoverage_le_fpqcPrecoverage

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
