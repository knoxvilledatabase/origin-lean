/-
Extracted from MeasureTheory/Constructions/UnitInterval.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# The canonical measure on the unit interval

This file provides a `MeasureTheory.MeasureSpace` instance on `unitInterval`,
and shows it is a probability measure with no atoms.

It also contains some basic results on the volume of various interval sets.
-/

open scoped unitInterval

open MeasureTheory Measure Set

namespace unitInterval

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma measurableEmbedding_coe : MeasurableEmbedding ((↑) : I → ℝ) where
  injective := Subtype.val_injective
  measurable := measurable_subtype_coe
  measurableSet_image' _ := measurableSet_Icc.subtype_image

lemma volume_apply {s : Set I} : volume s = volume (Subtype.val '' s) :=
  measurableEmbedding_coe.comap_apply ..

lemma measurePreserving_coe : MeasurePreserving ((↑) : I → ℝ) volume (volume.restrict I) :=
  measurePreserving_subtype_coe measurableSet_Icc

-- INSTANCE (free from Core): :
