/-
Extracted from Condensed/Light/TopComparison.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Condensed.Light.Basic
import Mathlib.Condensed.TopComparison

noncomputable section

/-!

# The functor from topological spaces to light condensed sets

We define the functor `topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u}`.

-/

universe u

open CategoryTheory

noncomputable abbrev TopCat.toLightCondSet (X : TopCat.{u}) : LightCondSet.{u} :=
  toSheafCompHausLike.{u} _ X (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

noncomputable abbrev topCatToLightCondSet : TopCat.{u} ⥤ LightCondSet.{u} :=
  topCatToSheafCompHausLike.{u} _ (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)
