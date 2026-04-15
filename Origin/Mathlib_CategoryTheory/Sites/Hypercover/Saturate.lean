/-
Extracted from CategoryTheory/Sites/Hypercover/Saturate.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Saturation of a `0`-hypercover

Given a `0`-hypercover `E`, we define a `1`-hypercover `E.saturate`
-/

namespace CategoryTheory.PreZeroHypercover

variable {C : Type*} [Category* C] {A : Type*} [Category* A]

open Limits

structure Relation {S : C} (E : PreZeroHypercover S) (i j : E.I₀) where
  /-- The object. -/
  obj : C
  /-- The first projection. -/
  fst : obj ⟶ E.X i
  /-- The second projection. -/
  snd : obj ⟶ E.X j
  w : fst ≫ E.f i = snd ≫ E.f j
