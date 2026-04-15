/-
Extracted from CategoryTheory/Limits/FormalCoproducts/ExtraDegeneracy.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Extradegeneracy for the Cech object

Let `U : FormalCoproduct C`. Let `T` be a terminal object in `C`.
In this file, we construct an isomorphism from the Cech object `U.cech` that is
defined for objects in `FormalCoproduct` to the general Cech nerve construction
applied to the morphism from `U` to the terminal object.
This isomorphism is used in order to show that, as an augmented object (over `T`),
the Cech object `U.cech` has an extra degeneracy when there is a
morphism `T ⟶ U.obj i₀` for some `i₀`.

-/

universe w t v u

open Simplicial

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  (U : FormalCoproduct.{w} C) {T : C} (hT : IsTerminal T)

-- INSTANCE (free from Core): (n

-- INSTANCE (free from Core): (n

noncomputable def cechIsoCechNerveApp (n : SimplexCategoryᵒᵖ) :
    U.cech.obj n ≅ (Arrow.cechNerve (Arrow.mk ((isTerminalIncl _ hT).from U))).obj n :=
  IsLimit.conePointUniqueUpToIso (WidePullbackCone.isLimitOfFan
    (arrows := fun _ ↦ (isTerminalIncl _ hT).from U)
    (U.isLimitPowerFan (ToType n.unop)) (isTerminalIncl _ hT)) (limit.isLimit _)
