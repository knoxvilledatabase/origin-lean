/-
Extracted from CategoryTheory/Presentable/Dense.lean
Genuine: 1 of 7 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# `κ`-presentable objects form a dense subcategory

In a `κ`-accessible category `C`, the inclusion of the full subcategory
of `κ`-presentable objects is a dense functor. This expresses canonically
any object `X : C` as a colimit of `κ`-presentable objects, and we show
that this is a `κ`-filtered colimit.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (C κ) in

lemma isCardinalFilteredGenerator_isCardinalPresentable
    [IsCardinalAccessibleCategory C κ] :
    (isCardinalPresentable C κ).IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  refine hP.of_le_isoClosure ?_ le_rfl
  rw [ObjectProperty.isoClosure_eq_self]
  exact hP.le_isCardinalPresentable

namespace IsCardinalAccessibleCategory

-- INSTANCE (free from Core): final_toCostructuredArrow

-- INSTANCE (free from Core): [IsCardinalAccessibleCategory

-- INSTANCE (free from Core): [IsCardinalAccessibleCategory

end IsCardinalAccessibleCategory

namespace IsFinitelyAccessibleCategory

-- INSTANCE (free from Core): [IsFinitelyAccessibleCategory.{w}

-- INSTANCE (free from Core): [IsFinitelyAccessibleCategory.{w}

-- INSTANCE (free from Core): [IsFinitelyAccessibleCategory.{w}

end IsFinitelyAccessibleCategory

end CategoryTheory
