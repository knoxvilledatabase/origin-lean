/-
Extracted from CategoryTheory/Localization/Opposite.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Localization of the opposite category

If a functor `L : C ⥤ D` is a localization functor for `W : MorphismProperty C`, it
is shown in this file that `L.op : Cᵒᵖ ⥤ Dᵒᵖ` is also a localization functor.

-/

noncomputable section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {W : MorphismProperty C}

namespace Localization

def StrictUniversalPropertyFixedTarget.op {E : Type*} [Category* E]
    (h : StrictUniversalPropertyFixedTarget L W Eᵒᵖ) :
    StrictUniversalPropertyFixedTarget L.op W.op E where
  inverts := h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert congr_arg Functor.leftOp (h.fac F.rightOp hF.rightOp)
  uniq F₁ F₂ eq := by
    suffices F₁.rightOp = F₂.rightOp by
      rw [← F₁.rightOp_leftOp_eq, ← F₂.rightOp_leftOp_eq, this]
    have eq' := congr_arg Functor.rightOp eq
    exact h.uniq _ _ eq'

-- INSTANCE (free from Core): isLocalization_op

end Localization

variable (L W)

variable [L.IsLocalization W]

namespace Functor

-- INSTANCE (free from Core): IsLocalization.op

-- INSTANCE (free from Core): IsLocalization.unop
