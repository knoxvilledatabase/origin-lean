/-
Extracted from CategoryTheory/Triangulated/Opposite/OpOp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The triangulated equivalence `Cᵒᵖᵒᵖ ≌ C`.

In this file, we show that if `C` is a pretriangulated category, then
the functors `opOp C : C ⥤ Cᵒᵖᵒᵖ` and `unopUnop C : Cᵒᵖᵒᵖ ⥤ C` are triangulated.
We also show that the unit and counit isomorphisms of the equivalence
`opOpEquivalence C : Cᵒᵖᵒᵖ ≌ C` are compatible with shifts, which is summarized
by the property `(opOpEquivalence C).IsTriangulated`.

-/

namespace CategoryTheory

open Opposite Pretriangulated.Opposite Limits

variable (C : Type*) [Category* C] [HasShift C ℤ]

namespace Pretriangulated

namespace Opposite

namespace OpOpCommShift

set_option backward.isDefEq.respectTransparency false in

def iso (n : ℤ) :
    shiftFunctor C n ⋙ opOp C ≅ opOp C ⋙ shiftFunctor Cᵒᵖᵒᵖ n :=
  NatIso.ofComponents
    (fun X ↦ ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).app (op X)).op ≪≫
      (shiftFunctorOpIso Cᵒᵖ n (-n) (add_neg_cancel n)).symm.app (op (op X)))
    (fun f ↦ Quiver.Hom.unop_inj (by
      simp [shiftFunctor_op_map _ n (-n), shiftFunctor_op_map _ (-n) n]))

variable {C}
