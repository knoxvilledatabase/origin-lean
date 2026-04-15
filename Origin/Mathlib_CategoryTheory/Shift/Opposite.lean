/-
Extracted from CategoryTheory/Shift/Opposite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The (naive) shift on the opposite category

If `C` is a category equipped with a shift by a monoid `A`, the opposite category
can be equipped with a shift such that the shift functor by `n` is `(shiftFunctor C n).op`.
This is the "naive" opposite shift, which we shall set on a category `OppositeShift C A`,
which is a type synonym for `Cᵒᵖ`.

However, for the application to (pre)triangulated categories, we would like to
define the shift on `Cᵒᵖ` so that `shiftFunctor Cᵒᵖ n` for `n : ℤ` identifies to
`(shiftFunctor C (-n)).op` rather than `(shiftFunctor C n).op`. Then, the construction
of the shift on `Cᵒᵖ` shall combine the shift on `OppositeShift C A` and another
construction of the "pullback" of a shift by a monoid morphism like `n ↦ -n`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `A`, we define
a type synonym `OppositeShift.functor A F` for `F.op`. When `F` has a `CommShift` structure
by `A`, we define a `CommShift` structure by `A` on `OppositeShift.functor A F`. In this
way, we can make this an instance and reserve `F.op` for the `CommShift` instance by
the modified shift in the case of (pre)triangulated categories.

Similarly, if `τ` is a natural transformation between functors `F,G : C ⥤ D`, we define
a type synonym for `τ.op` called
`OppositeShift.natTrans A τ : OppositeShift.functor A F ⟶ OppositeShift.functor A G`.
When `τ` has a `CommShift` structure by `A` (i.e. is compatible with `CommShift` structures
on `F` and `G`), we define a `CommShift` structure by `A` on `OppositeShift.natTrans A τ`.

Finally, if we have an adjunction `F ⊣ G` (with `G : D ⥤ C`), we define a type synonym
`OppositeShift.adjunction A adj : OppositeShift.functor A G ⊣ OppositeShift.functor A F`
for `adj.op`, and we show that, if `adj` compatible with `CommShift` structures
on `F` and `G`, then `OppositeShift.adjunction A adj` is also compatible with the pulled back
`CommShift` structures.

Given a `CommShift` structure on a functor `F`, we define a `CommShift` structure on `F.op`
(and vice versa).
We also prove that, if an adjunction `F ⊣ G` is compatible with `CommShift` structures on
`F` and `G`, then the opposite adjunction `G.op ⊣ F.op` is compatible with the opposite
`CommShift` structures.

-/

namespace CategoryTheory

open Limits Category

variable (C : Type*) [Category* C] (A : Type*) [AddMonoid A] [HasShift C A]

namespace HasShift

def mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where
  F n := (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_zero_add_inv_app n X.unop).trans (by simp))
  add_zero_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_add_zero_inv_app n X.unop).trans (by simp))

end HasShift
