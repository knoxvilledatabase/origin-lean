/-
Extracted from CategoryTheory/Shift/Twist.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Twisting a shift

Given a category `C` equipped with a shift by a monoid `A`, we introduce
a structure `t : TwistShiftData C A` which consists of a collection of
invertible elements in the center of the category `C` (typically, `C` will
be preadditive, and these will be signs), which allow to introduce a type
synonym category `t.Category` with identical shift functors as `C` but where
the isomorphisms `shiftFunctorAdd` have been modified.

-/

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (A : Type w) [AddMonoid A] [HasShift C A]

structure TwistShiftData where
  /-- The invertible elements in the center of `C` which are used to
  modify the `shiftFunctorAdd` isomorphisms. -/
  z (a b : A) : (CatCenter C)ˣ
  z_zero_zero : z 0 0 = 1 := by cat_disch
  assoc (a b c : A) : z (a + b) c * z a b = z a (b + c) * z b c := by cat_disch
  commShift (a b : A) : NatTrans.CommShift (z a b).val A := by infer_instance

namespace TwistShiftData

variable {C A} (t : TwistShiftData C A)

attribute [local simp] z_zero_zero
