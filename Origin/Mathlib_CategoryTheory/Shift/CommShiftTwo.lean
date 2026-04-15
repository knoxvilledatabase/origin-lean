/-
Extracted from CategoryTheory/Shift/CommShiftTwo.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Commutation with shifts of functors in two variables

We introduce a typeclass `Functor.CommShift₂Int` for a bifunctor `G : C₁ ⥤ C₂ ⥤ D`
(with `D` a preadditive category) as the two variable analogue of `Functor.CommShift`.
We require that `G` commutes with the shifts in both variables and that the two
ways to identify `(G.obj (X₁⟦p⟧)).obj (X₂⟦q⟧)` to `((G.obj X₁).obj X₂)⟦p + q⟧`
differ by the sign `(-1) ^ (p + q)`.

This is implemented using a structure `Functor.CommShift₂` which does not depend
on the preadditive structure on `D`: instead of signs, elements in `(CatCenter D)ˣ`
are used. These elements are part of a `CommShift₂Setup` structure which extends
a `TwistShiftData` structure (see the file `Mathlib.CategoryTheory.Shift.Twist`).

## TODO (@joelriou)
* Show that `G : C₁ ⥤ C₂ ⥤ D` satisfies `Functor.CommShift₂Int` iff the uncurried
  functor `C₁ × C₂ ⥤ D` commutes with the shift by `ℤ × ℤ`, where `C₁ × C₂` is
  equipped with the obvious product shift, and `D` is equipped with
  the twisted shift.

-/

namespace CategoryTheory

variable {C₁ C₁' C₂ C₂' D : Type*} [Category* C₁] [Category* C₁']
  [Category* C₂] [Category* C₂'] [Category* D]

variable (D) in

structure CommShift₂Setup (M : Type*) [AddCommMonoid M] [HasShift D M] extends
    TwistShiftData (PullbackShift D (AddMonoidHom.fst M M + AddMonoidHom.snd _ _)) (M × M) where
  z_zero₁ (m₁ m₂ : M) : z (0, m₁) (0, m₂) = 1 := by aesop
  z_zero₂ (m₁ m₂ : M) : z (m₁, 0) (m₂, 0) = 1 := by aesop
  /-- The invertible elements in the center of `D` that are equal
  to `(z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n)`. -/
  ε (m n : M) : (CatCenter D)ˣ
  hε (m n : M) : ε m n = (z (0, n) (m, 0))⁻¹ * z (m, 0) (0, n) := by aesop
