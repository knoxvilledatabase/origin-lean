/-
Extracted from Algebra/Category/Ring/Under/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Under `CommRingCat`

In this file we provide basic API for `Under R` when `R : CommRingCat`. `Under R` is
(equivalent to) the category of commutative `R`-algebras. For not necessarily commutative
algebras, use `AlgCat R` instead.
-/

noncomputable section

universe u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (A

set_option backward.isDefEq.respectTransparency false in

def toAlgHom {A B : Under R} (f : A ⟶ B) : A →ₐ[R] B where
  __ := f.right.hom
  commutes' a := by
    have : (A.hom ≫ f.right) a = B.hom a := by simp
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using this
