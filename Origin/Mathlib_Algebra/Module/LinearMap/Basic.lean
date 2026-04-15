/-
Extracted from Algebra/Module/LinearMap/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Further results on (semi)linear maps
-/

assert_not_exists Submonoid Finset TrivialStar

open Function

universe u u' v w x y z

variable {R R' S M M' : Type*}

namespace LinearMap

section toFunAsLinearMap

variable {R M N A : Type*} [Semiring R] [Semiring A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N] [SMulCommClass R A N]

variable (R M N A) in

def ltoFun : (M →ₗ[R] N) →ₗ[A] (M → N) where
  toFun f := f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
