/-
Extracted from Algebra/DirectSum/Algebra.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-! # Additively-graded algebra structures on `⨁ i, A i`

This file provides `R`-algebra structures on external direct sums of `R`-modules.

Recall that if `A i` are a family of `AddCommMonoid`s indexed by an `AddMonoid`, then an instance
of `DirectSum.GMonoid A` is a multiplication `A i → A j → A (i + j)` giving `⨁ i, A i` the
structure of a semiring. In this file, we introduce the `DirectSum.GAlgebra R A` class for the case
where all `A i` are `R`-modules. This is the extra structure needed to promote `⨁ i, A i` to an
`R`-algebra.

## Main definitions

* `DirectSum.GAlgebra R A`, the typeclass.
* `DirectSum.toAlgebra` extends `DirectSum.toSemiring` to produce an `AlgHom`.

-/

universe uι uR uA uB

variable {ι : Type uι}

namespace DirectSum

open DirectSum

variable (R : Type uR) (A : ι → Type uA) {B : Type uB}

variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

variable [AddMonoid ι] [GSemiring A]

class GAlgebra where
  toFun : R →+ A 0
  map_one : toFun 1 = GradedMonoid.GOne.one
  map_mul :
    ∀ r s, GradedMonoid.mk _ (toFun (r * s)) = .mk _ (GradedMonoid.GMul.mul (toFun r) (toFun s))
  commutes : ∀ (r) (x : GradedMonoid A), .mk _ (toFun r) * x = x * .mk _ (toFun r)
  smul_def : ∀ (r) (x : GradedMonoid A), r • x = .mk _ (toFun r) * x

end

variable [Semiring B] [GAlgebra R A] [Algebra R B]

-- INSTANCE (free from Core): _root_.GradedMonoid.smulCommClass_right

-- INSTANCE (free from Core): _root_.GradedMonoid.isScalarTower_right

variable [DecidableEq ι]

-- INSTANCE (free from Core): :
