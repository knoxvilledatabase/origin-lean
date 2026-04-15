/-
Extracted from Algebra/Module/GradedModule.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Graded Module

Given an `R`-algebra `A` graded by `𝓐`, a graded `A`-module `M` is expressed as
`DirectSum.Decomposition 𝓜` and `SetLike.GradedSMul 𝓐 𝓜`.
Then `⨁ i, 𝓜 i` is an `A`-module and is isomorphic to `M`.

## Tags

graded module
-/

open DirectSum

variable {ιA ιB : Type*} (A : ιA → Type*) (M : ιB → Type*)

namespace DirectSum

open GradedMonoid

class GdistribMulAction [AddMonoid ιA] [VAdd ιA ιB] [GMonoid A] [∀ i, AddMonoid (M i)]
    extends GMulAction A M where
  smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c
  smul_zero {i j} (a : A i) : smul a (0 : M j) = 0

class Gmodule [AddMonoid ιA] [VAdd ιA ιB] [∀ i, AddMonoid (A i)] [∀ i, AddMonoid (M i)] [GMonoid A]
    extends GdistribMulAction A M where
  add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b
  zero_smul {i j} (b : M j) : smul (0 : A i) b = 0

-- INSTANCE (free from Core): GSemiring.toGmodule

variable [AddMonoid ιA] [VAdd ιA ιB] [∀ i : ιA, AddCommMonoid (A i)] [∀ i, AddCommMonoid (M i)]
