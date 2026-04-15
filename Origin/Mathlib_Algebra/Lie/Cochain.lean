/-
Extracted from Algebra/Lie/Cochain.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Lie algebra cohomology in low degree
This file defines low degree cochains of Lie algebras with coefficients given by a module. They are
useful in the construction of central extensions, so we treat these easier cases separately from the
general theory of Lie algebra cohomology.

## Main definitions
* `LieAlgebra.oneCochain`: an abbreviation for a linear map.
* `LieAlgebra.twoCochain`: a submodule of bilinear maps, giving 2-cochains.
* `LieAlgebra.d₁₂`: The coboundary map taking 1-cochains to 2-cochains.
* `LieAlgebra.d₂₃`: A coboundary map taking 2-cochains to a space containing 3-cochains.
* `LieAlgebra.twoCocycle`: The submodule of 2-cocycles.

## TODO
* coboundaries, cohomology
* comparison to the Chevalley-Eilenberg complex.
* construction and classification of central extensions

## References
* [H. Cartan, S. Eilenberg, *Homological Algebra*](cartan-eilenberg-1956)

-/

namespace LieModule.Cohomology

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

abbrev oneCochain := L →ₗ[R] M

def twoCochain : Submodule R (L →ₗ[R] L →ₗ[R] M) where
  carrier := {c | ∀ x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]

variable {R L M}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
