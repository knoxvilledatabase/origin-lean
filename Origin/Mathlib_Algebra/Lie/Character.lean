/-
Extracted from Algebra/Lie/Character.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Characters of Lie algebras

A character of a Lie algebra `L` over a commutative ring `R` is a morphism of Lie algebras `L → R`,
where `R` is regarded as a Lie algebra over itself via the ring commutator. For an Abelian Lie
algebra (e.g., a Cartan subalgebra of a semisimple Lie algebra) a character is just a linear form.

## Main definitions

  * `LieAlgebra.LieCharacter`
  * `LieAlgebra.lieCharacterEquivLinearDual`

## Tags

lie algebra, lie character
-/

universe u v w w₁

namespace LieAlgebra

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

abbrev LieCharacter :=
  L →ₗ⁅R⁆ R

variable {R L}

theorem lieCharacter_apply_lie (χ : LieCharacter R L) (x y : L) : χ ⁅x, y⁆ = 0 := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, mul_comm, sub_self]
