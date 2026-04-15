/-
Extracted from Algebra/Lie/UniversalEnveloping.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Universal enveloping algebra

Given a commutative ring `R` and a Lie algebra `L` over `R`, we construct the universal
enveloping algebra of `L`, together with its universal property.

## Main definitions

  * `UniversalEnvelopingAlgebra`: the universal enveloping algebra, endowed with an
    `R`-algebra structure.
  * `UniversalEnvelopingAlgebra.ι`: the Lie algebra morphism from `L` to its universal
    enveloping algebra.
  * `UniversalEnvelopingAlgebra.lift`: given an associative algebra `A`, together with a Lie
    algebra morphism `f : L →ₗ⁅R⁆ A`, `lift R L f : UniversalEnvelopingAlgebra R L →ₐ[R] A` is the
    unique morphism of algebras through which `f` factors.
  * `UniversalEnvelopingAlgebra.ι_comp_lift`: states that the lift of a morphism is indeed part
    of a factorisation.
  * `UniversalEnvelopingAlgebra.lift_unique`: states that lifts of morphisms are indeed unique.
  * `UniversalEnvelopingAlgebra.hom_ext`: a restatement of `lift_unique` as an extensionality
    lemma.

## Tags

lie algebra, universal enveloping algebra, tensor algebra
-/

universe u₁ u₂ u₃

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "ιₜ" => TensorAlgebra.ι R

namespace UniversalEnvelopingAlgebra

inductive Rel : TensorAlgebra R L → TensorAlgebra R L → Prop
  | lie_compat (x y : L) : Rel (ιₜ ⁅x, y⁆ + ιₜ y * ιₜ x) (ιₜ x * ιₜ y)

end UniversalEnvelopingAlgebra

def UniversalEnvelopingAlgebra :=
  RingQuot (UniversalEnvelopingAlgebra.Rel R L)

deriving Inhabited, Ring, Algebra R

namespace UniversalEnvelopingAlgebra

def mkAlgHom : TensorAlgebra R L →ₐ[R] UniversalEnvelopingAlgebra R L :=
  RingQuot.mkAlgHom R (Rel R L)

variable {L}
