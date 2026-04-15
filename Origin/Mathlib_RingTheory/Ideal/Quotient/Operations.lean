/-
Extracted from RingTheory/Ideal/Quotient/Operations.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# More operations on modules and ideals related to quotients

## Main results:

- `RingHom.quotientKerEquivRange` : the **first isomorphism theorem** for commutative rings.
- `RingHom.quotientKerEquivRangeS` : the **first isomorphism theorem**
  for a morphism from a commutative ring to a semiring.
- `AlgHom.quotientKerEquivRange` : the **first isomorphism theorem**
  for a morphism of algebras (over a commutative semiring)
- `Ideal.quotientInfRingEquivPiQuotient`: the **Chinese Remainder Theorem**, version for coprime
  ideals (see also `ZMod.prodEquivPi` in `Data.ZMod.Quotient` for elementary versions about
  `ZMod`).
-/

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [Ring R] [Semiring S] (f : R →+* S)

def kerLift : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift _ f fun _ => mem_ker.mp
