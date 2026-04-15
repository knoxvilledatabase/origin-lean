/-
Extracted from Algebra/Lie/Derivation/Basic.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Lie derivations

This file defines *Lie derivations* and establishes some basic properties.

## Main definitions

- `LieDerivation`: A Lie derivation `D` from the Lie `R`-algebra `L` to the `L`-module `M` is an
  `R`-linear map that satisfies the Leibniz rule `D [a, b] = [a, D b] - [b, D a]`.
- `LieDerivation.inner`: The natural map from a Lie module to the derivations taking values in it.

## Main statements

- `LieDerivation.eqOn_lieSpan`: two Lie derivations equal on a set are equal on its Lie span.
- `LieDerivation.instLieAlgebra`: the set of Lie derivations from a Lie algebra to itself is a Lie
  algebra.

## Implementation notes

- Mathematically, a Lie derivation is just a derivation on a Lie algebra. However, the current
  implementation of `RingTheory.Derivation` requires a commutative associative algebra, so is
  incompatible with the setting of Lie algebras. Initially, this file is a copy-pasted adaptation of
  the `RingTheory.Derivation.Basic.lean` file.
- Since we don't have right actions of Lie algebras, the second term in the Leibniz rule is written
  as `- [b, D a]`. Within Lie algebras, skew symmetry restores the expected definition `[D a, b]`.
-/

structure LieDerivation (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    extends L →ₗ[R] M where
  protected leibniz' (a b : L) : toLinearMap ⁅a, b⁆ = ⁅a, toLinearMap b⁆ - ⁅b, toLinearMap a⁆

add_decl_doc LieDerivation.toLinearMap

namespace LieDerivation

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instLinearMapClass

def Simps.apply (D : LieDerivation R L M) : L → M := D

initialize_simps_projections LieDerivation (toFun → apply)

attribute [coe] toLinearMap

-- INSTANCE (free from Core): instCoeToLinearMap
