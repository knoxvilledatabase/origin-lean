/-
Extracted from FieldTheory/PolynomialGaloisGroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Galois Groups of Polynomials

In this file, we introduce the Galois group of a polynomial `p` over a field `F`,
defined as the automorphism group of its splitting field. We also provide
some results about some extension `E` above `p.SplittingField`.

## Main definitions

- `Polynomial.Gal p`: the Galois group of a polynomial p.
- `Polynomial.Gal.restrict p E`: the restriction homomorphism `Gal(E/F) → gal p`.
- `Polynomial.Gal.galAction p E`: the action of `gal p` on the roots of `p` in `E`.

## Main results

- `Polynomial.Gal.restrict_smul`: `restrict p E` is compatible with `gal_action p E`.
- `Polynomial.Gal.galActionHom_injective`: `gal p` acting on the roots of `p` in `E` is faithful.
- `Polynomial.Gal.restrictProd_injective`: `gal (p * q)` embeds as a subgroup of `gal p × gal q`.
- `Polynomial.Gal.card_of_separable`: For a separable polynomial, its Galois group has cardinality
equal to the dimension of its splitting field over `F`.
- `Polynomial.Gal.galActionHom_bijective_of_prime_degree`:
An irreducible polynomial of prime degree with two non-real roots has full Galois group.

## Other results
- `Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`: The number of complex roots
equals the number of real roots plus the number of roots not fixed by complex conjugation
(i.e. with some imaginary component).

-/

assert_not_exists Real

noncomputable section

open scoped Polynomial

open Module

namespace Polynomial

variable {F : Type*} [Field F] (p q : F[X]) (E : Type*) [Field E] [Algebra F E]

def Gal :=
  p.SplittingField ≃ₐ[F] p.SplittingField

deriving Group, Fintype, EquivLike, AlgEquivClass, MulSemiringAction _ p.SplittingField

namespace Gal
