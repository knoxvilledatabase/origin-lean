/-
Extracted from LinearAlgebra/RootSystem/RootPositive.lean
Genuine: 2 of 4 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Invariant and root-positive bilinear forms on root pairings

This file contains basic results on Weyl-invariant inner products for root systems and root data.
Given a root pairing we define a structure which contains a bilinear form together with axioms for
reflection-invariance, symmetry, and strict positivity on all roots.  We show that root-positive
forms display the same sign behavior as the canonical pairing between roots and coroots.

Root-positive forms show up naturally as the invariant forms for symmetrizable Kac-Moody Lie
algebras.  In the finite case, the canonical polarization yields a root-positive form that is
positive semi-definite on weight space and positive-definite on the span of roots.

## Main definitions / results:

* `RootPairing.InvariantForm`: an invariant bilinear form on a root pairing.
* `RootPairing.RootPositiveForm`: Given a root pairing this is a structure which contains a
  bilinear form together with axioms for reflection-invariance, symmetry, and strict positivity on
  all roots.
* `RootPairing.zero_lt_pairingIn_iff`: sign relations between `RootPairing.pairingIn` and a
  root-positive form.
* `RootPairing.pairing_eq_zero_iff`: symmetric vanishing condition for `RootPairing.pairing`
* `RootPairing.coxeterWeight_nonneg`: All pairs of roots have non-negative Coxeter weight.
* `RootPairing.coxeterWeight_zero_iff_isOrthogonal` : A Coxeter weight vanishes iff the roots are
  orthogonal.

-/

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R S M N : Type*} [CommRing S] [LinearOrder S]
  [CommRing R] [Algebra S R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

-- DISSOLVED: InvariantForm

namespace InvariantForm

variable {P : RootPairing ι R M N} (B : P.InvariantForm) (i j : ι)

-- DISSOLVED: apply_root_ne_zero

lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← B.isOrthogonal_reflection j]
  rw [reflection_apply, reflection_apply_self, root_coroot'_eq_pairing, LinearMap.map_sub₂,
    LinearMap.map_smul₂, smul_eq_mul, map_neg, map_neg, mul_neg, neg_sub_neg]

lemma pairing_mul_eq_pairing_mul_swap :
    P.pairing j i * B.form (P.root i) (P.root i) =
    P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [← B.two_mul_apply_root_root i j, ← B.two_mul_apply_root_root j i, ← B.symm.eq,
    RingHom.id_apply]
