/-
Extracted from RingTheory/MvPolynomial/Localization.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Localization and multivariate polynomial rings

In this file we show some results connecting multivariate polynomial rings and localization.

## Main results

- `MvPolynomial.isLocalization`: If `S` is the localization of `R` at a submonoid `M`, then
  `MvPolynomial σ S` is the localization of `MvPolynomial σ R` at the image of `M` in
  `MvPolynomial σ R`.

-/

variable {σ R : Type*} [CommRing R] (M : Submonoid R)

variable (S : Type*) [CommRing S] [Algebra R S]

namespace MvPolynomial

variable [IsLocalization M S]

attribute [local instance] algebraMvPolynomial

-- INSTANCE (free from Core): isLocalization

lemma isLocalization_C_mk' (a : R) (m : M) :
    C (IsLocalization.mk' S a m) = IsLocalization.mk' (MvPolynomial σ S) (C (σ := σ) a)
      ⟨C m, Submonoid.mem_map_of_mem C m.property⟩ := by
  simp_rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_def, map_C, ← map_mul,
    IsLocalization.mk'_spec]

end MvPolynomial

namespace IsLocalization.Away

open MvPolynomial

variable (r : R) [IsLocalization.Away r S]

set_option backward.privateInPublic true in

private noncomputable

def auxHom : (MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 }) →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span { C r * X () - 1}) (aeval (fun _ ↦ invSelf r)) <| by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro p ⟨q, rfl⟩
      simp
    · simp
    · intro p q _ _ hp hq
      simp [hp, hq]
    · intro a x _ hx
      simp [hx]
