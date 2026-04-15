/-
Extracted from RingTheory/DedekindDomain/Instances.lean
Genuine: 4 of 24 | Dissolved: 0 | Infrastructure: 20
-/
import Origin.Core

/-!
# Instances for Dedekind domains
This file contains various instances to work with localization of a ring extension.

A very common situation in number theory is to have an extension of (say) Dedekind domains `R` and
`S`, and to prove a property of this extension it is useful to consider the localization `Rₚ` of `R`
at `P`, a prime ideal of `R`. One also works with the corresponding localization `Sₚ` of `S` and the
fraction fields `K` and `L` of `R` and `S`. In this situation there are many compatible algebra
structures and various properties of the rings involved. Another situation is when we have a
tower extension `R ⊆ S ⊆ T` and thus we work with `Rₚ ⊆ Sₚ ⊆ Tₚ` where
`Tₚ` is the localization of `T` at `P`. This file contains a collection of such instances.

## Implementation details
In general one wants all the results below for any algebra satisfying `IsLocalization`, but those
cannot be instances (since Lean has no way of guessing the submonoid). Having the instances in the
special case of *the* localization at a prime ideal is useful in working with Dedekind domains.

-/

open nonZeroDivisors IsLocalization Algebra Module IsFractionRing IsScalarTower

attribute [local instance] FractionRing.liftAlgebra

variable {R : Type*} (S : Type*) (T : Type*) [CommRing R] [CommRing S] [CommRing T] [IsDomain R]
  [IsDomain S] [IsDomain T] [Algebra R S]

local notation3 "K" => FractionRing R

local notation3 "L" => FractionRing S

local notation3 "F" => FractionRing T

theorem algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul {A : Type*} (B : Type*)
    [CommSemiring A] [CommSemiring B] [Algebra A B] [NoZeroDivisors B] [FaithfulSMul A B]
    {S : Submonoid A} (hS : S ≤ A⁰) : algebraMapSubmonoid B S ≤ B⁰ :=
  map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective A B) hS

variable (Rₘ Sₘ : Type*) [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ] [IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] {M : Submonoid R} [IsLocalization M Rₘ]
    [Algebra Rₘ Sₘ] [Algebra S Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ]
    [IsScalarTower R S Sₘ] [IsLocalization (algebraMapSubmonoid S M) Sₘ]
    [Algebra (FractionRing Rₘ) (FractionRing Sₘ)]
    [IsScalarTower Rₘ (FractionRing Rₘ) (FractionRing Sₘ)]

set_option backward.isDefEq.respectTransparency false in

include R S in

theorem FractionRing.isSeparable_of_isLocalization (hM : M ≤ R⁰) :
    Algebra.IsSeparable (FractionRing Rₘ) (FractionRing Sₘ) := by
  let M' := algebraMapSubmonoid S M
  have hM' : algebraMapSubmonoid S M ≤ S⁰ := algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul
    _ hM
  let f₁ : Rₘ →+* K := map _ (T := R⁰) (RingHom.id R) hM
  let f₂ : Sₘ →+* L := map _ (T := S⁰) (RingHom.id S) hM'
  algebraize [f₁, f₂]
  have := localization_isScalarTower_of_submonoid_le Rₘ K _ _ hM
  have := localization_isScalarTower_of_submonoid_le Sₘ L _ _ hM'
  have := isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have := isFractionRing_of_isDomain_of_isLocalization M' Sₘ L
  have : IsDomain Rₘ := isDomain_of_le_nonZeroDivisors _ hM
  apply Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv Rₘ K).symm.toRingEquiv
    (FractionRing.algEquiv Sₘ L).symm.toRingEquiv
  apply ringHom_ext R⁰
  ext
  simp only [RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing R), AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
    algebraMap_apply R S L, algebraMap_apply S Sₘ L, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  simp only [← algebraMap_apply]
  rw [algebraMap_apply R Rₘ (FractionRing Rₘ), ← algebraMap_apply Rₘ, ← algebraMap_apply]

end

variable {P : Ideal R} [P.IsPrime]

local notation3 "P'" => algebraMapSubmonoid S P.primeCompl

local notation3 "Rₚ" => Localization.AtPrime P

local notation3 "Sₚ" => Localization P'

variable [FaithfulSMul R S]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

noncomputable abbrev Localization.AtPrime.liftAlgebra : Algebra Sₚ L :=
  (map _ (T := S⁰) (RingHom.id S)
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      P.primeCompl_le_nonZeroDivisors)).toAlgebra

attribute [local instance] Localization.AtPrime.liftAlgebra

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

example : instAlgebraLocalizationAtPrime P = instAlgebraAtPrimeFractionRing (S := R) := by

  with_reducible_and_instances rfl

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [IsDedekindDomain

-- INSTANCE (free from Core): [IsDedekindDomain

-- INSTANCE (free from Core): [Algebra.IsSeparable

local notation3 "P''" => algebraMapSubmonoid T P.primeCompl

local notation3 "Tₚ" => Localization P''

variable [Algebra S T] [Algebra R T] [IsScalarTower R S T]

-- INSTANCE (free from Core): :

noncomputable abbrev Localization.AtPrime.algebra_localization_localization :
    Algebra Sₚ Tₚ := localizationAlgebra P' T

attribute [local instance] Localization.AtPrime.algebra_localization_localization

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Module.Finite

-- INSTANCE (free from Core): [IsTorsionFree

-- INSTANCE (free from Core): [Algebra.IsIntegral

variable [IsTorsionFree R T]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [IsTorsionFree
