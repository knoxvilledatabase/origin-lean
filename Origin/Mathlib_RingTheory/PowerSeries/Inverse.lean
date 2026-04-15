/-
Extracted from RingTheory/PowerSeries/Inverse.lean
Genuine: 28 | Conflates: 0 | Dissolved: 15 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # Formal power series - Inverses

If the constant coefficient of a formal (univariate) power series is invertible,
then this formal power series is invertible.
(See the discussion in `Mathlib.RingTheory.MvPowerSeries.Inverse` for
the construction.)

Formal (univariate) power series over a local ring form a local ring.

Formal (univariate) power series over a field form a discrete valuation ring, and a normalization
monoid. The definition `residueFieldOfPowerSeries` provides the isomorphism between the residue
field of `k⟦X⟧` and `k`, when `k` is a field.

-/

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section Ring

variable [Ring R]

protected def inv.aux : R → R⟦X⟧ → R⟦X⟧ :=
  MvPowerSeries.inv.aux

theorem coeff_inv_aux (n : ℕ) (a : R) (φ : R⟦X⟧) :
    coeff R n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (inv.aux a φ) else 0 := by
  rw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) ↦ (single () a, single () b))
    fun (f, g) ↦ (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
    obtain H | H := le_or_lt n j
    · aesop
    rw [if_pos H, if_pos]
    · rfl
    refine ⟨?_, fun hh ↦ H.not_le ?_⟩
    · rintro ⟨⟩
      simpa [Finsupp.single_eq_same] using le_of_lt H
    · simpa [Finsupp.single_eq_same] using hh ()

def invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit φ u

theorem coeff_invOfUnit (n : ℕ) (φ : R⟦X⟧) (u : Rˣ) :
    coeff R n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff R x.1 φ * coeff R x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹ : R) φ

@[simp]
theorem constantCoeff_invOfUnit (φ : R⟦X⟧) (u : Rˣ) :
    constantCoeff R (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, if_pos rfl]

@[simp]
theorem mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff R φ = u) :
    φ * invOfUnit φ u = 1 :=
  MvPowerSeries.mul_invOfUnit φ u <| h

@[simp]
theorem invOfUnit_mul (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff R φ = u) :
    invOfUnit φ u * φ = 1 :=
  MvPowerSeries.invOfUnit_mul φ u h

theorem isUnit_iff_constantCoeff {φ : R⟦X⟧} :
    IsUnit φ ↔ IsUnit (constantCoeff R φ) :=
  MvPowerSeries.isUnit_iff_constantCoeff

theorem sub_const_eq_shift_mul_X (φ : R⟦X⟧) :
    φ - C R (constantCoeff R φ) = (mk fun p ↦ coeff R (p + 1) φ) * X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)

theorem sub_const_eq_X_mul_shift (φ : R⟦X⟧) :
    φ - C R (constantCoeff R φ) = X * mk fun p ↦ coeff R (p + 1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

end Ring

section Field

variable {k : Type*} [Field k]

protected def inv : k⟦X⟧ → k⟦X⟧ :=
  MvPowerSeries.inv

instance : Inv k⟦X⟧ := ⟨PowerSeries.inv⟩

theorem inv_eq_inv_aux (φ : k⟦X⟧) : φ⁻¹ = inv.aux (constantCoeff k φ)⁻¹ φ :=
  rfl

theorem coeff_inv (n) (φ : k⟦X⟧) :
    coeff k n φ⁻¹ =
      if n = 0 then (constantCoeff k φ)⁻¹
      else
        -(constantCoeff k φ)⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff k x.1 φ * coeff k x.2 φ⁻¹ else 0 := by
  rw [inv_eq_inv_aux, coeff_inv_aux n (constantCoeff k φ)⁻¹ φ]

@[simp]
theorem constantCoeff_inv (φ : k⟦X⟧) : constantCoeff k φ⁻¹ = (constantCoeff k φ)⁻¹ :=
  MvPowerSeries.constantCoeff_inv φ

theorem inv_eq_zero {φ : k⟦X⟧} : φ⁻¹ = 0 ↔ constantCoeff k φ = 0 :=
  MvPowerSeries.inv_eq_zero

-- DISSOLVED: zero_inv

-- DISSOLVED: invOfUnit_eq

@[simp]
theorem invOfUnit_eq' (φ : k⟦X⟧) (u : Units k) (h : constantCoeff k φ = u) :
    invOfUnit φ u = φ⁻¹ :=
  MvPowerSeries.invOfUnit_eq' φ _ h

-- DISSOLVED: mul_inv_cancel

-- DISSOLVED: inv_mul_cancel

-- DISSOLVED: eq_mul_inv_iff_mul_eq

-- DISSOLVED: eq_inv_iff_mul_eq_one

-- DISSOLVED: inv_eq_iff_mul_eq_one

protected theorem mul_inv_rev (φ ψ : k⟦X⟧) : (φ * ψ)⁻¹ = ψ⁻¹ * φ⁻¹ :=
  MvPowerSeries.mul_inv_rev _ _

instance : InvOneClass k⟦X⟧ :=
  { inferInstanceAs <| InvOneClass <| MvPowerSeries Unit k with }

@[simp]
theorem C_inv (r : k) : (C k r)⁻¹ = C k r⁻¹ :=
  MvPowerSeries.C_inv _

@[simp]
theorem X_inv : (X : k⟦X⟧)⁻¹ = 0 :=
  MvPowerSeries.X_inv _

theorem smul_inv (r : k) (φ : k⟦X⟧) : (r • φ)⁻¹ = r⁻¹ • φ⁻¹ :=
  MvPowerSeries.smul_inv _ _

-- DISSOLVED: firstUnitCoeff

-- DISSOLVED: Inv_divided_by_X_pow_order

-- DISSOLVED: Inv_divided_by_X_pow_order_rightInv

-- DISSOLVED: Inv_divided_by_X_pow_order_leftInv

open scoped Classical

def Unit_of_divided_by_X_pow_order (f : k⟦X⟧) : k⟦X⟧ˣ :=
  if hf : f = 0 then 1
  else
    { val := divided_by_X_pow_order hf
      inv := Inv_divided_by_X_pow_order hf
      val_inv := Inv_divided_by_X_pow_order_rightInv hf
      inv_val := Inv_divided_by_X_pow_order_leftInv hf }

-- DISSOLVED: isUnit_divided_by_X_pow_order

-- DISSOLVED: Unit_of_divided_by_X_pow_order_nonzero

@[simp]
theorem Unit_of_divided_by_X_pow_order_zero : Unit_of_divided_by_X_pow_order (0 : k⟦X⟧) = 1 := by
  simp only [Unit_of_divided_by_X_pow_order, dif_pos]

-- DISSOLVED: eq_divided_by_X_pow_order_Iff_Unit

end Field

section IsLocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f]

@[instance]
theorem map.isLocalHom : IsLocalHom (map f) :=
  MvPowerSeries.map.isLocalHom f

alias map.isLocalRingHom := map.isLocalHom

variable [IsLocalRing R]

instance : IsLocalRing R⟦X⟧ :=
  { inferInstanceAs <| IsLocalRing <| MvPowerSeries Unit R with }

end IsLocalRing

section DiscreteValuationRing

variable {k : Type*} [Field k]

open DiscreteValuationRing

theorem hasUnitMulPowIrreducibleFactorization :
    HasUnitMulPowIrreducibleFactorization k⟦X⟧ :=
  ⟨X, And.intro X_irreducible
      (by
        intro f hf
        use f.order.lift (order_finite_iff_ne_zero.mpr hf)
        use Unit_of_divided_by_X_pow_order f
        simp only [Unit_of_divided_by_X_pow_order_nonzero hf]
        exact self_eq_X_pow_order_mul_divided_by_X_pow_order hf)⟩

instance : UniqueFactorizationMonoid k⟦X⟧ :=
  hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

instance : DiscreteValuationRing k⟦X⟧ :=
  ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization

instance isNoetherianRing : IsNoetherianRing k⟦X⟧ :=
  PrincipalIdealRing.isNoetherianRing

theorem maximalIdeal_eq_span_X : IsLocalRing.maximalIdeal (k⟦X⟧) = Ideal.span {X} := by
  have hX : (Ideal.span {(X : k⟦X⟧)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one X_prime
    · intro I f hI hfX hfI
      rw [Ideal.mem_span_singleton, X_dvd_iff] at hfX
      have hfI0 : C k (f 0) ∈ I := by
        have : C k (f 0) = f - (f - C k (f 0)) := by rw [sub_sub_cancel]
        rw [this]
        apply Ideal.sub_mem I hfI
        apply hI
        rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, ←
          coeff_zero_eq_constantCoeff_apply, sub_eq_zero, coeff_zero_eq_constantCoeff]
        rfl
      rw [← Ideal.eq_top_iff_one]
      apply Ideal.eq_top_of_isUnit_mem I hfI0 (IsUnit.map (C k) (Ne.isUnit hfX))
  rw [IsLocalRing.eq_maximalIdeal hX]

instance : NormalizationMonoid k⟦X⟧ where
  normUnit f := (Unit_of_divided_by_X_pow_order f)⁻¹
  normUnit_zero := by simp only [Unit_of_divided_by_X_pow_order_zero, inv_one]
  normUnit_mul  := fun hf hg ↦ by
    simp only [← mul_inv, inv_inj]
    simp only [Unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
      Unit_of_divided_by_X_pow_order_nonzero hf, Unit_of_divided_by_X_pow_order_nonzero hg,
      Units.ext_iff, val_unitOfInvertible, Units.val_mul, divided_by_X_pow_orderMul]
  normUnit_coe_units := by
    intro u
    set u₀ := u.1 with hu
    have h₀ : IsUnit u₀ := ⟨u, hu.symm⟩
    rw [inv_inj, Units.ext_iff, ← hu, Unit_of_divided_by_X_pow_order_nonzero h₀.ne_zero]
    exact ((eq_divided_by_X_pow_order_Iff_Unit h₀.ne_zero).mpr h₀).symm

theorem normUnit_X : normUnit (X : k⟦X⟧) = 1 := by
  simp [normUnit, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero]

theorem X_eq_normalizeX : (X : k⟦X⟧) = normalize X := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

open UniqueFactorizationMonoid Classical

-- DISSOLVED: normalized_count_X_eq_of_coe

open IsLocalRing

theorem ker_coeff_eq_max_ideal : RingHom.ker (constantCoeff k) = maximalIdeal _ :=
  Ideal.ext fun _ ↦ by
    rw [RingHom.mem_ker, maximalIdeal_eq_span_X, Ideal.mem_span_singleton, X_dvd_iff]

def residueFieldOfPowerSeries : ResidueField k⟦X⟧ ≃+* k :=
  (Ideal.quotEquivOfEq (ker_coeff_eq_max_ideal).symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

end DiscreteValuationRing

end PowerSeries

end
