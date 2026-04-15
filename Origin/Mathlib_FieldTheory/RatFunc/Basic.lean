/-
Extracted from FieldTheory/RatFunc/Basic.lean
Genuine: 21 of 35 | Dissolved: 1 | Infrastructure: 13
-/
import Origin.Core

/-!
# The field structure of rational functions

## Main definitions
Working with rational functions as polynomials:
- `RatFunc.instField` provides a field structure
You can use `IsFractionRing` API to treat `RatFunc` as the field of fractions of polynomials:
* `algebraMap K[X] K⟮X⟯` maps polynomials to rational functions
* `IsFractionRing.algEquiv` maps other fields of fractions of `K[X]` to `K⟮X⟯`.

In particular:
* `FractionRing.algEquiv K[X] K⟮X⟯` maps the generic field of
  fraction construction to `K⟮X⟯`. Combine this with `AlgEquiv.restrictScalars` to change
  the `FractionRing K[X] ≃ₐ[K[X]] K⟮X⟯` to `FractionRing K[X] ≃ₐ[K] K⟮X⟯`.

Working with rational functions as fractions:
- `RatFunc.num` and `RatFunc.denom` give the numerator and denominator.
  These values are chosen to be coprime and such that `RatFunc.denom` is monic.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
  - `RatFunc.liftMonoidWithZeroHom` lifts a `K[X] →*₀ G₀` to
    a `K⟮X⟯ →*₀ G₀`, where `[CommRing K] [CommGroupWithZero G₀]`
  - `RatFunc.liftRingHom` lifts a `K[X] →+* L` to a `K⟮X⟯ →+* L`,
    where `[CommRing K] [Field L]`
  - `RatFunc.liftAlgHom` lifts a `K[X] →ₐ[S] L` to a `K⟮X⟯ →ₐ[S] L`,
    where `[CommRing K] [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]`
This is satisfied by injective homs.

We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
  - `RatFunc.map` lifts `K[X] →* R[X]` when `[CommRing K] [CommRing R]`
  - `RatFunc.mapRingHom` lifts `K[X] →+* R[X]` when `[CommRing K] [CommRing R]`
  - `RatFunc.mapAlgHom` lifts `K[X] →ₐ[S] R[X]` when
    `[CommRing K] [IsDomain K] [CommRing R] [IsDomain R]`
-/

universe u v

noncomputable section

open scoped nonZeroDivisors Polynomial

variable {K : Type u}

namespace RatFunc

section Field

variable [CommRing K]

protected irreducible_def zero : K⟮X⟯ :=
  ⟨0⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_zero : (ofFractionRing 0 : K⟮X⟯) = 0 :=
  zero_def.symm

protected irreducible_def add : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_add (p q : FractionRing K[X]) :
    ofFractionRing (p + q) = ofFractionRing p + ofFractionRing q :=
  (add_def _ _).symm

protected irreducible_def sub : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_sub (p q : FractionRing K[X]) :
    ofFractionRing (p - q) = ofFractionRing p - ofFractionRing q :=
  (sub_def _ _).symm

protected irreducible_def neg : K⟮X⟯ → K⟮X⟯
  | ⟨p⟩ => ⟨-p⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_neg (p : FractionRing K[X]) :
    ofFractionRing (-p) = -ofFractionRing p :=
  (neg_def _).symm

protected irreducible_def one : K⟮X⟯ :=
  ⟨1⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_one : (ofFractionRing 1 : K⟮X⟯) = 1 :=
  one_def.symm

protected irreducible_def mul : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_mul (p q : FractionRing K[X]) :
    ofFractionRing (p * q) = ofFractionRing p * ofFractionRing q :=
  (mul_def _ _).symm

section IsDomain

variable [IsDomain K]

protected irreducible_def div : K⟮X⟯ → K⟮X⟯ → K⟮X⟯
  | ⟨p⟩, ⟨q⟩ => ⟨p / q⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_div (p q : FractionRing K[X]) :
    ofFractionRing (p / q) = ofFractionRing p / ofFractionRing q :=
  (div_def _ _).symm

protected irreducible_def inv : K⟮X⟯ → K⟮X⟯
  | ⟨p⟩ => ⟨p⁻¹⟩

-- INSTANCE (free from Core): :

theorem ofFractionRing_inv (p : FractionRing K[X]) :
    ofFractionRing p⁻¹ = (ofFractionRing p)⁻¹ :=
  (inv_def _).symm

-- DISSOLVED: mul_inv_cancel

end IsDomain

section SMul

variable {R : Type*}

protected irreducible_def smul [SMul R (FractionRing K[X])] : R → K⟮X⟯ → K⟮X⟯
  | r, ⟨p⟩ => ⟨r • p⟩

-- INSTANCE (free from Core): [SMul

theorem ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    ofFractionRing (c • p) = c • ofFractionRing p :=
  (smul_def _ _).symm

theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : K⟮X⟯) :
    toFractionRing (c • p) = c • toFractionRing p := by
  cases p
  rw [← ofFractionRing_smul]

theorem smul_eq_C_smul (x : K⟮X⟯) (r : K) : r • x = Polynomial.C r • x := by
  obtain ⟨x⟩ := x
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul, ← ofFractionRing_smul, Localization.smul_mk,
    Localization.smul_mk, smul_eq_mul, Polynomial.smul_eq_C_mul]

section IsDomain

variable [IsDomain K]

variable [Monoid R] [DistribMulAction R K[X]]

variable [IsScalarTower R K[X] K[X]]

theorem mk_smul (c : R) (p q : K[X]) : RatFunc.mk (c • p) q = c • RatFunc.mk p q := by
  letI : SMulZeroClass R (FractionRing K[X]) := inferInstance
  by_cases hq : q = 0
  · rw [hq, mk_zero, mk_zero, ← ofFractionRing_smul, smul_zero]
  · rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq, ← Localization.smul_mk, ←
      ofFractionRing_smul]

-- INSTANCE (free from Core): :

end IsDomain

end SMul

variable (K)

-- INSTANCE (free from Core): [Subsingleton

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instNontrivial
