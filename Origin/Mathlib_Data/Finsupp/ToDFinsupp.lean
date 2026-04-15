/-
Extracted from Data/Finsupp/ToDFinsupp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conversion between `Finsupp` and homogeneous `DFinsupp`

This module provides conversions between `Finsupp` and `DFinsupp`.
It is in its own file since neither `Finsupp` or `DFinsupp` depend on each other.

## Main definitions

* "identity" maps between `Finsupp` and `DFinsupp`:
  * `Finsupp.toDFinsupp : (ι →₀ M) → (Π₀ i : ι, M)`
  * `DFinsupp.toFinsupp : (Π₀ i : ι, M) → (ι →₀ M)`
  * Bundled equiv versions of the above:
    * `finsuppEquivDFinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
    * `finsuppAddEquivDFinsupp : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
    * `finsuppLequivDFinsupp R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`
* stronger versions of `Finsupp.split`:
  * `sigmaFinsuppEquivDFinsupp : ((Σ i, η i) →₀ N) ≃ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppAddEquivDFinsupp : ((Σ i, η i) →₀ N) ≃+ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppLequivDFinsupp : ((Σ i, η i) →₀ N) ≃ₗ[R] (Π₀ i, (η i →₀ N))`

## Theorems

The defining features of these operations is that they preserve the function and support:

* `Finsupp.toDFinsupp_coe`
* `Finsupp.toDFinsupp_support`
* `DFinsupp.toFinsupp_coe`
* `DFinsupp.toFinsupp_support`

and therefore map `Finsupp.single` to `DFinsupp.single` and vice versa:

* `Finsupp.toDFinsupp_single`
* `DFinsupp.toFinsupp_single`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to `Finsupp.toDFinsupp`:

* `finsupp_add_equiv_dfinsupp_apply`
* `finsupp_lequiv_dfinsupp_apply`
* `finsupp_add_equiv_dfinsupp_symm_apply`
* `finsupp_lequiv_dfinsupp_symm_apply`

## Implementation notes

We provide `DFinsupp.toFinsupp` and `finsuppEquivDFinsupp` computably by adding
`[DecidableEq ι]` and `[Π m : M, Decidable (m ≠ 0)]` arguments. To aid with definitional unfolding,
these arguments are also present on the `noncomputable` equivs.
-/

variable {ι : Type*} {R : Type*} {M : Type*}

/-! ### Basic definitions and lemmas -/

section Defs

def Finsupp.toDFinsupp [Zero M] (f : ι →₀ M) : Π₀ _ : ι, M where
  toFun := f
  support' :=
    Trunc.mk
      ⟨f.support.1, fun i => (Classical.em (f i = 0)).symm.imp_left Finsupp.mem_support_iff.mpr⟩
