/-
Extracted from RingTheory/LaurentSeries.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Laurent Series

In this file we define `LaurentSeries R`, the formal Laurent series over `R`, here an *arbitrary*
type with a zero. They are denoted `R⸨X⸩`.

## Main Definitions

* Defines `LaurentSeries` as an abbreviation for `HahnSeries ℤ`.
* Defines `hasseDeriv` of a Laurent series with coefficients in a module over a ring.
* Provides a coercion from power series `R⟦X⟧` into `R⸨X⸩` given by `HahnSeries.ofPowerSeries`.
* Defines `LaurentSeries.powerSeriesPart`
* Defines the localization map `LaurentSeries.of_powerSeries_localization` which evaluates to
  `HahnSeries.ofPowerSeries`.
* Embedding of rational functions into Laurent series, provided as a coercion, utilizing
  the underlying `RatFunc.coeAlgHom`.
* Study of the `X`-Adic valuation on the ring of Laurent series over a field
* In `LaurentSeries.uniformContinuous_coeff` we show that sending a Laurent series to its `d`th
  coefficient is uniformly continuous, ensuring that it sends a Cauchy filter `ℱ` in `K⸨X⸩`
  to a Cauchy filter in `K`: since this latter is given the discrete topology, this provides an
  element `LaurentSeries.Cauchy.coeff ℱ d` in `K` that serves as `d`th coefficient of the Laurent
  series to which the filter `ℱ` converges.

## Main Results

* Basic properties of Hasse derivatives
### About the `X`-Adic valuation:
* The (integral) valuation of a power series is the order of the first non-zero coefficient, see
  `LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero`.
* The valuation of a Laurent series is the order of the first non-zero coefficient, see
  `LaurentSeries.valuation_le_iff_coeff_lt_eq_zero`.
* Every Laurent series of valuation less than `(1 : ℤᵐ⁰)` comes from a power series, see
  `LaurentSeries.val_le_one_iff_eq_coe`.
* The uniform space of `LaurentSeries` over a field is complete, formalized in the instance
  `instLaurentSeriesComplete`.
* The field of rational functions is dense in `LaurentSeries`: this is the declaration
  `LaurentSeries.coe_range_dense` and relies principally upon `LaurentSeries.exists_ratFunc_val_lt`,
  stating that for every Laurent series `f` and every `γ : ℤᵐ⁰` one can find a rational function `Q`
  such that the `X`-adic valuation `v` satisfies `v (f - Q) < γ`.
* In `LaurentSeries.valuation_compare` we prove that the extension of the `X`-adic valuation from
  `K⟮X⟯` up to its abstract completion coincides, modulo the isomorphism with `K⸨X⸩`, with the
  `X`-adic valuation on `K⸨X⸩`.
* The two declarations `LaurentSeries.mem_integers_of_powerSeries` and
  `LaurentSeries.exists_powerSeries_of_memIntegers` show that an element in the completion of
  `K⟮X⟯` is in the unit ball if and only if it comes from a power series through the
  isomorphism `LaurentSeriesRingEquiv`.
* `LaurentSeries.powerSeriesAlgEquiv` is the `K`-algebra isomorphism between `K⟦X⟧`
  and the unit ball inside the `X`-adic completion of `K⟮X⟯`.

## Implementation details

* Since `LaurentSeries` is just an abbreviation of `HahnSeries ℤ`, the definition of the
  coefficients is given in terms of `HahnSeries.coeff` and this forces sometimes to go
  back-and-forth from `X : R⸨X⸩` to `single 1 1 : R⟦ℤ⟧`.
* To prove the isomorphism between the `X`-adic completion of `K⟮X⟯` and `K⸨X⸩` we construct
  two completions of `K⟮X⟯`: the first (`LaurentSeries.ratfuncAdicComplPkg`) is its abstract
  uniform completion; the second (`LaurentSeries.LaurentSeriesPkg`) is simply `K⸨X⸩`, once we prove
  that it is complete and contains `K⟮X⟯` as a dense subspace. The isomorphism is the
  comparison equivalence, expressing the mathematical idea that the completion "is unique". It is
  `LaurentSeries.comparePkg`.
* For applications to `K⟦X⟧` it is actually more handy to use the *inverse* of the above
  equivalence: `LaurentSeries.LaurentSeriesAlgEquiv` is the *topological, algebra equivalence*
  `K⸨X⸩ ≃ₐ[K] RatFuncAdicCompl K`.
* In order to compare `K⟦X⟧` with the valuation subring in the `X`-adic completion of
  `K⟮X⟯` we consider its alias `LaurentSeries.powerSeries_as_subring` as a subring of `K⸨X⸩`,
  that is itself clearly isomorphic (via the inverse of `LaurentSeries.powerSeriesEquivSubring`)
  to `K⟦X⟧`.

-/

universe u

open scoped PowerSeries

open HahnSeries Polynomial

noncomputable section

abbrev LaurentSeries (R : Type u) [Zero R] := R⟦ℤ⟧

variable {R : Type*}

namespace LaurentSeries

scoped notation:9000 R "⸨X⸩" => LaurentSeries R

end

section HasseDeriv

def hasseDeriv (R : Type*) {V : Type*} [AddCommGroup V] [Semiring R] [Module R V] (k : ℕ) :
    V⸨X⸩ →ₗ[R] V⸨X⸩ where
  toFun f := HahnSeries.ofSuppBddBelow (fun n ↦ Ring.choose (n + k) k • f.coeff (n + k)) <| by
    refine ⟨f.order - k, fun x h ↦ ?_⟩
    contrapose! h
    rw [Function.notMem_support, coeff_eq_zero_of_lt_order <| lt_sub_iff_add_lt.mp h, smul_zero]
  map_add' f g := by
    ext
    simp only [ofSuppBddBelow, coeff_add', Pi.add_apply, smul_add]
  map_smul' r f := by
    ext
    simp only [ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply, smul_comm r]

variable [Semiring R] {V : Type*} [AddCommGroup V] [Module R V]
