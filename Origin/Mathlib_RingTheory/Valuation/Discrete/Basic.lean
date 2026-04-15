/-
Extracted from RingTheory/Valuation/Discrete/Basic.lean
Genuine: 9 of 11 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ`, a valuation `v : A → Γ` on a ring `A` is
*discrete*, if there is an element `γ : Γˣ` that is `< 1` and generated the range of `v`,
implemented as `MonoidWithZeroHom.valueGroup v`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `γ = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.

Note that this definition of discrete implies that the valuation is nontrivial and of rank one, as
is commonly assumed in number theory. To avoid potential confusion with other definitions of
discrete, we use the name `IsRankOneDiscrete` to refer to discrete valuations in this setting.

## Main Definitions
* `Valuation.IsRankOneDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if there is
  an element `γ : Γˣ` that is `< 1` and generates the range of `v`.
* `Valuation.IsUniformizer`: Given a `Γ`-valued valuation `v` on a ring `R`, an element `π : R` is
  a uniformizer if `v π` is a generator of the value group that is `<1`.
* `Valuation.Uniformizer`: A structure bundling an element of a ring and a proof that it is a
  uniformizer.

## Main Results
* `Valuation.IsUniformizer.of_associated`: An element associated to a uniformizer is itself a
  uniformizer.
* `Valuation.associated_of_isUniformizer`: If two elements are uniformizers, they are associated.
* `Valuation.IsUniformizer.is_generator` A generator of the maximal ideal is a uniformizer when
  the valuation is discrete.
* `Valuation.IsRankOneDiscrete.mk'`: if the `valueGroup` of the valuation `v` is cyclic and
  nontrivial, then `v` is discrete.
* `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`: If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then there exists a uniformizer for `v`.
* `Valuation.isUniformizer_of_maximalIdeal_eq_span`: Given a discrete valuation `v` on a field `K`,
  a generator of the maximal ideal of `v.valuationSubring` is a uniformizer for `v`.
* `Valuation.valuationSubring_isDiscreteValuationRing` : If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then `v.valuationSubring` is a discrete
  valuation ring. This instance is the formalization of Chapter I, Section 1, Proposition 1 in
  [serre1968].
* `IsDiscreteValuationRing.isRankOneDiscrete`: Given a DVR `A` and a field `K` satisfying
  `IsFractionRing A K`, the valuation induced on `K` is discrete.
* `IsDiscreteValuationRing.equivValuationSubring` The ring isomorphism between a DVR and the
  unit ball in its field of fractions endowed with the adic valuation of the maximal ideal.


## TODO
* Relate discrete valuations and discrete valuation rings (contained in the project
  <https://github.com/mariainesdff/LocalClassFieldTheory>)
-/

namespace Valuation

open LinearOrderedCommGroup MonoidWithZeroHom Set Subgroup

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [Ring A] (v : Valuation A Γ)

class IsRankOneDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), zpowers γ = (valueGroup v) ∧ γ < 1

namespace IsRankOneDiscrete

variable [IsRankOneDiscrete v]

lemma exists_generator_lt_one : ∃ (γ : Γˣ), zpowers γ = valueGroup v ∧ γ < 1 :=
  exists_generator_lt_one'

noncomputable def generator : Γˣ := (exists_generator_lt_one v).choose

lemma generator_zpowers_eq_valueGroup :
    zpowers (generator v) = valueGroup v :=
  (exists_generator_lt_one v).choose_spec.1

lemma generator_mem_valueGroup :
    (IsRankOneDiscrete.generator v) ∈ valueGroup v := by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact mem_zpowers (IsRankOneDiscrete.generator v)

lemma generator_lt_one : generator v < 1 :=
  (exists_generator_lt_one v).choose_spec.2

-- DISSOLVED: generator_ne_one

lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    Units.val '' (zpowers (generator w)) = range w \ {0} := by
  rw [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    ↑(generator w) ∈ range w := by
  apply diff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

-- DISSOLVED: generator_ne_zero

noncomputable def generator' : valueGroup v := ⟨generator v, generator_mem_valueGroup v⟩
