/-
Extracted from Analysis/Fourier/AddCircle.lean
Genuine: 42 | Conflates: 0 | Dissolved: 5 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.FundThmCalculus

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series for functions on the additive circle
`AddCircle T = ℝ / ℤ • T`.

## Main definitions

* `haarAddCircle`, Haar measure on `AddCircle T`, normalized to have total measure `1`. (Note
  that this is not the same normalisation as the standard measure defined in `Integral.Periodic`,
  so we do not declare it as a `MeasureSpace` instance, to avoid confusion.)
* for `n : ℤ`, `fourier n` is the monomial `fun x => exp (2 π i n x / T)`,
  bundled as a continuous map from `AddCircle T` to `ℂ`.
* `fourierBasis` is the Hilbert basis of `Lp ℂ 2 haarAddCircle` given by the images of the
  monomials `fourier n`.
* `fourierCoeff f n`, for `f : AddCircle T → E` (with `E` a complete normed `ℂ`-vector space), is
  the `n`-th Fourier coefficient of `f`, defined as an integral over `AddCircle T`. The lemma
  `fourierCoeff_eq_intervalIntegral` expresses this as an integral over `[a, a + T]` for any real
  `a`.
* `fourierCoeffOn`, for `f : ℝ → E` and `a < b` reals, is the `n`-th Fourier
  coefficient of the unique periodic function of period `b - a` which agrees with `f` on `(a, b]`.
  The lemma `fourierCoeffOn_eq_integral` expresses this as an integral over `[a, b]`.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(AddCircle T, ℂ)`, i.e. that its `Submodule.topologicalClosure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourierLp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `AddCircle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourierBasis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`hasSum_fourier_series_L2`). Parseval's identity, `tsum_sq_fourierCoeff`, is
a direct consequence.

For continuous maps `f : AddCircle T → ℂ`, the theorem
`hasSum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i : ℤ), fourierCoeff f i * fourier i`
converges to `f` in the uniform-convergence topology of `C(AddCircle T, ℂ)`.
-/

noncomputable section

open scoped ENNReal ComplexConjugate Real

open TopologicalSpace ContinuousMap MeasureTheory MeasureTheory.Measure Algebra Submodule Set

variable {T : ℝ}

namespace AddCircle

/-! ### Measure on `AddCircle T`

In this file we use the Haar measure on `AddCircle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `Topology.Instances.AddCircle`). -/

variable [hT : Fact (0 < T)]

def haarAddCircle : Measure (AddCircle T) :=
  addHaarMeasure ⊤

instance : IsAddHaarMeasure (@haarAddCircle T _) :=
  Measure.isAddHaarMeasure_addHaarMeasure ⊤

instance : IsProbabilityMeasure (@haarAddCircle T _) :=
  IsProbabilityMeasure.mk addHaarMeasure_self

theorem volume_eq_smul_haarAddCircle :
    (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _) :=
  rfl

end AddCircle

open AddCircle

section Monomials

def fourier (n : ℤ) : C(AddCircle T, ℂ) where
  toFun x := toCircle (n • x :)
  continuous_toFun := continuous_induced_dom.comp <| continuous_toCircle.comp <| continuous_zsmul _

@[simp]
theorem fourier_apply {n : ℤ} {x : AddCircle T} : fourier n x = toCircle (n • x :) :=
  rfl

theorem fourier_coe_apply {n : ℤ} {x : ℝ} :
    fourier n (x : AddCircle T) = Complex.exp (2 * π * Complex.I * n * x / T) := by
  rw [fourier_apply, ← QuotientAddGroup.mk_zsmul, toCircle, Function.Periodic.lift_coe,
    Circle.coe_exp, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, zsmul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  norm_num
  congr 1; ring

@[simp]
theorem fourier_coe_apply' {n : ℤ} {x : ℝ} :
    toCircle (n • (x : AddCircle T) :) = Complex.exp (2 * π * Complex.I * n * x / T) := by
  rw [← fourier_apply]; exact fourier_coe_apply

theorem fourier_zero {x : AddCircle T} : fourier 0 x = 1 := by
  induction x using QuotientAddGroup.induction_on
  simp only [fourier_coe_apply]
  norm_num

theorem fourier_zero' {x : AddCircle T} : @toCircle T 0 = (1 : ℂ) := by
  have : fourier 0 x = @toCircle T 0 := by rw [fourier_apply, zero_smul]
  rw [← this]; exact fourier_zero

theorem fourier_eval_zero (n : ℤ) : fourier n (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.mk_zero, fourier_coe_apply, Complex.ofReal_zero, mul_zero,
    zero_div, Complex.exp_zero]

theorem fourier_one {x : AddCircle T} : fourier 1 x = toCircle x := by rw [fourier_apply, one_zsmul]

theorem fourier_neg {n : ℤ} {x : AddCircle T} : fourier (-n) x = conj (fourier n x) := by
  induction x using QuotientAddGroup.induction_on
  simp_rw [fourier_apply, toCircle]
  rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_zsmul]
  simp_rw [Function.Periodic.lift_coe, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg,
    neg_smul, mul_neg]

@[simp]
theorem fourier_neg' {n : ℤ} {x : AddCircle T} : @toCircle T (-(n • x)) = conj (fourier n x) := by
  rw [← neg_smul, ← fourier_apply]; exact fourier_neg

theorem fourier_add {m n : ℤ} {x : AddCircle T} : fourier (m+n) x = fourier m x * fourier n x := by
  simp_rw [fourier_apply, add_zsmul, toCircle_add, Circle.coe_mul]

@[simp]
theorem fourier_add' {m n : ℤ} {x : AddCircle T} :
    toCircle ((m + n) • x :) = fourier m x * fourier n x := by
  rw [← fourier_apply]; exact fourier_add

theorem fourier_norm [Fact (0 < T)] (n : ℤ) : ‖@fourier T n‖ = 1 := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  have : ∀ x : AddCircle T, ‖fourier n x‖ = 1 := fun x => Circle.abs_coe _
  simp_rw [this]
  exact @ciSup_const _ _ _ Zero.instNonempty _

-- DISSOLVED: fourier_add_half_inv_index

def fourierSubalgebra : StarSubalgebra ℂ C(AddCircle T, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range fourier)
  star_mem' := by
    show Algebra.adjoin ℂ (range (fourier (T := T))) ≤
      star (Algebra.adjoin ℂ (range (fourier (T := T))))
    refine adjoin_le ?_
    rintro - ⟨n, rfl⟩
    exact subset_adjoin ⟨-n, ext fun _ => fourier_neg⟩

theorem fourierSubalgebra_coe :
    Subalgebra.toSubmodule (@fourierSubalgebra T).toSubalgebra = span ℂ (range (@fourier T)) := by
  apply adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · ext1 z; exact fourier_zero
  · rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext1 z
    exact fourier_add

variable [hT : Fact (0 < T)]

theorem fourierSubalgebra_separatesPoints : (@fourierSubalgebra T).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, ?_⟩
  dsimp only; rw [fourier_one, fourier_one]
  contrapose! hxy
  rw [Subtype.coe_inj] at hxy
  exact injective_toCircle hT.elim.ne' hxy

theorem fourierSubalgebra_closure_eq_top : (@fourierSubalgebra T).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints fourierSubalgebra
    fourierSubalgebra_separatesPoints

theorem span_fourier_closure_eq_top : (span ℂ (range <| @fourier T)).topologicalClosure = ⊤ := by
  rw [← fourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    fourierSubalgebra_closure_eq_top

abbrev fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Lp ℂ p (@haarAddCircle T hT) :=
  toLp (E := ℂ) p haarAddCircle ℂ (fourier n)

theorem coeFn_fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    @fourierLp T hT p _ n =ᵐ[haarAddCircle] fourier n :=
  coeFn_toLp haarAddCircle (fourier n)

theorem span_fourierLp_closure_eq_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (span ℂ (range (@fourierLp T _ p _))).topologicalClosure = ⊤ := by
  convert
    (ContinuousMap.toLp_denseRange ℂ (@haarAddCircle T hT) ℂ hp).topologicalClosure_map_submodule
      span_fourier_closure_eq_top
  erw [map_span, range_comp]
  simp only [ContinuousLinearMap.coe_coe]

theorem orthonormal_fourier : Orthonormal ℂ (@fourierLp T _ 2 _) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [ContinuousMap.inner_toLp (@haarAddCircle T hT) (fourier i) (fourier j)]
  simp_rw [← fourier_neg, ← fourier_add]
  split_ifs with h
  · simp_rw [h, neg_add_cancel]
    have : ⇑(@fourier T 0) = (fun _ => 1 : AddCircle T → ℂ) := by ext1; exact fourier_zero
    rw [this, integral_const, measure_univ, ENNReal.one_toReal, Complex.real_smul,
      Complex.ofReal_one, mul_one]
  have hij : -i + j ≠ 0 := by
    rw [add_comm]
    exact sub_ne_zero.mpr (Ne.symm h)
  convert integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
    (fourier_add_half_inv_index hij hT.elim)

end Monomials

section ScopeHT

variable [hT : Fact (0 < T)]

section fourierCoeff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def fourierCoeff (f : AddCircle T → E) (n : ℤ) : E :=
  ∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle

theorem fourierCoeff_eq_intervalIntegral (f : AddCircle T → E) (n : ℤ) (a : ℝ) :
    fourierCoeff f n = (1 / T) • ∫ x in a..a + T, @fourier T (-n) x • f x := by
  have : ∀ x : ℝ, @fourier T (-n) x • f x = (fun z : AddCircle T => @fourier T (-n) z • f z) x := by
    intro x; rfl
  -- After https://github.com/leanprover/lean4/pull/3124, we need to add `singlePass := true` to avoid an infinite loop.
  simp_rw (config := {singlePass := true}) [this]
  rw [fourierCoeff, AddCircle.intervalIntegral_preimage T a (fun z => _ • _),
    volume_eq_smul_haarAddCircle, integral_smul_measure, ENNReal.toReal_ofReal hT.out.le,
    ← smul_assoc, smul_eq_mul, one_div_mul_cancel hT.out.ne', one_smul]

theorem fourierCoeff.const_smul (f : AddCircle T → E) (c : ℂ) (n : ℤ) :
    fourierCoeff (c • f :) n = c • fourierCoeff f n := by
  simp_rw [fourierCoeff, Pi.smul_apply, ← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul,
    smul_assoc, integral_smul]

theorem fourierCoeff.const_mul (f : AddCircle T → ℂ) (c : ℂ) (n : ℤ) :
    fourierCoeff (fun x => c * f x) n = c * fourierCoeff f n :=
  fourierCoeff.const_smul f c n

def fourierCoeffOn {a b : ℝ} (hab : a < b) (f : ℝ → E) (n : ℤ) : E :=
  haveI := Fact.mk (by linarith : 0 < b - a)
  fourierCoeff (AddCircle.liftIoc (b - a) a f) n

theorem fourierCoeffOn_eq_integral {a b : ℝ} (f : ℝ → E) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab f n =
      (1 / (b - a)) • ∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x := by
  haveI := Fact.mk (by linarith : 0 < b - a)
  rw [fourierCoeffOn, fourierCoeff_eq_intervalIntegral _ _ a, add_sub, add_sub_cancel_left]
  congr 1
  simp_rw [intervalIntegral.integral_of_le hab.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [liftIoc_coe_apply]
  rwa [add_sub, add_sub_cancel_left]

theorem fourierCoeffOn.const_smul {a b : ℝ} (f : ℝ → E) (c : ℂ) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab (c • f) n = c • fourierCoeffOn hab f n := by
  haveI := Fact.mk (by linarith : 0 < b - a)
  apply fourierCoeff.const_smul

theorem fourierCoeffOn.const_mul {a b : ℝ} (f : ℝ → ℂ) (c : ℂ) (n : ℤ) (hab : a < b) :
    fourierCoeffOn hab (fun x => c * f x) n = c * fourierCoeffOn hab f n :=
  fourierCoeffOn.const_smul _ _ _ _

theorem fourierCoeff_liftIoc_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral, add_sub_cancel_left a T]
  · congr 1
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun x hx => ?_)
    rw [liftIoc_coe_apply]
    rwa [uIoc_of_le (lt_add_of_pos_right a hT.out).le] at hx

theorem fourierCoeff_liftIco_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIco T a f) n =
    fourierCoeffOn (lt_add_of_pos_right a hT.out) f n := by
  rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ a, add_sub_cancel_left a T]
  congr 1
  simp_rw [intervalIntegral.integral_of_le (lt_add_of_pos_right a hT.out).le]
  iterate 2 rw [integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [liftIco_coe_apply (Ioo_subset_Ico_self hx)]

end fourierCoeff

section FourierL2

def fourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 <| @haarAddCircle T hT) :=
  HilbertBasis.mk orthonormal_fourier (span_fourierLp_closure_eq_top (by norm_num)).ge

@[simp]
theorem coe_fourierBasis : ⇑(@fourierBasis T hT) = @fourierLp T hT 2 _ :=
  HilbertBasis.coe_mk _ _

theorem fourierBasis_repr (f : Lp ℂ 2 <| @haarAddCircle T hT) (i : ℤ) :
    fourierBasis.repr f i = fourierCoeff f i := by
  trans ∫ t : AddCircle T, conj ((@fourierLp T hT 2 _ i : AddCircle T → ℂ) t) * f t ∂haarAddCircle
  · rw [fourierBasis.repr_apply_apply f i, MeasureTheory.L2.inner_def, coe_fourierBasis]
    simp only [RCLike.inner_apply]
  · apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 i] with _ ht
    rw [ht, ← fourier_neg, smul_eq_mul]

theorem hasSum_fourier_series_L2 (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f := by
  simp_rw [← fourierBasis_repr]; rw [← coe_fourierBasis]
  exact HilbertBasis.hasSum_repr fourierBasis f

theorem tsum_sq_fourierCoeff (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2 = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle := by
  simp_rw [← fourierBasis_repr]
  have H₁ : ‖fourierBasis.repr f‖ ^ 2 = ∑' i, ‖fourierBasis.repr f i‖ ^ 2 := by
    apply_mod_cast lp.norm_rpow_eq_tsum ?_ (fourierBasis.repr f)
    norm_num
  have H₂ : ‖fourierBasis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg RCLike.re (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_inner] at H₃
    rw [← H₁, H₂, H₃]
  · exact L2.integrable_inner f f

end FourierL2

section Convergence

variable (f : C(AddCircle T, ℂ))

theorem fourierCoeff_toLp (n : ℤ) :
    fourierCoeff (toLp (E := ℂ) 2 haarAddCircle ℂ f) n = fourierCoeff f n :=
  integral_congr_ae (Filter.EventuallyEq.mul (Filter.Eventually.of_forall (by tauto))
    (ContinuousMap.coeFn_toAEEqFun haarAddCircle f))

variable {f}

theorem hasSum_fourier_series_of_summable (h : Summable (fourierCoeff f)) :
    HasSum (fun i => fourierCoeff f i • fourier i) f := by
  have sum_L2 := hasSum_fourier_series_L2 (toLp (E := ℂ) 2 haarAddCircle ℂ f)
  simp_rw [fourierCoeff_toLp] at sum_L2
  refine ContinuousMap.hasSum_of_hasSum_Lp (.of_norm ?_) sum_L2
  simp_rw [norm_smul, fourier_norm, mul_one]
  exact h.norm

theorem has_pointwise_sum_fourier_series_of_summable (h : Summable (fourierCoeff f))
    (x : AddCircle T) : HasSum (fun i => fourierCoeff f i • fourier i x) (f x) := by
  convert (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_fourier_series_of_summable h)

end Convergence

end ScopeHT

section deriv

open Complex intervalIntegral

open scoped Interval

variable (T)

theorem hasDerivAt_fourier (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier n (y : AddCircle T))
      (2 * π * I * n / T * fourier n (x : AddCircle T)) x := by
  simp_rw [fourier_coe_apply]
  refine (?_ : HasDerivAt (fun y => exp (2 * π * I * n * y / T)) _ _).comp_ofReal
  rw [(fun α β => by ring : ∀ α β : ℂ, α * exp β = exp β * α)]
  refine (hasDerivAt_exp _).comp (x : ℂ) ?_
  convert hasDerivAt_mul_const (2 * ↑π * I * ↑n / T) using 1
  ext1 y; ring

theorem hasDerivAt_fourier_neg (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier (-n) (y : AddCircle T))
      (-2 * π * I * n / T * fourier (-n) (x : AddCircle T)) x := by
  simpa using hasDerivAt_fourier T (-n) x

variable {T}

-- DISSOLVED: has_antideriv_at_fourier_neg

-- DISSOLVED: fourierCoeffOn_of_hasDeriv_right

-- DISSOLVED: fourierCoeffOn_of_hasDerivAt_Ioo

-- DISSOLVED: fourierCoeffOn_of_hasDerivAt

end deriv
