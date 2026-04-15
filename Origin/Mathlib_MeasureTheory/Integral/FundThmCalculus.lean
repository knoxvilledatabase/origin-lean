/-
Extracted from MeasureTheory/Integral/FundThmCalculus.lean
Genuine: 82 | Conflates: 0 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.VitaliCaratheodory

/-!
# Fundamental Theorem of Calculus

We prove various versions of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for interval integrals in `ℝ`.

Recall that its first version states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`,
and its second version states that, if `f` has an integrable derivative on `[a, b]`, then
`∫ x in a..b, f' x = f b - f a`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `intervalIntegral` namespace. Many of them follow
the naming scheme `integral_has(Strict?)(F?)Deriv(Within?)At(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `Has(Strict?)(F?)Deriv(Within?)At`.
Let us explain the meaning of each part of the name:

* `Strict` means that the theorem is about strict differentiability, see `HasStrictDerivAt` and
  `HasStrictFDerivAt`;
* `F` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `Within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(Within?)`. These theorems are named
`(f?)deriv(Within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `intervalIntegral.integral_hasFDerivWithinAt_of_tendsto_ae` states that
`(u, v) ↦ ∫ x in u..v, f x` has a derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t`
at `(a, b)` provided that `f` tends to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where
possible values of `s`, `t`, and corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |

We use a typeclass `intervalIntegral.FTCFilter` to make Lean automatically find `la`/`lb` based on
`s`/`t`. This way we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial
ones not covered by `integral_hasDerivWithinAt_of_tendsto_ae_(left|right)` and
`integral_hasFDerivAt_of_tendsto_ae`). Similarly, `integral_hasDerivWithinAt_of_tendsto_ae_right`
works for both one-sided derivatives using the same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae`, states the following.
Let `(la, la')` be an `intervalIntegral.FTCFilter` pair of filters around `a` (i.e.,
`intervalIntegral.FTCFilter a la la'`) and let `(lb, lb')` be an `intervalIntegral.FTCFilter` pair
of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at `la'` and `lb'`,
respectively, then
$$
  \int_{va}^{vb} f ∂μ - \int_{ua}^{ub} f ∂μ =
  \int_{ub}^{vb} cb ∂μ - \int_{ua}^{va} ca ∂μ + o(‖∫_{ua}^{va} 1 ∂μ‖ + ‖∫_{ub}^{vb} (1:ℝ) ∂μ‖)
$$
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

### FTC-2 and corollaries

We use FTC-1 to prove several versions of FTC-2 for the Lebesgue measure, using a similar naming
scheme as for the versions of FTC-1. They include:
* `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` - most general version, for functions
  with a right derivative
* `intervalIntegral.integral_eq_sub_of_hasDerivAt` - version for functions with a derivative on
  an open set
* `intervalIntegral.integral_deriv_eq_sub'` - version that is easiest to use when computing the
  integral of a specific function

We then derive additional integration techniques from FTC-2:
* `intervalIntegral.integral_mul_deriv_eq_deriv_mul` - integration by parts
* `intervalIntegral.integral_comp_mul_deriv''` - integration by substitution

Many applications of these theorems can be found in the file
`Mathlib/Analysis/SpecialFunctions/Integrals.lean`.

Note that the assumptions of FTC-2 are formulated in the form that `f'` is integrable. To use it in
a context with the stronger assumption that `f'` is continuous, one can use
`ContinuousOn.intervalIntegrable` or `ContinuousOn.integrableOn_Icc` or
`ContinuousOn.integrableOn_uIcc`.

### `intervalIntegral.FTCFilter` class

As explained above, many theorems in this file rely on the typeclass
`intervalIntegral.FTCFilter (a : ℝ) (l l' : Filter ℝ)` to avoid code duplication. This typeclass
combines four assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has the following “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`,
`(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`.
Furthermore, we have the following instances that are equal to the previously mentioned instances:
`(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`.
While the difference between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure,
it becomes important in the versions of FTC about any locally finite measure if this measure has an
atom at one of the endpoints.

### Combining one-sided and two-sided derivatives

There are some `intervalIntegral.FTCFilter` instances where the fact that it is one-sided or
two-sided depends on the point, namely `(x, 𝓝[Set.Icc a b] x, 𝓝[Set.Icc a b] x)` (resp.
`(x, 𝓝[Set.uIcc a b] x, 𝓝[Set.uIcc a b] x)`, with `x ∈ Icc a b` (resp. `x ∈ uIcc a b`). This results
in a two-sided derivatives for `x ∈ Set.Ioo a b` and one-sided derivatives for `x ∈ {a, b}`. Other
instances could be added when needed (in that case, one also needs to add instances for
`Filter.IsMeasurablyGenerated` and `Filter.TendstoIxxClass`).

## Tags

integral, fundamental theorem of calculus, FTC-1, FTC-2, change of variables in integrals
-/

noncomputable section

open scoped Classical

open MeasureTheory Set Filter Function

open scoped Classical Topology Filter ENNReal Interval NNReal

variable {ι 𝕜 E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace intervalIntegral

section FTC1

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`intervalIntegral.FTCFilter a l l'`. This typeclass has exactly four “real” instances:
`(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`, `(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` can be
seen as a generalization of lemma `integral_hasStrictFDerivAt` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `intervalIntegral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and `lb' ⊓ ae μ`,
respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

class FTCFilter (a : outParam ℝ) (outer : Filter ℝ) (inner : outParam <| Filter ℝ) extends
    TendstoIxxClass Ioc outer inner : Prop where
  pure_le : pure a ≤ outer
  le_nhds : inner ≤ 𝓝 a
  [meas_gen : IsMeasurablyGenerated inner]

namespace FTCFilter

instance pure (a : ℝ) : FTCFilter a (pure a) ⊥ where
  pure_le := le_rfl
  le_nhds := bot_le

instance nhdsWithinSingleton (a : ℝ) : FTCFilter a (𝓝[{a}] a) ⊥ := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]; infer_instance

theorem finiteAt_inner {a : ℝ} (l : Filter ℝ) {l'} [h : FTCFilter a l l'] {μ : Measure ℝ}
    [IsLocallyFiniteMeasure μ] : μ.FiniteAtFilter l' :=
  (μ.finiteAt_nhds a).filter_mono h.le_nhds

instance nhds (a : ℝ) : FTCFilter a (𝓝 a) (𝓝 a) where
  pure_le := pure_le_nhds a
  le_nhds := le_rfl

instance nhdsUniv (a : ℝ) : FTCFilter a (𝓝[univ] a) (𝓝 a) := by rw [nhdsWithin_univ]; infer_instance

instance nhdsLeft (a : ℝ) : FTCFilter a (𝓝[≤] a) (𝓝[≤] a) where
  pure_le := pure_le_nhdsWithin right_mem_Iic
  le_nhds := inf_le_left

instance nhdsRight (a : ℝ) : FTCFilter a (𝓝[≥] a) (𝓝[>] a) where
  pure_le := pure_le_nhdsWithin left_mem_Ici
  le_nhds := inf_le_left

instance nhdsIcc {x a b : ℝ} [h : Fact (x ∈ Icc a b)] :
    FTCFilter x (𝓝[Icc a b] x) (𝓝[Icc a b] x) where
  pure_le := pure_le_nhdsWithin h.out
  le_nhds := inf_le_left

instance nhdsUIcc {x a b : ℝ} [h : Fact (x ∈ [[a, b]])] :
    FTCFilter x (𝓝[[[a, b]]] x) (𝓝[[[a, b]]] x) :=
  .nhdsIcc (h := h)

end FTCFilter

open Asymptotics

section

variable {f : ℝ → E} {a b : ℝ} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι}
  {μ : Measure ℝ} {u v ua va ub vb : ι → ℝ}

theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae' [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  have A := hf.integral_sub_linear_isLittleO_ae hfm hl (hu.Ioc hv)
  have B := hf.integral_sub_linear_isLittleO_ae hfm hl (hv.Ioc hu)
  simp_rw [integral_const', sub_smul]
  refine ((A.trans_le fun t ↦ ?_).sub (B.trans_le fun t ↦ ?_)).congr_left fun t ↦ ?_
  · cases le_total (u t) (v t) <;> simp [*]
  · cases le_total (u t) (v t) <;> simp [*]
  · simp_rw [intervalIntegral]
    abel

theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - (μ (Ioc (u t) (v t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (u t) (v t)).toReal :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf hl hu hv).congr'
    (huv.mono fun x hx => by simp [integral_const', hx])
    (huv.mono fun x hx => by simp [integral_const', hx])

theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + (μ (Ioc (v t) (u t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (v t) (u t)).toReal :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf hl hv hu
          huv).neg_left.congr_left
    fun t => by simp [integral_symm (u t), add_comm]

section

variable [IsLocallyFiniteMeasure μ]

theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf (FTCFilter.finiteAt_inner l) hu hv

theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - (μ (Ioc (u t) (v t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (u t) (v t)).toReal :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + (μ (Ioc (v t) (u t))).toReal • c) =o[lt] fun t =>
      (μ <| Ioc (v t) (u t)).toReal :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

end

variable [FTCFilter a la la'] [FTCFilter b lb lb'] [IsLocallyFiniteMeasure μ]

theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f la' μ)
    (hmeas_b : StronglyMeasurableAtFilter f lb' μ) (ha_lim : Tendsto f (la' ⊓ ae μ) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae μ) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x ∂μ) - ∫ x in ua t..ub t, f x ∂μ) -
          ((∫ _ in ub t..vb t, cb ∂μ) - ∫ _ in ua t..va t, ca ∂μ)) =o[lt]
      fun t => ‖∫ _ in ua t..va t, (1 : ℝ) ∂μ‖ + ‖∫ _ in ub t..vb t, (1 : ℝ) ∂μ‖ := by
  haveI := FTCFilter.meas_gen la; haveI := FTCFilter.meas_gen lb
  refine
    ((measure_integral_sub_linear_isLittleO_of_tendsto_ae hmeas_a ha_lim hua hva).neg_left.add_add
          (measure_integral_sub_linear_isLittleO_of_tendsto_ae hmeas_b hb_lim hub hvb)).congr'
      ?_ EventuallyEq.rfl
  have A : ∀ᶠ t in lt, IntervalIntegrable f μ (ua t) (va t) :=
    ha_lim.eventually_intervalIntegrable_ae hmeas_a (FTCFilter.finiteAt_inner la) hua hva
  have A' : ∀ᶠ t in lt, IntervalIntegrable f μ a (ua t) :=
    ha_lim.eventually_intervalIntegrable_ae hmeas_a (FTCFilter.finiteAt_inner la)
      (tendsto_const_pure.mono_right FTCFilter.pure_le) hua
  have B : ∀ᶠ t in lt, IntervalIntegrable f μ (ub t) (vb t) :=
    hb_lim.eventually_intervalIntegrable_ae hmeas_b (FTCFilter.finiteAt_inner lb) hub hvb
  have B' : ∀ᶠ t in lt, IntervalIntegrable f μ b (ub t) :=
    hb_lim.eventually_intervalIntegrable_ae hmeas_b (FTCFilter.finiteAt_inner lb)
      (tendsto_const_pure.mono_right FTCFilter.pure_le) hub
  filter_upwards [A, A', B, B'] with _ ua_va a_ua ub_vb b_ub
  rw [← integral_interval_sub_interval_comm']
  · abel
  exacts [ub_vb, ua_va, b_ub.symm.trans <| hab.symm.trans a_ua]

theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f lb' μ)
    (hf : Tendsto f (lb' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x ∂μ) - ∫ x in a..u t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  simpa using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab stronglyMeasurableAt_bot
      hmeas ((tendsto_bot : Tendsto _ ⊥ (𝓝 (0 : E))).mono_left inf_le_left) hf
      (tendsto_const_pure : Tendsto _ _ (pure a)) tendsto_const_pure hu hv

theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f la' μ)
    (hf : Tendsto f (la' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x ∂μ) - ∫ x in u t..b, f x ∂μ) + ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  simpa using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab hmeas
      stronglyMeasurableAt_bot hf ((tendsto_bot : Tendsto _ ⊥ (𝓝 (0 : E))).mono_left inf_le_left) hu
      hv (tendsto_const_pure : Tendsto _ _ (pure b)) tendsto_const_pure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/

variable [CompleteSpace E]
  {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι} {a b : ℝ}
  {u v ua ub va vb : ι → ℝ} [FTCFilter a la la'] [FTCFilter b lb lb']

/-!
#### Auxiliary `Asymptotics.IsLittleO` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use
`Asymptotics.isLittleO` because we have no definition of `HasStrict(F)DerivAtFilter` in the library.
-/

theorem integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l') (hf : Tendsto f (l' ⊓ ae volume) (𝓝 c)) {u v : ι → ℝ}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x) - (v t - u t) • c) =o[lt] (v - u) := by
  simpa [integral_const] using measure_integral_sub_linear_isLittleO_of_tendsto_ae hfm hf hu hv

theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la')
    (hmeas_b : StronglyMeasurableAtFilter f lb') (ha_lim : Tendsto f (la' ⊓ ae volume) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae volume) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x) - ∫ x in ua t..ub t, f x) -
          ((vb t - ub t) • cb - (va t - ua t) • ca)) =o[lt]
      fun t => ‖va t - ua t‖ + ‖vb t - ub t‖ := by
  simpa [integral_const]
    using measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab hmeas_a hmeas_b
      ha_lim hb_lim hua hva hub hvb

theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f lb')
    (hf : Tendsto f (lb' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x) - ∫ x in a..u t, f x) - (v t - u t) • c) =o[lt] (v - u) := by
  simpa only [integral_const, smul_eq_mul, mul_one] using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hab hmeas hf hu hv

theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f la')
    (hf : Tendsto f (la' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x) - ∫ x in u t..b, f x) + (v t - u t) • c) =o[lt] (v - u) := by
  simpa only [integral_const, smul_eq_mul, mul_one] using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left hab hmeas hf hu hv

open ContinuousLinearMap (fst snd smulRight sub_apply smulRight_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_hasStrictFDerivAt_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tendsto to `a` and `b`,
  respectively;

* `integral_hasStrictFDerivAt`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_hasStrictDerivAt_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_hasStrictDerivAt_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/

theorem integral_hasStrictFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) := by
  have :=
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      (continuous_snd.fst.tendsto ((a, b), (a, b)))
      (continuous_fst.fst.tendsto ((a, b), (a, b)))
      (continuous_snd.snd.tendsto ((a, b), (a, b)))
      (continuous_fst.snd.tendsto ((a, b), (a, b)))
  refine .of_isLittleO <| (this.congr_left ?_).trans_isBigO ?_
  · intro x; simp [sub_smul]
  · exact isBigO_fst_prod.norm_left.add isBigO_snd_prod.norm_left

theorem integral_hasStrictFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

theorem integral_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b :=
  .of_isLittleO <|
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb continuousAt_snd
      continuousAt_fst

theorem integral_hasStrictDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

theorem integral_hasStrictDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-c) a := by
  simpa only [← integral_symm] using
    (integral_hasStrictDerivAt_of_tendsto_ae_right hf.symm hmeas ha).neg

theorem integral_hasStrictDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-f a) a := by
  simpa only [← integral_symm] using (integral_hasStrictDerivAt_right hf.symm hmeas ha).neg

theorem _root_.Continuous.integral_hasStrictDerivAt {f : ℝ → E} (hf : Continuous f) (a b : ℝ) :
    HasStrictDerivAt (fun u => ∫ x : ℝ in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
    hf.continuousAt

theorem _root_.Continuous.deriv_integral (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u => ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `HasFDerivAt`,
`HasDerivAt`, `fderiv`, and `deriv`.
-/

theorem integral_hasFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) :=
  (integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).hasFDerivAt

theorem integral_hasFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  (integral_hasStrictFDerivAt hf hmeas_a hmeas_b ha hb).hasFDerivAt

theorem fderiv_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv

theorem fderiv_integral (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a) :=
  (integral_hasFDerivAt hf hmeas_a hmeas_b ha hb).fderiv

theorem integral_hasDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in a..u, f x) c b :=
  (integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas hb).hasDerivAt

theorem integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  (integral_hasStrictDerivAt_right hf hmeas hb).hasDerivAt

theorem deriv_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in a..u, f x) b = c :=
  (integral_hasDerivAt_of_tendsto_ae_right hf hmeas hb).deriv

theorem deriv_integral_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    deriv (fun u => ∫ x in a..u, f x) b = f b :=
  (integral_hasDerivAt_right hf hmeas hb).deriv

theorem integral_hasDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-c) a :=
  (integral_hasStrictDerivAt_of_tendsto_ae_left hf hmeas ha).hasDerivAt

theorem integral_hasDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-f a) a :=
  (integral_hasStrictDerivAt_left hf hmeas ha).hasDerivAt

theorem deriv_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in u..b, f x) a = -c :=
  (integral_hasDerivAt_of_tendsto_ae_left hf hmeas hb).deriv

theorem deriv_integral_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : ContinuousAt f a) :
    deriv (fun u => ∫ x in u..b, f x) a = -f a :=
  (integral_hasDerivAt_left hf hmeas hb).deriv

/-!
#### One-sided derivatives
-/

theorem integral_hasFDerivWithinAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (s ×ˢ t) (a, b) := by
  rw [HasFDerivWithinAt, nhdsWithin_prod_eq]
  have :=
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      (tendsto_const_pure.mono_right FTCFilter.pure_le : Tendsto _ _ (𝓝[s] a)) tendsto_fst
      (tendsto_const_pure.mono_right FTCFilter.pure_le : Tendsto _ _ (𝓝[t] b)) tendsto_snd
  refine .of_isLittleO <| (this.congr_left ?_).trans_isBigO ?_
  · intro x; simp [sub_smul]
  · exact isBigO_fst_prod.norm_left.add isBigO_snd_prod.norm_left

theorem integral_hasFDerivWithinAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (ha : Tendsto f la (𝓝 <| f a))
    (hb : Tendsto f lb (𝓝 <| f b)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (s ×ˢ t) (a, b) :=
  integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

macro "uniqueDiffWithinAt_Ici_Iic_univ" : tactic =>

  `(tactic| (first | exact uniqueDiffOn_Ici _ _ left_mem_Ici |

    exact uniqueDiffOn_Iic _ _ right_mem_Iic | exact uniqueDiffWithinAt_univ (𝕜 := ℝ) (E := ℝ)))

theorem fderivWithin_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ)
    (ht : UniqueDiffWithinAt ℝ t b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    fderivWithin ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (s ×ˢ t) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderivWithin <| hs.prod ht

theorem integral_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in a..u, f x) c s b :=
  .of_isLittleO <| integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb
    (tendsto_const_pure.mono_right FTCFilter.pure_le) tendsto_id

theorem integral_hasDerivWithinAt_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b) : HasDerivWithinAt (fun u => ∫ x in a..u, f x) (f b) s b :=
  integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

theorem derivWithin_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas hb).derivWithin hs

theorem derivWithin_integral_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b)
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = f b :=
  (integral_hasDerivWithinAt_right hf hmeas hb).derivWithin hs

theorem integral_hasDerivWithinAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-c) s a := by
  simp only [integral_symm b]
  exact (integral_hasDerivWithinAt_of_tendsto_ae_right hf.symm hmeas ha).neg

theorem integral_hasDerivWithinAt_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a) : HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-f a) s a :=
  integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas (ha.mono_left inf_le_left)

theorem derivWithin_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas ha).derivWithin hs

theorem derivWithin_integral_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a)
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -f a :=
  (integral_hasDerivWithinAt_left hf hmeas ha).derivWithin hs

theorem differentiableOn_integral_of_continuous {s : Set ℝ}
    (hintg : ∀ x ∈ s, IntervalIntegrable f volume a x) (hcont : Continuous f) :
    DifferentiableOn ℝ (fun u => ∫ x in a..u, f x) s := fun y hy =>
  (integral_hasDerivAt_right (hintg y hy) hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
        hcont.continuousAt).differentiableAt.differentiableWithinAt

end FTC1

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals, i.e., the assertion
that `∫ x in a..b, f' x = f b - f a` under suitable assumptions.

The most classical version of this theorem assumes that `f'` is continuous. However, this is
unnecessarily strong: the result holds if `f'` is just integrable. We prove the strong version,
following [Rudin, *Real and Complex Analysis* (Theorem 7.21)][rudin2006real]. The proof is first
given for real-valued functions, and then deduced for functions with a general target space. For
a real-valued function `g`, it suffices to show that `g b - g a ≤ (∫ x in a..b, g' x) + ε` for all
positive `ε`. To prove this, choose a lower-semicontinuous function `G'` with `g' < G'` and with
integral close to that of `g'` (its existence is guaranteed by the Vitali-Carathéodory theorem).
It satisfies `g t - g a ≤ ∫ x in a..t, G' x` for all `t ∈ [a, b]`: this inequality holds at `a`,
and if it holds at `t` then it holds for `u` close to `t` on its right, as the left hand side
increases by `g u - g t ∼ (u -t) g' t`, while the right hand side increases by
`∫ x in t..u, G' x` which is roughly at least `∫ x in t..u, G' t = (u - t) G' t`, by lower
semicontinuity. As  `g' t < G' t`, this gives the conclusion. One can therefore push progressively
this inequality to the right until the point `b`, where it gives the desired conclusion.
-/

variable {g' g φ : ℝ → ℝ} {a b : ℝ}

theorem sub_le_integral_of_hasDeriv_right_of_le_Ico (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (φint : IntegrableOn φ (Icc a b)) (hφg : ∀ x ∈ Ico a b, g' x ≤ φ x) :
    g b - g a ≤ ∫ y in a..b, φ y := by
  refine le_of_forall_pos_le_add fun ε εpos => ?_
  -- Bound from above `g'` by a lower-semicontinuous function `G'`.
  rcases exists_lt_lowerSemicontinuous_integral_lt φ φint εpos with
    ⟨G', f_lt_G', G'cont, G'int, G'lt_top, hG'⟩
  -- we will show by "induction" that `g t - g a ≤ ∫ u in a..t, G' u` for all `t ∈ [a, b]`.
  set s := {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} ∩ Icc a b
  -- the set `s` of points where this property holds is closed.
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g t - g a, ∫ u in a..t, (G' u).toReal)) (Icc a b) := by
      rw [← uIcc_of_le hab] at G'int hcont ⊢
      exact (hcont.sub continuousOn_const).prod (continuousOn_primitive_interval G'int)
    simp only [s, inter_comm]
    exact this.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  have main : Icc a b ⊆ {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} := by
    -- to show that the set `s` is all `[a, b]`, it suffices to show that any point `t` in `s`
    -- with `t < b` admits another point in `s` slightly to its right
    -- (this is a sort of real induction).
    refine s_closed.Icc_subset_of_forall_exists_gt
      (by simp only [integral_same, mem_setOf_eq, sub_self, le_rfl]) fun t ht v t_lt_v => ?_
    obtain ⟨y, g'_lt_y', y_lt_G'⟩ : ∃ y : ℝ, (g' t : EReal) < y ∧ (y : EReal) < G' t :=
      EReal.lt_iff_exists_real_btwn.1 ((EReal.coe_le_coe_iff.2 (hφg t ht.2)).trans_lt (f_lt_G' t))
    -- bound from below the increase of `∫ x in a..u, G' x` on the right of `t`, using the lower
    -- semicontinuity of `G'`.
    have I1 : ∀ᶠ u in 𝓝[>] t, (u - t) * y ≤ ∫ w in t..u, (G' w).toReal := by
      have B : ∀ᶠ u in 𝓝 t, (y : EReal) < G' u := G'cont.lowerSemicontinuousAt _ _ y_lt_G'
      rcases mem_nhds_iff_exists_Ioo_subset.1 B with ⟨m, M, ⟨hm, hM⟩, H⟩
      have : Ioo t (min M b) ∈ 𝓝[>] t := Ioo_mem_nhdsWithin_Ioi' (lt_min hM ht.right.right)
      filter_upwards [this] with u hu
      have I : Icc t u ⊆ Icc a b := Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_right _ _))
      calc
        (u - t) * y = ∫ _ in Icc t u, y := by
          simp only [hu.left.le, MeasureTheory.integral_const, Algebra.id.smul_eq_mul, sub_nonneg,
            MeasurableSet.univ, Real.volume_Icc, Measure.restrict_apply, univ_inter,
            ENNReal.toReal_ofReal]
        _ ≤ ∫ w in t..u, (G' w).toReal := by
          rw [intervalIntegral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc]
          apply setIntegral_mono_ae_restrict
          · simp only [integrableOn_const, Real.volume_Icc, ENNReal.ofReal_lt_top, or_true]
          · exact IntegrableOn.mono_set G'int I
          · have C1 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), G' x < ∞ :=
              ae_mono (Measure.restrict_mono I le_rfl) G'lt_top
            have C2 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), x ∈ Icc t u :=
              ae_restrict_mem measurableSet_Icc
            filter_upwards [C1, C2] with x G'x hx
            apply EReal.coe_le_coe_iff.1
            have : x ∈ Ioo m M := by
              simp only [hm.trans_le hx.left,
                (hx.right.trans_lt hu.right).trans_le (min_le_left M b), mem_Ioo, and_self_iff]
            refine (H this).out.le.trans_eq ?_
            exact (EReal.coe_toReal G'x.ne (f_lt_G' x).ne_bot).symm
    -- bound from above the increase of `g u - g a` on the right of `t`, using the derivative at `t`
    have I2 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ (u - t) * y := by
      have g'_lt_y : g' t < y := EReal.coe_lt_coe_iff.1 g'_lt_y'
      filter_upwards [(hderiv t ⟨ht.2.1, ht.2.2⟩).limsup_slope_le' (not_mem_Ioi.2 le_rfl) g'_lt_y,
        self_mem_nhdsWithin] with u hu t_lt_u
      have := mul_le_mul_of_nonneg_left hu.le (sub_pos.2 t_lt_u.out).le
      rwa [← smul_eq_mul, sub_smul_slope] at this
    -- combine the previous two bounds to show that `g u - g a` increases less quickly than
    -- `∫ x in a..u, G' x`.
    have I3 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ ∫ w in t..u, (G' w).toReal := by
      filter_upwards [I1, I2] with u hu1 hu2 using hu2.trans hu1
    have I4 : ∀ᶠ u in 𝓝[>] t, u ∈ Ioc t (min v b) := by
      refine mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.2 ⟨min v b, ?_, Subset.rfl⟩
      simp only [lt_min_iff, mem_Ioi]
      exact ⟨t_lt_v, ht.2.2⟩
    -- choose a point `x` slightly to the right of `t` which satisfies the above bound
    rcases (I3.and I4).exists with ⟨x, hx, h'x⟩
    -- we check that it belongs to `s`, essentially by construction
    refine ⟨x, ?_, Ioc_subset_Ioc le_rfl (min_le_left _ _) h'x⟩
    calc
      g x - g a = g t - g a + (g x - g t) := by abel
      _ ≤ (∫ w in a..t, (G' w).toReal) + ∫ w in t..x, (G' w).toReal := add_le_add ht.1 hx
      _ = ∫ w in a..x, (G' w).toReal := by
        apply integral_add_adjacent_intervals
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2.1]
          exact IntegrableOn.mono_set G'int
            (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le))
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x.1.le]
          apply IntegrableOn.mono_set G'int
          exact Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.2.1 (h'x.2.trans (min_le_right _ _)))
  -- now that we know that `s` contains `[a, b]`, we get the desired result by applying this to `b`.
  calc
    g b - g a ≤ ∫ y in a..b, (G' y).toReal := main (right_mem_Icc.2 hab)
    _ ≤ (∫ y in a..b, φ y) + ε := by
      convert hG'.le <;>
        · rw [intervalIntegral.integral_of_le hab]
          simp only [integral_Icc_eq_integral_Ioc', Real.volume_singleton]

theorem sub_le_integral_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, g' x ≤ φ x) : g b - g a ≤ ∫ y in a..b, φ y := by
  -- This follows from the version on a closed-open interval (applied to `[t, b)` for `t` close to
  -- `a`) and a continuity argument.
  obtain rfl | a_lt_b := hab.eq_or_lt
  · simp
  set s := {t | g b - g t ≤ ∫ u in t..b, φ u} ∩ Icc a b
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g b - g t, ∫ u in t..b, φ u)) (Icc a b) := by
      rw [← uIcc_of_le hab] at hcont φint ⊢
      exact (continuousOn_const.sub hcont).prod (continuousOn_primitive_interval_left φint)
    simp only [s, inter_comm]
    exact this.preimage_isClosed_of_isClosed isClosed_Icc isClosed_le_prod
  have A : closure (Ioc a b) ⊆ s := by
    apply s_closed.closure_subset_iff.2
    intro t ht
    refine ⟨?_, ⟨ht.1.le, ht.2⟩⟩
    exact
      sub_le_integral_of_hasDeriv_right_of_le_Ico ht.2 (hcont.mono (Icc_subset_Icc ht.1.le le_rfl))
        (fun x hx => hderiv x ⟨ht.1.trans_le hx.1, hx.2⟩)
        (φint.mono_set (Icc_subset_Icc ht.1.le le_rfl)) fun x hx => hφg x ⟨ht.1.trans_le hx.1, hx.2⟩
  rw [closure_Ioc a_lt_b.ne] at A
  exact (A (left_mem_Icc.2 hab)).1

theorem integral_le_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, φ x ≤ g' x) : (∫ y in a..b, φ y) ≤ g b - g a := by
  rw [← neg_le_neg_iff]
  convert sub_le_integral_of_hasDeriv_right_of_le hab hcont.neg (fun x hx => (hderiv x hx).neg)
    φint.neg fun x hx => neg_le_neg (hφg x hx) using 1
  · abel
  · simp only [← integral_neg]; rfl

theorem integral_eq_sub_of_hasDeriv_right_of_le_real (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'int : IntegrableOn g' (Icc a b)) : ∫ y in a..b, g' y = g b - g a :=
  le_antisymm (integral_le_sub_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)
    (sub_le_integral_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)

variable [CompleteSpace E] {f f' : ℝ → E}

theorem integral_eq_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (f'int : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by
  refine (NormedSpace.eq_iff_forall_dual_eq ℝ).2 fun g => ?_
  rw [← g.intervalIntegral_comp_comm f'int, g.map_sub]
  exact integral_eq_sub_of_hasDeriv_right_of_le_real hab (g.continuous.comp_continuousOn hcont)
    (fun x hx => g.hasFDerivAt.comp_hasDerivWithinAt x (hderiv x hx))
    (g.integrable_comp ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 f'int))

theorem integral_eq_sub_of_hasDeriv_right (hcont : ContinuousOn f (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, min_eq_left, max_eq_right, hab] at hcont hderiv hint
    apply integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  · simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab] at hcont hderiv
    rw [integral_symm, integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint.symm, neg_sub]

theorem integral_eq_sub_of_hasDerivAt_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right_of_le hab hcont (fun x hx => (hderiv x hx).hasDerivWithinAt)
    hint

theorem integral_eq_sub_of_hasDerivAt (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right (HasDerivAt.continuousOn hderiv)
    (fun _x hx => (hderiv _ (mem_Icc_of_Ioo hx)).hasDerivWithinAt) hint

theorem integral_eq_sub_of_hasDerivAt_of_tendsto (hab : a < b) {fa fb}
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    ∫ y in a..b, f' y = fb - fa := by
  set F : ℝ → E := update (update f a fa) b fb
  have Fderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f' x) x := by
    refine fun x hx => (hderiv x hx).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy
    unfold F
    rw [update_noteq hy.2.ne, update_noteq hy.1.ne']
  have hcont : ContinuousOn F (Icc a b) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_diff_right, Ico_diff_left]
    refine ⟨⟨fun z hz => (hderiv z hz).continuousAt.continuousWithinAt, ?_⟩, ?_⟩
    · exact fun _ => ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · rintro -
      refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsWithin_Iio (right_mem_Ioc.2 hab)] with _ hz using
        (update_noteq hz.1.ne' _ _).symm
  simpa [F, hab.ne, hab.ne'] using integral_eq_sub_of_hasDerivAt_of_le hab.le hcont Fderiv hint

theorem integral_deriv_eq_sub (hderiv : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => (hderiv x hx).hasDerivAt) hint

theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f')
    (hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x) (hcont : ContinuousOn f' (uIcc a b)) :
    ∫ y in a..b, f' y = f b - f a := by
  rw [← hderiv, integral_deriv_eq_sub hdiff]
  rw [hderiv]
  exact hcont.intervalIntegrable

lemma integral_unitInterval_deriv_eq_sub [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    {f f' : 𝕜 → E} {z₀ z₁ : 𝕜}
    (hcont : ContinuousOn (fun t : ℝ ↦ f' (z₀ + t • z₁)) (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (z₀ + t • z₁)) (z₀ + t • z₁)) :
    z₁ • ∫ t in (0 : ℝ)..1, f' (z₀ + t • z₁) = f (z₀ + z₁) - f z₀ := by
  let γ (t : ℝ) : 𝕜 := z₀ + t • z₁
  have hint : IntervalIntegrable (z₁ • (f' ∘ γ)) MeasureTheory.volume 0 1 :=
    (ContinuousOn.const_smul hcont z₁).intervalIntegrable_of_Icc zero_le_one
  have hderiv' : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (f ∘ γ) (z₁ • (f' ∘ γ) t) t := by
    intro t ht
    refine (hderiv t <| (Set.uIcc_of_le (α := ℝ) zero_le_one).symm ▸ ht).scomp t ?_
    have : HasDerivAt (fun t : ℝ ↦ t • z₁) z₁ t := by
      convert (hasDerivAt_id t).smul_const (F := 𝕜) _ using 1
      simp only [one_smul]
    exact this.const_add z₀
  convert (integral_eq_sub_of_hasDerivAt hderiv' hint) using 1
  · simp_rw [← integral_smul, Function.comp_apply]
  · simp only [γ, Function.comp_apply, one_smul, zero_smul, add_zero]

/-!
### Automatic integrability for nonnegative derivatives
-/

theorem integrableOn_deriv_right_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) : IntegrableOn g' (Ioc a b) := by
  by_cases hab : a < b; swap
  · simp [Ioc_eq_empty hab]
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have meas_g' : AEMeasurable g' (volume.restrict (Ioo a b)) := by
    apply (aemeasurable_derivWithin_Ioi g _).congr
    refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_
    exact (hderiv x hx).derivWithin (uniqueDiffWithinAt_Ioi _)
  suffices H : (∫⁻ x in Ioo a b, ‖g' x‖₊) ≤ ENNReal.ofReal (g b - g a) from
    ⟨meas_g'.aestronglyMeasurable, H.trans_lt ENNReal.ofReal_lt_top⟩
  by_contra! H
  obtain ⟨f, fle, fint, hf⟩ :
    ∃ f : SimpleFunc ℝ ℝ≥0,
      (∀ x, f x ≤ ‖g' x‖₊) ∧
        (∫⁻ x : ℝ in Ioo a b, f x) < ∞ ∧ ENNReal.ofReal (g b - g a) < ∫⁻ x : ℝ in Ioo a b, f x :=
    exists_lt_lintegral_simpleFunc_of_lt_lintegral H
  let F : ℝ → ℝ := (↑) ∘ f
  have intF : IntegrableOn F (Ioo a b) := by
    refine ⟨f.measurable.coe_nnreal_real.aestronglyMeasurable, ?_⟩
    simpa only [F, HasFiniteIntegral, comp_apply, NNReal.nnnorm_eq] using fint
  have A : ∫⁻ x : ℝ in Ioo a b, f x = ENNReal.ofReal (∫ x in Ioo a b, F x) :=
    lintegral_coe_eq_integral _ intF
  rw [A] at hf
  have B : (∫ x : ℝ in Ioo a b, F x) ≤ g b - g a := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    refine integral_le_sub_of_hasDeriv_right_of_le hab.le hcont hderiv ?_ fun x hx => ?_
    · rwa [integrableOn_Icc_iff_integrableOn_Ioo]
    · convert NNReal.coe_le_coe.2 (fle x)
      simp only [Real.norm_of_nonneg (g'pos x hx), coe_nnnorm]
  exact lt_irrefl _ (hf.trans_le (ENNReal.ofReal_le_ofReal B))

theorem integrableOn_deriv_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) :
    IntegrableOn g' (Ioc a b) :=
  integrableOn_deriv_right_of_nonneg hcont (fun x hx => (hderiv x hx).hasDerivWithinAt) g'pos

theorem intervalIntegrable_deriv_of_nonneg (hcont : ContinuousOn g (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt g (g' x) x)
    (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ g' x) : IntervalIntegrable g' volume a b := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, min_eq_left, max_eq_right, hab, IntervalIntegrable, hab,
      Ioc_eq_empty_of_le, integrableOn_empty, and_true] at hcont hderiv hpos ⊢
    exact integrableOn_deriv_of_nonneg hcont hderiv hpos
  · simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab, IntervalIntegrable, Ioc_eq_empty_of_le,
      integrableOn_empty, true_and] at hcont hderiv hpos ⊢
    exact integrableOn_deriv_of_nonneg hcont hderiv hpos

/-!
### Integration by parts
-/

section Parts

variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem integral_deriv_mul_eq_sub_of_hasDeriv_right {u v u' v' : ℝ → A}
    (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a := by
  apply integral_eq_sub_of_hasDeriv_right (hu.mul hv) fun x hx ↦ (huu' x hx).mul (hvv' x hx)
  exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)

theorem integral_deriv_mul_eq_sub_of_hasDerivAt {u v u' v' : ℝ → A}
    (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv
    (fun x hx ↦ huu' x hx |>.hasDerivWithinAt) (fun x hx ↦ hvv' x hx |>.hasDerivWithinAt) hu' hv'

theorem integral_deriv_mul_eq_sub_of_hasDerivWithinAt {u v u' v' : ℝ → A}
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

theorem integral_deriv_mul_eq_sub {u v u' v' : ℝ → A}
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (fun x hx ↦ hu x hx |>.hasDerivWithinAt) (fun x hx ↦ hv x hx |>.hasDerivWithinAt) hu' hv'

theorem integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right {u v u' v' : ℝ → A}
    (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  rw [← integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv', ← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)
  · exact hu'.mul_continuousOn hv

theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivAt {u v u' v' : ℝ → A}
    (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv
        (fun x hx ↦ (huu' x hx).hasDerivWithinAt) (fun x hx ↦ (hvv' x hx).hasDerivWithinAt) hu' hv'

theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt {u v u' v' : ℝ → A}
    (hu : ∀ x ∈ [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : ∀ x ∈ [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (fun x hx ↦ (hu x hx).continuousWithinAt)
    (fun x hx ↦ (hv x hx).continuousWithinAt)
    (fun x hx ↦ hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx ↦ hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

theorem integral_mul_deriv_eq_deriv_mul {u v u' v' : ℝ → A}
    (hu : ∀ x ∈ [[a, b]], HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (fun x hx ↦ (hu x hx).hasDerivWithinAt) (fun x hx ↦ (hv x hx).hasDerivWithinAt) hu' hv'

end Parts

/-!
### Integration by substitution / Change of variables
-/

section SMul

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem integral_comp_smul_deriv''' {f f' : ℝ → ℝ} {g : ℝ → G} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x => f' x • (g ∘ f) x) [[a, b]]) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  by_cases hG : CompleteSpace G; swap
  · simp [intervalIntegral, integral, hG]
  rw [hf.image_uIcc, ← intervalIntegrable_iff'] at hg1
  have h_cont : ContinuousOn (fun u => ∫ t in f a..f u, g t) [[a, b]] := by
    refine (continuousOn_primitive_interval' hg1 ?_).comp hf ?_
    · rw [← hf.image_uIcc]; exact mem_image_of_mem f left_mem_uIcc
    · rw [← hf.image_uIcc]; exact mapsTo_image _ _
  have h_der :
    ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt (fun u => ∫ t in f a..f u, g t) (f' x • (g ∘ f) x) (Ioi x) x := by
    intro x hx
    obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hx.1
    obtain ⟨d, hd⟩ := nonempty_Ioo.mpr hx.2
    have cdsub : [[c, d]] ⊆ Ioo (min a b) (max a b) := by
      rw [uIcc_of_le (hc.2.trans hd.1).le]
      exact Icc_subset_Ioo hc.1 hd.2
    replace hg_cont := hg_cont.mono (image_subset f cdsub)
    let J := [[sInf (f '' [[c, d]]), sSup (f '' [[c, d]])]]
    have hJ : f '' [[c, d]] = J := (hf.mono (cdsub.trans Ioo_subset_Icc_self)).image_uIcc
    rw [hJ] at hg_cont
    have h2x : f x ∈ J := by rw [← hJ]; exact mem_image_of_mem _ (mem_uIcc_of_le hc.2.le hd.1.le)
    have h2g : IntervalIntegrable g volume (f a) (f x) := by
      refine hg1.mono_set ?_
      rw [← hf.image_uIcc]
      exact hf.surjOn_uIcc left_mem_uIcc (Ioo_subset_Icc_self hx)
    have h3g : StronglyMeasurableAtFilter g (𝓝[J] f x) :=
      hg_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc (f x)
    haveI : Fact (f x ∈ J) := ⟨h2x⟩
    have : HasDerivWithinAt (fun u => ∫ x in f a..u, g x) (g (f x)) J (f x) :=
      intervalIntegral.integral_hasDerivWithinAt_right h2g h3g (hg_cont (f x) h2x)
    refine (this.scomp x ((hff' x hx).Ioo_of_Ioi hd.1) ?_).Ioi_of_Ioo hd.1
    rw [← hJ]
    refine (mapsTo_image _ _).mono ?_ Subset.rfl
    exact Ioo_subset_Icc_self.trans ((Icc_subset_Icc_left hc.2.le).trans Icc_subset_uIcc)
  rw [← intervalIntegrable_iff'] at hg2
  simp_rw [integral_eq_sub_of_hasDeriv_right h_cont h_der hg2, integral_same, sub_zero]

theorem integral_comp_smul_deriv'' {f f' : ℝ → ℝ} {g : ℝ → G} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  refine
    integral_comp_smul_deriv''' hf hff' (hg.mono <| image_subset _ Ioo_subset_Icc_self) ?_
      (hf'.smul (hg.comp hf <| subset_preimage_image f _)).integrableOn_Icc
  rw [hf.image_uIcc] at hg ⊢
  exact hg.integrableOn_Icc

theorem integral_comp_smul_deriv' {f f' : ℝ → ℝ} {g : ℝ → G}
    (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (h' : ContinuousOn f' (uIcc a b))
    (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_comp_smul_deriv'' (fun x hx => (h x hx).continuousAt.continuousWithinAt)
    (fun x hx => (h x <| Ioo_subset_Icc_self hx).hasDerivWithinAt) h' hg

theorem integral_comp_smul_deriv {f f' : ℝ → ℝ} {g : ℝ → G}
    (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (h' : ContinuousOn f' (uIcc a b))
    (hg : Continuous g) : (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_comp_smul_deriv' h h' hg.continuousOn

theorem integral_deriv_comp_smul_deriv' {f f' : ℝ → ℝ} {g g' : ℝ → E} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a := by
  rw [integral_comp_smul_deriv'' hf hff' hf' hg',
    integral_eq_sub_of_hasDeriv_right hg hgg' (hg'.mono _).intervalIntegrable]
  exacts [rfl, intermediate_value_uIcc hf]

theorem integral_deriv_comp_smul_deriv {f f' : ℝ → ℝ} {g g' : ℝ → E}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => (hg x hx).scomp x <| hf x hx)
    (hf'.smul (hg'.comp_continuousOn <| HasDerivAt.continuousOn hf)).intervalIntegrable

end SMul

section Mul

theorem integral_comp_mul_deriv''' {a b : ℝ} {f f' : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) [[a, b]]) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) [[a, b]] := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_comp_smul_deriv''' hf hff' hg_cont hg1 hg2'

theorem integral_comp_mul_deriv'' {f f' g : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using integral_comp_smul_deriv'' hf hff' hf' hg

theorem integral_comp_mul_deriv' {f f' g : ℝ → ℝ} (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x := by
  simpa [mul_comm] using integral_comp_smul_deriv' h h' hg

theorem integral_comp_mul_deriv {f f' g : ℝ → ℝ} (h : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x :=
  integral_comp_mul_deriv' h h' hg.continuousOn

theorem integral_deriv_comp_mul_deriv' {f f' g g' : ℝ → ℝ} (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_comp_smul_deriv' hf hff' hf' hg hgg' hg'

theorem integral_deriv_comp_mul_deriv {f f' g g' : ℝ → ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_comp_smul_deriv hf hg hf' hg'

end Mul

end intervalIntegral

set_option linter.style.longFile 1700
