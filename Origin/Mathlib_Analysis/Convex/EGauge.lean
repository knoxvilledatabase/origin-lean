/-
Extracted from Analysis/Convex/EGauge.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Minkowski functional, normed field version

In this file we define `(egauge 𝕜 s ·)`
to be the Minkowski functional (gauge) of the set `s`
in a topological vector space `E` over a normed field `𝕜`,
as a function `E → ℝ≥0∞`.

It is defined as the infimum of the norms of `c : 𝕜` such that `x ∈ c • s`.
In particular, for `𝕜 = ℝ≥0` this definition gives an `ℝ≥0∞`-valued version of `gauge`
defined in `Mathlib/Analysis/Convex/Gauge.lean`.

This definition can be used to generalize the notion of Fréchet derivative
to maps between topological vector spaces without norms.

Currently, we can't reuse results about `egauge` for `gauge`,
because we lack a theory of normed semifields.
-/

open Function Set Filter Metric

open scoped Topology Pointwise ENNReal NNReal

section SMul

noncomputable def egauge (𝕜 : Type*) [ENorm 𝕜] {E : Type*} [SMul 𝕜 E] (s : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ (c : 𝕜) (_ : x ∈ c • s), ‖c‖ₑ

variable (𝕜 : Type*) [NNNorm 𝕜] {E : Type*} [SMul 𝕜 E] {c : 𝕜} {s t : Set E} {x : E} {r : ℝ≥0∞}

lemma Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [FunLike F E E'] [MulActionHomClass F 𝕜 E E']
    (f : F) {t : Set E'} (h : MapsTo f s t) (x : E) : egauge 𝕜 t (f x) ≤ egauge 𝕜 s x :=
  iInf_mono fun c ↦ iInf_mono' fun hc ↦ ⟨h.smul_set c hc, le_rfl⟩
