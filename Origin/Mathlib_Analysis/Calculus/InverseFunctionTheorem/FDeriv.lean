/-
Extracted from Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `HasStrictFDerivAt.toOpenPartialHomeomorph` that repacks a function `f`
with a `hf : HasStrictFDerivAt f f' a`, `f' : E ≃L[𝕜] F`, into an `OpenPartialHomeomorph`.
The `toFun` of this `OpenPartialHomeomorph` is defeq to `f`, so one can apply theorems
about `OpenPartialHomeomorph` to `hf.toOpenPartialHomeomorph f`, and get statements about `f`.

Then we define `HasStrictFDerivAt.localInverse` to be the `invFun` of this `OpenPartialHomeomorph`,
and prove two versions of the inverse function theorem:

* `HasStrictFDerivAt.to_localInverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.localInverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `HasStrictFDerivAt.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in the `Analysis/Calculus/FDeriv` and `Analysis/Calculus/Deriv`
folders, and in `ContDiff.lean`.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/

open Function Set Filter Metric

open scoped Topology NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Asymptotics Filter Metric Set

open ContinuousLinearMap (id)

/-!
### Inverse function theorem

Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `ApproximatesLinearOn` on an open neighborhood
of `a`, and we can apply `ApproximatesLinearOn.toOpenPartialHomeomorph` to construct the inverse
function. -/

namespace HasStrictFDerivAt

theorem approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) {c : ℝ≥0} (hc : Subsingleton E ∨ 0 < c) :
    ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c := by
  rcases hc with hE | hc
  · refine ⟨univ, IsOpen.mem_nhds isOpen_univ trivial, fun x _ y _ => ?_⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.isLittleO.def hc
  rw [nhds_prod_eq, Filter.Eventually, mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩

theorem map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) (h : f'.range = ⊤) :
    map f (𝓝 a) = 𝓝 (f a) := by
  let f'symm := f'.nonlinearRightInverseOfSurjective h
  set c : ℝ≥0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinearRightInverseOfSurjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c :=
    hf.approximates_deriv_on_nhds (Or.inr cpos)
  apply hs.map_nhds_eq f'symm s_nhds (Or.inr (NNReal.half_lt_self _))
  simp [ne_of_gt f'symm_pos]

variable {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

theorem approximates_deriv_on_open_nhds (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ s : Set E, a ∈ s ∧ IsOpen s ∧
      ApproximatesLinearOn f (f' : E →L[𝕜] F) s (‖(f'.symm : F →L[𝕜] E)‖₊⁻¹ / 2) := by
  simp only [← and_assoc]
  refine ((nhds_basis_opens a).exists_iff fun s t => ApproximatesLinearOn.mono_set).1 ?_
  exact
    hf.approximates_deriv_on_nhds <|
      f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' => half_pos <| inv_pos.2 hf'

variable (f)

variable [CompleteSpace E]

def toOpenPartialHomeomorph (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
  OpenPartialHomeomorph E F :=
    ApproximatesLinearOn.toOpenPartialHomeomorph f
    (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
      NNReal.half_lt_self <| ne_of_gt <| inv_pos.2 hf')
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.1

variable {f}
