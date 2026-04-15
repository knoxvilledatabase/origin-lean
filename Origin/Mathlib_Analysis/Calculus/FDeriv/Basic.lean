/-
Extracted from Analysis/Calculus/FDeriv/Basic.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The Fréchet derivative: basic properties

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `HasFDerivWithinAt f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasFDerivAt f f' x := HasFDerivWithinAt f f' x univ`

Finally,

  `HasStrictFDerivAt f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`IsBoundedBilinearMap.hasFDerivAt` twice: first for `HasFDerivAt`, then for
`HasStrictFDerivAt`.

## Main results

This file builds on the bare-bones definition given in `Defs.lean` by establishing a variety of
relatively straightforward properties of the derivative.

Deeper properties are defined in other files in the folder `Analysis/Calculus/FDeriv/`, which
contain the usual formulas (and existence assertions) for the derivative of
* constants (`Const.lean`)
* bounded linear maps (`Linear.lean`)
* bounded bilinear maps (`Bilinear.lean`)
* sum of two functions (`Add.lean`)
* sum of finitely many functions (`Add.lean`)
* multiplication of a function by a scalar constant (`Add.lean`)
* negative of a function (`Add.lean`)
* subtraction of two functions (`Add.lean`)
* multiplication of a function by a scalar function (`Mul.lean`)
* multiplication of two scalar functions (`Mul.lean`)
* composition of functions (the chain rule) (`Comp.lean`)
* inverse function (`Mul.lean`)
  (assuming that it exists; the inverse function theorem is in `../Inverse.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `Deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : Differentiable ℝ (fun x ↦ sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : DifferentiableAt ℝ (fun x ↦ exp x / (1 + sin x)) x := by
  simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `Deriv.lean`.

## Implementation details

For a discussion of the definitions and their rationale, see the file docstring of
`Mathlib.Analysis.Calculus.FDeriv.Defs`.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their Cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(fun x ↦ exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

## TODO

Generalize more results to topological vector spaces.

## Tags

derivative, differentiable, Fréchet, calculus

-/

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section DerivativeUniqueness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

variable {f : E → F}

variable {f' f₁' : E →L[𝕜] F}

variable {x : E}

variable {s : Set E}

/-!
### Uniqueness of the derivative

In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `UniqueDiffWithinAt` and `UniqueDiffOn` indeed imply the
uniqueness of the derivative. -/

theorem HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f' s x) {α : Type*} {l : Filter α}
    {c : α → 𝕜} {d : α → E} {v : E} (dlim : Tendsto d l (𝓝 0)) (dtop : ∀ᶠ n in l, x + d n ∈ s)
    (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (x + d n) - f x)) l (𝓝 (f' v)) := by
  have tendsto_arg : Tendsto (fun n => x + d n) l (𝓝[s] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using tendsto_const_nhds.add dlim, dtop⟩
  have := calc
    (fun n ↦ c n • (f (x + d n) - f x) - f' (c n • d n)) =o[𝕜; l] fun n ↦ c n • d n := by
      simpa [smul_sub] using h.isLittleOTVS.comp_tendsto tendsto_arg |>.smul_left c
    _ =O[𝕜; l] (1 : α → 𝕜) := cdlim.isBigOTVS_one _
  rw [isLittleOTVS_one] at this
  simpa using this.add <| ((map_continuous f').tendsto v).comp cdlim

variable [T2Space F]

theorem HasFDerivWithinAt.unique_on (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : EqOn f' f₁' (tangentConeAt 𝕜 s x) := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  exact tendsto_nhds_unique (hf.lim hd₀ hds hcd) (hg.lim hd₀ hds hcd)

theorem UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)

theorem UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : HasFDerivWithinAt f f' s x)
    (h₁ : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  (H x hx).eq h h₁

theorem HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x) : f' = f₁' := by
  rw [HasFDerivAt, ← nhdsWithin_univ] at *
  exact uniqueDiffWithinAt_univ.eq h₀ h₁

end DerivativeUniqueness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable {x : E}

variable {s t : Set E}

variable {L L₁ L₂ : Filter (E × E)}

section FDerivProperties

/-! ### Basic properties of the derivative -/

nonrec theorem HasFDerivAtFilter.mono (h : HasFDerivAtFilter f f' L₂) (hst : L₁ ≤ L₂) :
    HasFDerivAtFilter f f' L₁ :=
  .of_isLittleOTVS <| h.isLittleOTVS.mono hst
