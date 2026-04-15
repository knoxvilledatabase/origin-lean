/-
Extracted from Analysis/Calculus/Deriv/Basic.lean
Genuine: 24 of 33 | Dissolved: 5 | Infrastructure: 4
-/
import Origin.Core

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

- `HasDerivAtFilter f f' L` states that the function `f` has the
  derivative `f'` along the filter `L : Filter (𝕜 × 𝕜)`.

- `HasDerivWithinAt f f' s x` states that the function `f` has the
  derivative `f'` at the point `x` within the subset `s`.

- `HasDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x`.

- `HasStrictDerivAt f f' x` states that the function `f` has the derivative `f'`
  at the point `x` in the sense of strict differentiability, i.e.,
  `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

- `derivWithin f s x` is a derivative of `f` at `x` within `s`. If the
  derivative does not exist, then `derivWithin f s x` equals zero.

- `deriv f x` is a derivative of `f` at `x`. If the derivative does not
  exist, then `deriv f x` equals zero.

The theorems `fderivWithin_derivWithin` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps (in `Linear.lean`)
  - addition (in `Add.lean`)
  - sum of finitely many functions (in `Add.lean`)
  - negation (in `Add.lean`)
  - subtraction (in `Add.lean`)
  - star (in `Star.lean`)
  - multiplication of two functions in `𝕜 → 𝕜` (in `Mul.lean`)
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E` (in `Mul.lean`)
  - powers of a function (in `Pow.lean` and `ZPow.lean`)
  - inverse `x → x⁻¹` (in `Inv.lean`)
  - division (in `Inv.lean`)
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜` (in `Comp.lean`)
  - composition of a function in `F → E` with a function in `𝕜 → F` (in `Comp.lean`)
  - inverse function (assuming that it exists; the inverse function theorem is in `Inverse.lean`)
  - polynomials (in `Polynomial.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp; ring
```

The relationship between the derivative of a function and its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`
is developed in the file `Mathlib/Analysis/Calculus/Deriv/Slope.lean`.

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. See the explanations there.
-/

universe u v w

noncomputable section

open scoped Topology ENNReal NNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight toSpanSingleton_inj toSpanSingleton)

section TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable [ContinuousSMul 𝕜 F]

def HasDerivAtFilter (f : 𝕜 → F) (f' : F) (L : Filter (𝕜 × 𝕜)) :=
  HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L

def HasDerivWithinAt (f : 𝕜 → F) (f' : F) (s : Set 𝕜) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝[s] x ×ˢ pure x)

def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)

def HasStrictDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
  HasDerivAtFilter f f' (𝓝 (x, x))

end

def derivWithin (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) :=
  fderivWithin 𝕜 f s x 1

def deriv (f : 𝕜 → F) (x : 𝕜) :=
  fderiv 𝕜 f x 1

variable {f f₀ f₁ : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L : Filter (𝕜 × 𝕜)}

variable [ContinuousSMul 𝕜 F]

theorem hasFDerivAtFilter_iff_hasDerivAtFilter {f' : 𝕜 →L[𝕜] F} :
    HasFDerivAtFilter f f' L ↔ HasDerivAtFilter f (f' 1) L := by simp [HasDerivAtFilter]

alias ⟨HasFDerivAtFilter.hasDerivAtFilter, _⟩ := hasFDerivAtFilter_iff_hasDerivAtFilter

theorem hasDerivAtFilter_iff_hasFDerivAtFilter :
    HasDerivAtFilter f f' L ↔ HasFDerivAtFilter f (toSpanSingleton 𝕜 f') L :=
  .rfl

alias ⟨HasDerivAtFilter.hasFDerivAtFilter, _⟩ := hasDerivAtFilter_iff_hasFDerivAtFilter

theorem hasFDerivWithinAt_iff_hasDerivWithinAt {f' : 𝕜 →L[𝕜] F} :
    HasFDerivWithinAt f f' s x ↔ HasDerivWithinAt f (f' 1) s x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivWithinAt.hasDerivWithinAt, _⟩ := hasFDerivWithinAt_iff_hasDerivWithinAt

alias ⟨HasDerivWithinAt.hasFDerivWithinAt, _⟩ :=

  hasDerivWithinAt_iff_hasFDerivWithinAt

theorem hasFDerivAt_iff_hasDerivAt {f' : 𝕜 →L[𝕜] F} : HasFDerivAt f f' x ↔ HasDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

alias ⟨HasFDerivAt.hasDerivAt, _⟩ := hasFDerivAt_iff_hasDerivAt

alias ⟨HasDerivAt.hasFDerivAt, _⟩ := hasDerivAt_iff_hasFDerivAt

theorem hasStrictFDerivAt_iff_hasStrictDerivAt {f' : 𝕜 →L[𝕜] F} :
    HasStrictFDerivAt f f' x ↔ HasStrictDerivAt f (f' 1) x :=
  hasFDerivAtFilter_iff_hasDerivAtFilter

protected alias ⟨HasStrictFDerivAt.hasStrictDerivAt, _⟩ :=

  hasStrictFDerivAt_iff_hasStrictDerivAt

alias ⟨HasStrictDerivAt.hasStrictFDerivAt, _⟩ := hasStrictDerivAt_iff_hasStrictFDerivAt

end

theorem derivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    derivWithin f s x = 0 := by
  unfold derivWithin
  rw [fderivWithin_zero_of_not_differentiableWithinAt h]
  simp

-- DISSOLVED: differentiableWithinAt_of_derivWithin_ne_zero

end TVS

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f f₀ f₁ : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter (𝕜 × 𝕜)}

theorem derivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) : derivWithin f s x = 0 := by
  rw [derivWithin, fderivWithin_zero_of_not_accPt h, ContinuousLinearMap.zero_apply]

theorem derivWithin_zero_of_not_uniqueDiffWithinAt (h : ¬UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = 0 :=
  derivWithin_zero_of_not_accPt <| mt AccPt.uniqueDiffWithinAt h

theorem derivWithin_zero_of_notMem_closure (h : x ∉ closure s) : derivWithin f s x = 0 := by
  rw [derivWithin, fderivWithin_zero_of_notMem_closure h, ContinuousLinearMap.zero_apply]

theorem deriv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0 := by
  unfold deriv
  rw [fderiv_zero_of_not_differentiableAt h]
  simp

-- DISSOLVED: differentiableAt_of_deriv_ne_zero

theorem UniqueDiffWithinAt.eq_deriv (s : Set 𝕜) (H : UniqueDiffWithinAt 𝕜 s x)
    (h : HasDerivWithinAt f f' s x) (h₁ : HasDerivWithinAt f f₁' s x) : f' = f₁' :=
  toSpanSingleton_inj.mp <| UniqueDiffWithinAt.eq H h h₁

theorem hasDerivAtFilter_iff_isLittleO :
    HasDerivAtFilter f f' L ↔
      (fun p => f p.1 - f p.2 - (p.1 - p.2) • f') =o[L] fun p => p.1 - p.2 :=
  hasFDerivAtFilter_iff_isLittleO ..

theorem hasDerivAtFilter_iff_tendsto :
    HasDerivAtFilter f f' L ↔
      Tendsto (fun p ↦ ‖p.1 - p.2‖⁻¹ * ‖f p.1 - f p.2 - (p.1 - p.2) • f'‖) L (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

theorem hasDerivWithinAt_iff_isLittleO :
    HasDerivWithinAt f f' s x ↔
      (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝[s] x] fun x' => x' - x :=
  hasFDerivWithinAt_iff_isLittleO

alias ⟨HasDerivWithinAt.isLittleO, HasDerivWithinAt.of_isLittleO⟩ := hasDerivWithinAt_iff_isLittleO

theorem hasDerivWithinAt_iff_tendsto :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto

theorem hasDerivAt_iff_isLittleO :
    HasDerivAt f f' x ↔ (fun x' : 𝕜 => f x' - f x - (x' - x) • f') =o[𝓝 x] fun x' => x' - x :=
  hasFDerivAt_iff_isLittleO ..

alias ⟨HasDerivAt.isLittleO, HasDerivAt.of_isLittleO⟩ := hasDerivAt_iff_isLittleO

theorem hasDerivAt_iff_tendsto :
    HasDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAt_iff_tendsto

theorem HasDerivAtFilter.isBigO_sub (h : HasDerivAtFilter f f' L) :
    (fun p => f p.1 - f p.2) =O[L] fun p => p.1 - p.2 :=
  HasFDerivAtFilter.isBigO_sub h

-- DISSOLVED: isInducing_toSpanSingleton

-- DISSOLVED: HasDerivAtFilter.isEquivalent_sub

-- DISSOLVED: HasDerivAtFilter.isTheta_sub
