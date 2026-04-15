/-
Extracted from Analysis/Calculus/InverseFunctionTheorem/Deriv.lean
Genuine: 4 of 5 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, 1D case

In this file we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `ContinuousLinearEquiv.unitsEquivAut` to translate `HasStrictDerivAt f f' a` and
`f' ≠ 0` into `HasStrictFDerivAt f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/

open Filter

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (f : 𝕜 → 𝕜)

noncomputable section

namespace HasStrictDerivAt

variable (f' a : 𝕜) (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0)

include hf hf'

abbrev localInverse : 𝕜 → 𝕜 :=
  (hf.hasStrictFDerivAt_equiv hf').localInverse _ _ _

variable {f f' a}

theorem map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').map_nhds_eq_of_equiv

theorem to_localInverse : HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_localInverse

theorem to_local_left_inverse {g : 𝕜 → 𝕜} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    HasStrictDerivAt g f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_local_left_inverse hg

end HasStrictDerivAt

variable {f}

-- DISSOLVED: isOpenMap_of_hasStrictDerivAt

alias open_map_of_strict_deriv := isOpenMap_of_hasStrictDerivAt
