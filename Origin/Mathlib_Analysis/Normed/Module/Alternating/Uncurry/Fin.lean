/-
Extracted from Analysis/Normed/Module/Alternating/Uncurry/Fin.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uncurrying continuous alternating maps

Given a continuous function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines a continuous alternating form `ContinuousAlternatingMap.alternatizeUncurryFin f`
in `n + 1` arguments.

This function is given by
```
ContinuousAlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given a continuous alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `𝕜`-multilinear maps over any normed field `𝕜`,
not only a field of characteristic zero.

## Main results

- `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of continuous alternating maps,
  then the twice uncurried `f` is zero.

The latter theorem will be used
to prove that the second exterior derivative of a differential form is zero.
-/

open Fin Function

namespace ContinuousAlternatingMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ}

theorem map_insertNth (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (p : Fin (n + 1)) (x : E) (v : Fin n → E) :
    f (p.insertNth x v) = (-1) ^ (p : ℕ) • f (Matrix.vecCons x v) :=
  f.toAlternatingMap.map_insertNth p x v

theorem neg_one_pow_smul_map_insertNth (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (p : Fin (n + 1)) (x : E)
    (v : Fin n → E) : (-1) ^ (p : ℕ) • f (p.insertNth x v) = f (Matrix.vecCons x v) :=
  f.toAlternatingMap.neg_one_pow_smul_map_insertNth p x v

theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : E [⋀^Fin n]→L[𝕜] F)
    {v : Fin (n + 1) → E} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ (i : ℕ) • f (i.removeNth v) + (-1) ^ (j : ℕ) • f (j.removeNth v) = 0 :=
  f.toAlternatingMap.neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq hvij hij

set_option backward.privateInPublic true in

private def alternatizeUncurryFinCLM.aux :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →ₗ[𝕜] E [⋀^Fin (n + 1)]→ₗ[𝕜] F :=
  AlternatingMap.alternatizeUncurryFinLM ∘ₗ (toAlternatingMapLinear (R := 𝕜)).compRight (S := 𝕜) ∘ₗ
    ContinuousLinearMap.coeLM 𝕜

private lemma alternatizeUncurryFinCLM.aux_apply (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F)
    (v : Fin (n + 1) → E) :
    aux f v = ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (i.removeNth v) := by
  simp [aux, AlternatingMap.alternatizeUncurryFin_apply]

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

variable (𝕜 E F) in
