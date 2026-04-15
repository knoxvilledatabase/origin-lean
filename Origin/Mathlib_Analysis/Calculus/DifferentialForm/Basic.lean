/-
Extracted from Analysis/Calculus/DifferentialForm/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exterior derivative of a differential form on a normed space

In this file we define the exterior derivative of a differential form on a normed space.
Under certain smoothness assumptions, we prove that this operation is linear in the form
and the second exterior derivative of a form is zero.

We represent a differential `n`-form on `E` taking values in `F` as `E → E [⋀^Fin n]→L[𝕜] F`.

## Implementation notes

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeriv_apply`.

## TODO

- Introduce notation for:
  - an unbundled `n`-form on a normed space;
  - a bundled `C^r`-smooth `n`-form on a normed space;
  - same for manifolds (not defined yet).
- Introduce bundled `C^r`-smooth `n`-forms on normed spaces and manifolds.
  - Discuss the future API and the use cases that need to be covered on Zulip.
  - Introduce new types & notation, copy the API.
- Add shorter and more readable definitions (or abbreviations?)
  for `0`-forms (`constOfIsEmpty`) and `1`-forms (`ofSubsingleton`),
  sync with the API for `ContinuousMultilinearMap`.
-/

open Filter ContinuousAlternatingMap Set

open scoped Topology

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n m k : ℕ} {r : WithTop ℕ∞}
  {ω ω₁ ω₂ : E → E [⋀^Fin n]→L[𝕜] F} {s t : Set E} {x : E}

noncomputable def extDeriv (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderiv 𝕜 ω x)

noncomputable def extDerivWithin (ω : E → E [⋀^Fin n]→L[𝕜] F) (s : Set E) (x : E) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderivWithin 𝕜 ω s x)
