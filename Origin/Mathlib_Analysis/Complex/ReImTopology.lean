/-
Extracted from Analysis/Complex/ReImTopology.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Closure, interior, and frontier of preimages under `re` and `im`

In this fact we use the fact that `ℂ` is naturally homeomorphic to `ℝ × ℝ` to deduce some
topological properties of `Complex.re` and `Complex.im`.

## Main statements

Each statement about `Complex.re` listed below has a counterpart about `Complex.im`.

* `Complex.isHomeomorphicTrivialFiberBundle_re`: `Complex.re` turns `ℂ` into a trivial
  topological fiber bundle over `ℝ`;
* `Complex.isOpenMap_re`, `Complex.isQuotientMap_re`: in particular, `Complex.re` is an open map
  and is a quotient map;
* `Complex.interior_preimage_re`, `Complex.closure_preimage_re`, `Complex.frontier_preimage_re`:
  formulas for `interior (Complex.re ⁻¹' s)` etc;
* `Complex.interior_setOf_re_le` etc: particular cases of the above formulas in the cases when `s`
  is one of the infinite intervals `Set.Ioi a`, `Set.Ici a`, `Set.Iio a`, and `Set.Iic a`,
  formulated as `interior {z : ℂ | z.re ≤ a} = {z | z.re < a}` etc.

## Tags

complex, real part, imaginary part, closure, interior, frontier
-/

open Set Topology

noncomputable section

namespace Complex

theorem isHomeomorphicTrivialFiberBundle_re : IsHomeomorphicTrivialFiberBundle ℝ re :=
  ⟨equivRealProdCLM.toHomeomorph, fun _ => rfl⟩

theorem isHomeomorphicTrivialFiberBundle_im : IsHomeomorphicTrivialFiberBundle ℝ im :=
  ⟨equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ), fun _ => rfl⟩

theorem isOpenMap_re : IsOpenMap re :=
  isHomeomorphicTrivialFiberBundle_re.isOpenMap_proj

theorem isOpenMap_im : IsOpenMap im :=
  isHomeomorphicTrivialFiberBundle_im.isOpenMap_proj

theorem isQuotientMap_re : IsQuotientMap re :=
  isHomeomorphicTrivialFiberBundle_re.isQuotientMap_proj

theorem isQuotientMap_im : IsQuotientMap im :=
  isHomeomorphicTrivialFiberBundle_im.isQuotientMap_proj

theorem interior_preimage_re (s : Set ℝ) : interior (re ⁻¹' s) = re ⁻¹' interior s :=
  (isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re _).symm

theorem interior_preimage_im (s : Set ℝ) : interior (im ⁻¹' s) = im ⁻¹' interior s :=
  (isOpenMap_im.preimage_interior_eq_interior_preimage continuous_im _).symm

theorem closure_preimage_re (s : Set ℝ) : closure (re ⁻¹' s) = re ⁻¹' closure s :=
  (isOpenMap_re.preimage_closure_eq_closure_preimage continuous_re _).symm

theorem closure_preimage_im (s : Set ℝ) : closure (im ⁻¹' s) = im ⁻¹' closure s :=
  (isOpenMap_im.preimage_closure_eq_closure_preimage continuous_im _).symm

theorem frontier_preimage_re (s : Set ℝ) : frontier (re ⁻¹' s) = re ⁻¹' frontier s :=
  (isOpenMap_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm

theorem frontier_preimage_im (s : Set ℝ) : frontier (im ⁻¹' s) = im ⁻¹' frontier s :=
  (isOpenMap_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm
