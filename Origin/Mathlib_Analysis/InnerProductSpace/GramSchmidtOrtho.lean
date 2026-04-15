/-
Extracted from Analysis/InnerProductSpace/GramSchmidtOrtho.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gramSchmidt`: the Gram-Schmidt process
- `gramSchmidt_orthogonal`: `gramSchmidt` produces an orthogonal system of vectors.
- `span_gramSchmidt`: `gramSchmidt` preserves span of vectors.
- `gramSchmidt_linearIndependent`: if the input vectors of `gramSchmidt` are linearly independent,
  then so are the output vectors.
- `gramSchmidt_ne_zero`: if the input vectors of `gramSchmidt` are linearly independent,
  then the output vectors are non-zero.
- `gramSchmidtBasis`: the basis produced by the Gram-Schmidt process when given a basis as input
- `gramSchmidtNormed`:
  the normalized `gramSchmidt` process, i.e each vector in `gramSchmidtNormed` has unit length
- `gramSchmidt_orthonormal`: `gramSchmidtNormed` produces an orthonormal system of vectors.
- `gramSchmidtOrthonormalBasis`: orthonormal basis constructed by the Gram-Schmidt process from
  an indexed set of vectors of the right size
-/

open Finset Submodule Module

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace InnerProductSpace

noncomputable def gramSchmidt [WellFoundedLT ι] (f : ι → E) (n : ι) : E :=
  f n - ∑ i : Iio n, (𝕜 ∙ gramSchmidt f i).starProjection (f n)

termination_by n

decreasing_by exact mem_Iio.1 i.2

theorem gramSchmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]

theorem gramSchmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [gramSchmidt_def, sub_add_cancel]

theorem gramSchmidt_def'' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n,
      (⟪gramSchmidt 𝕜 f i, f n⟫ / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i := by
  simp only [← map_pow, ← starProjection_singleton, ← gramSchmidt_def' 𝕜 f n]
