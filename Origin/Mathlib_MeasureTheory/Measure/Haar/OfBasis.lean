/-
Extracted from MeasureTheory/Measure/Haar/OfBasis.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Additive Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelepiped spanned by the basis.

## Main definitions

* `parallelepiped v` is the parallelepiped spanned by a finite family of vectors.
* `Basis.parallelepiped` is the parallelepiped associated to a basis, seen as a compact set with
  nonempty interior.
* `Basis.addHaar` is the Lebesgue measure associated to a basis, giving measure `1` to the
  corresponding parallelepiped.

In particular, we declare a `MeasureSpace` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/

open Set TopologicalSpace MeasureTheory MeasureTheory.Measure Module

open scoped Pointwise

noncomputable section

variable {ι ι' E F : Type*}

section Fintype

variable [Fintype ι] [Fintype ι']

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Icc 0 1

theorem mem_parallelepiped_iff (v : ι → E) (x : E) :
    x ∈ parallelepiped v ↔ ∃ t ∈ Icc (0 : ι → ℝ) 1, x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]

theorem parallelepiped_basis_eq (b : Basis ι ℝ E) :
    parallelepiped b = {x | ∀ i, b.repr x i ∈ Set.Icc 0 1} := by
  classical
  ext x
  simp_rw [mem_parallelepiped_iff, mem_setOf_eq, b.ext_elem_iff, _root_.map_sum,
    map_smul, Finset.sum_apply', Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mem_Icc,
    Pi.le_def, Pi.zero_apply, Pi.one_apply, ← forall_and]
  aesop

theorem image_parallelepiped (f : E →ₗ[ℝ] F) (v : ι → E) :
    f '' parallelepiped v = parallelepiped (f ∘ v) := by
  simp only [parallelepiped, ← image_comp]
  congr 1 with t
  simp only [Function.comp_apply, _root_.map_sum, map_smulₛₗ, RingHom.id_apply]
