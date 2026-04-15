/-
Extracted from LinearAlgebra/RootSystem/GeckConstruction/Basic.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Geck's construction of a Lie algebra associated to a root system

This file contains an implementation of Geck's construction of a semisimple Lie algebra from a
reduced crystallographic root system. It follows [Geck](Geck2017) quite closely.

## Main definitions:
* `RootPairing.GeckConstruction.lieAlgebra`: the Geck construction of the Lie algebra associated to
  a root system with distinguished base.
* `RootPairing.GeckConstruction.cartanSubalgebra`: a distinguished subalgebra corresponding to a
  Cartan subalgebra of the Geck construction.
* `RootPairing.GeckConstruction.cartanSubalgebra_le_lieAlgebra`: the distinguished subalgebra is
  contained in the Geck construction.

## Alternative approaches

There are at least three ways to construct a Lie algebra from a root system:
1. As a quotient of a free Lie algebra, using the Serre relations
2. Directly defining the Lie bracket on $H ⊕ K^∣Φ|$
3. The Geck construction

We comment on these as follows:
1. This construction takes just a matrix as input. It yields a semisimple Lie algebra iff the
   matrix is a Cartan matrix but it is quite a lot of work to prove this. On the other hand, it also
   allows construction of Kac-Moody Lie algebras. It has been implemented as `Matrix.ToLieAlgebra`
   but as of May 2025, almost nothing has been proved about it in Mathlib.
2. This construction takes a root system with base as input, together with sufficient additional
   data to determine a collection of extraspecial pairs of roots. The additional data for the
   extraspecial pairs is required to pin down certain signs when defining the Lie bracket. (These
   signs can be interpreted as a set-theoretic splitting of Tits's extension of the Weyl group by
   an elementary 2-group of order $2^l$ where $l$ is the rank.)
3. This construction takes a root system with base as input and is implemented here.

There seems to be no known construction of a Lie algebra from a root system without first choosing
a base: https://mathoverflow.net/questions/495434/

-/

noncomputable section

open Function Set Submodule

open scoped Matrix

attribute [local simp] Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}

def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i))

lemma h_def [DecidableEq ι] (i : b.support) :
    h i = .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

lemma h_eq_diagonal [DecidableEq ι] (i : b.support) :
    h i = .diagonal (Sum.elim 0 (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

variable (b) in

lemma linearIndependent_h [Finite ι] [CharZero R] [IsDomain R] [P.IsRootSystem] :
    LinearIndependent R (h (b := b)) := by
  classical
  have : Matrix.diagLinearMap (b.support ⊕ ι) R R ∘ h =
      Sum.elimZeroLeft ∘ fun i : b.support ↦ algebraMap ℤ R ∘ (P.pairingIn ℤ · i) := by
    ext; rw [comp_apply, h_def]; aesop
  apply LinearIndependent.of_comp (Matrix.diagLinearMap _ _ _)
  rw [this, LinearMap.linearIndependent_iff_of_injOn _ Sum.elim_injective'.injOn,
    linearIndependent_algebraMap_comp_iff]
  suffices LinearIndependent ℤ (fun i j : b.support ↦ P.pairingIn ℤ j i) from
    this.of_linearIndependent_subset b.support
  apply b.cartanMatrix.transpose.linearIndependent_rows_of_det_ne_zero
  rw [Matrix.det_transpose, ← Matrix.nondegenerate_iff_det_ne_zero]
  exact b.cartanMatrix_nondegenerate

lemma span_range_h_le_range_diagonal [DecidableEq ι] :
    span R (range h) ≤ LinearMap.range (Matrix.diagonalLinearMap (b.support ⊕ ι) R R) := by
  rw [span_le]
  rintro - ⟨i, rfl⟩
  rw [h_eq_diagonal]
  exact LinearMap.mem_range_self _ _

open Matrix in
