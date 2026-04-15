/-
Extracted from LinearAlgebra/LinearIndependent/BaseChange.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Base change for linear independence

This file is a place to collect base change results for linear independence.

-/

open Function Set TensorProduct

variable {ι ι' : Type*} [Finite ι']

private lemma LinearIndependent.linearIndependent_algebraMap_comp_aux {K : Type*} (L : Type*)
    [Field K] [Field L] [Algebra K L]
    {v : ι → ι' → K} (hv : LinearIndependent K v) :
    LinearIndependent L (fun i ↦ algebraMap K L ∘ v i) := by
  classical
  let : Fintype ι' := .ofFinite ι'
  let I : Set (ι' → K) := hv.linearIndepOn_id.extend (subset_univ _)
  let b : Module.Basis I K (ι' → K) := .extend hv.linearIndepOn_id
  let b' : Module.Basis I L (ι' → L) := (b.baseChange L).map (TensorProduct.piScalarRight K L L ι')
  let v' (i : ι) : I := ⟨v i, hv.linearIndepOn_id.subset_extend _ <| mem_range_self i⟩
  have hv' : b' ∘ v' = fun i ↦ algebraMap K L ∘ v i := by
    ext; simp [b', b, v', Module.Basis.extend, Algebra.algebraMap_eq_smul_one]
  have h_inj : Injective v' := fun i j hij ↦ by have : Injective v := hv.injective; aesop
  rw [← hv']
  exact b'.linearIndependent.comp _ h_inj
