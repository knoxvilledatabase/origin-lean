/-
Extracted from LinearAlgebra/QuadraticForm/Radical.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The radical of a quadratic form

We define the radical of a quadratic form. This is a standard construction if 2 is invertible
in the coefficient ring, but is more fiddly otherwise. We follow the account in
Chapter II, §7 of [elman-karpenko-merkurjev-2008].
-/

open Finset QuadraticMap

namespace QuadraticMap

variable {R M M' P : Type*} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup P]
  [CommRing R] [Module R M] [Module R M'] [Module R P] (Q : QuadraticMap R M P)

def radical : Submodule R M where
  carrier := {x : M | Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0}
  zero_mem' := by simp
  smul_mem' a x hx := by simp [QuadraticMap.map_smul, hx.1, hx.2]
  add_mem' := fun {x y} hx hy ↦ by
    refine ⟨?_, by simp [hx.2, hy.2]⟩
    have := congr_arg (· y) hx.2
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.zero_apply, sub_sub, sub_eq_zero] at this
    rw [this, hx.1, hy.1, zero_add]

variable {Q}

lemma mem_radical_iff' {m : M} :
    m ∈ Q.radical ↔ Q m = 0 ∧ ∀ n : M, Q (m + n) = Q n := by
  simp +contextual [radical, QuadraticMap.polarBilin, LinearMap.ext_iff,
    QuadraticMap.polar, sub_sub, sub_eq_zero]
