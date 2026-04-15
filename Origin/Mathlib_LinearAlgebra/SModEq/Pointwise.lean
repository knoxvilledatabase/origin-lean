/-
Extracted from LinearAlgebra/SModEq/Pointwise.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pointwise lemmas for modular equivalence

In this file, we record more lemmas about `SModEq` on elements
of modules or rings.
-/

open Submodule

open Polynomial

variable {R : Type*} [Ring R] {I : Ideal R}

variable {M : Type*} [AddCommGroup M] [Module R M] {U : Submodule R M}

variable {x y : M}

namespace SModEq

theorem smul' (hxy : x ≡ y [SMOD U])
    {c : R} (hc : c ∈ I) : c • x ≡ c • y [SMOD (I • U)] := by
  rw [SModEq.sub_mem] at hxy ⊢
  rw [← smul_sub]
  exact smul_mem_smul hc hxy

end SModEq
