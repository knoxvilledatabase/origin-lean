/-
Extracted from Data/Set/Pointwise/Support.lean
Genuine: 2 | Conflates: 0 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Set.Pointwise.SMul

/-!
# Support of a function composed with a scalar action

We show that the support of `x ↦ f (c⁻¹ • x)` is equal to `c • support f`.
-/

open Pointwise

open Function Set

section Group

variable {α β γ : Type*} [Group α] [MulAction α β]

theorem mulSupport_comp_inv_smul [One γ] (c : α) (f : β → γ) :
    (mulSupport fun x ↦ f (c⁻¹ • x)) = c • mulSupport f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mulSupport]

theorem support_comp_inv_smul [Zero γ] (c : α) (f : β → γ) :
    (support fun x ↦ f (c⁻¹ • x)) = c • support f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]

attribute [to_additive existing support_comp_inv_smul] mulSupport_comp_inv_smul

end Group

section GroupWithZero

variable {α β γ : Type*} [GroupWithZero α] [MulAction α β]

-- DISSOLVED: mulSupport_comp_inv_smul₀

-- DISSOLVED: support_comp_inv_smul₀

attribute [to_additive existing support_comp_inv_smul₀] mulSupport_comp_inv_smul₀

end GroupWithZero
