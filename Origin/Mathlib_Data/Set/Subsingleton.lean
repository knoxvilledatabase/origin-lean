/-
Extracted from Data/Set/Subsingleton.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subsingleton

Defines the predicate `Subsingleton s : Prop`, saying that `s` has at most one element.

Also defines `Nontrivial s : Prop` : the predicate saying that `s` has at least two distinct
elements.

-/

assert_not_exists HeytingAlgebra RelIso

open Function

universe u v

namespace Set

/-! ### Subsingleton -/

section Subsingleton

variable {α : Type u} {a : α} {s t : Set α}

protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s), x = y

theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s ⊆ t) : s.Subsingleton := fun _ hx _ hy =>
  ht (hst hx) (hst hy)

theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩
