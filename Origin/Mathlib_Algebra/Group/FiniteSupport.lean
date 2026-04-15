/-
Extracted from Algebra/Group/FiniteSupport.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of support
-/

namespace Function

variable {α β γ : Type*} [One γ]

@[to_additive (attr := simp)]
lemma mulSupport_along_fiber_finite_of_finite (f : α × β → γ) (a : α) (h : (mulSupport f).Finite) :
    (mulSupport fun b ↦ f (a, b)).Finite :=
  (h.image Prod.snd).subset (mulSupport_along_fiber_subset f a)

end Function
