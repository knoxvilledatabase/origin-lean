/-
Extracted from Topology/Order/CountableSeparating.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Countably many infinite intervals separate points

In this file we prove that in a linear order with second countable order topology,
the points can be separated by countably many infinite intervals.
We prove 4 versions of this statement (one for each of the infinite intervals),
as well as provide convenience corollaries about `Filter.EventuallyEq`.
-/

open Set

variable {X : Type*} [TopologicalSpace X] [LinearOrder X]
  [OrderTopology X] [SecondCountableTopology X]

namespace HasCountableSeparatingOn

variable {s : Set X}

-- INSTANCE (free from Core): range_Iio

-- INSTANCE (free from Core): range_Ioi

-- INSTANCE (free from Core): range_Iic

-- INSTANCE (free from Core): range_Ici

end HasCountableSeparatingOn

namespace Filter.EventuallyEq

variable {α : Type*} {l : Filter α} [CountableInterFilter l] {f g : α → X}

lemma of_forall_eventually_lt_iff (h : ∀ x, ∀ᶠ a in l, f a < x ↔ g a < x) : f =ᶠ[l] g :=
  of_forall_separating_preimage (· ∈ range Iio) <| forall_mem_range.2 <| fun x ↦ .set_eq (h x)

lemma of_forall_eventually_le_iff (h : ∀ x, ∀ᶠ a in l, f a ≤ x ↔ g a ≤ x) : f =ᶠ[l] g :=
  of_forall_separating_preimage (· ∈ range Iic) <| forall_mem_range.2 <| fun x ↦ .set_eq (h x)

lemma of_forall_eventually_gt_iff (h : ∀ x, ∀ᶠ a in l, x < f a ↔ x < g a) : f =ᶠ[l] g :=
  of_forall_eventually_lt_iff (X := Xᵒᵈ) h

lemma of_forall_eventually_ge_iff (h : ∀ x, ∀ᶠ a in l, x ≤ f a ↔ x ≤ g a) : f =ᶠ[l] g :=
  of_forall_eventually_le_iff (X := Xᵒᵈ) h

end Filter.EventuallyEq
