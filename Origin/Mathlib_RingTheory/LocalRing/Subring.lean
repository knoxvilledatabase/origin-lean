/-
Extracted from RingTheory/LocalRing/Subring.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subrings of local rings

We prove basic properties of subrings of local rings.
-/

namespace IsLocalRing

variable {R S} [Semiring R] [Semiring S]

open nonZeroDivisors

theorem of_injective [IsLocalRing S] {f : R →+* S} (hf : Function.Injective f)
    (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R := by
  haveI : Nontrivial R := f.domain_nontrivial
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab ↦
    (IsLocalRing.isUnit_or_isUnit_of_add_one (map_add f .. ▸ map_one f ▸ congrArg f hab)).imp ?_ ?_
  <;> exact h _ ∘ mem_nonZeroDivisors_of_injective hf ∘ IsUnit.mem_nonZeroDivisors

theorem of_subring [IsLocalRing S] {R : Subsemiring S} (h : ∀ a, a ∈ R⁰ → IsUnit a) :
    IsLocalRing R :=
  of_injective R.subtype_injective h

theorem of_subring' {R R' : Subsemiring S} [IsLocalRing R'] (inc : R ≤ R')
    (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R :=
  of_injective (Subsemiring.inclusion_injective inc) h

end IsLocalRing
