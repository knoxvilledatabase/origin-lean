/-
Extracted from Algebra/Star/RingQuot.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The *-ring structure on suitable quotients of a *-ring.
-/

namespace RingQuot

universe u

variable {R : Type u} [Semiring R] (r : R → R → Prop)

section StarRing

variable [StarRing R]

set_option linter.style.whitespace false in -- manual alignment is not recognised

theorem Rel.star (hr : ∀ a b, r a b → r (star a) (star b))
    ⦃a b : R⦄ (h : Rel r a b) : Rel r (star a) (star b) := by
  induction h with
  | of h          => exact Rel.of (hr _ _ h)
  | add_left _ h  => rw [star_add, star_add]
                     exact Rel.add_left h
  | mul_left _ h  => rw [star_mul, star_mul]
                     exact Rel.mul_right h
  | mul_right _ h => rw [star_mul, star_mul]
                     exact Rel.mul_left h

private def star' (hr : ∀ a b, r a b → r (star a) (star b)) : RingQuot r → RingQuot r
  | ⟨a⟩ => ⟨Quot.map (star : R → R) (Rel.star r hr) a⟩
