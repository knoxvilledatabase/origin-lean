/-
Extracted from Data/Multiset/Antidiagonal.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/

assert_not_exists IsOrderedMonoid Ring

universe u

namespace Multiset

open List

variable {α β : Type*}

def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l ↦ (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun _ _ h ↦ Quot.sound (revzip_powersetAux_perm h)
