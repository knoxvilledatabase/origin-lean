/-
Extracted from Data/ZMod/IntUnitsPower.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# The power operator on `ℤˣ` by `ZMod 2`, `ℕ`, and `ℤ`

See also the related `negOnePow`.

## TODO

* Generalize this to `Pow G (Zmod n)` where `orderOf g = n`.

## Implementation notes

In future, we could consider a `LawfulPower M R` typeclass; but we can save ourselves a lot of work
by using `Module R (Additive M)` in its place, especially since this already has instances for
`R = ℕ` and `R = ℤ`.
-/

assert_not_exists Ideal TwoSidedIdeal

-- INSTANCE (free from Core): :

lemma ZMod.natCast_smul_units (n : ℕ) (au : Additive ℤˣ) : (n : ZMod 2) • au = n • au :=
  (Int.units_pow_eq_pow_mod_two au n).symm

-- INSTANCE (free from Core): :

section CommSemiring

variable {R : Type*} [CommSemiring R] [Module R (Additive ℤˣ)]

-- INSTANCE (free from Core): Int.instUnitsPow

example : Int.instUnitsPow = Monoid.toPow := rfl

example : Int.instUnitsPow = DivInvMonoid.toZPow := rfl
