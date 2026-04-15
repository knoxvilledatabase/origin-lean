/-
Extracted from Data/Nat/GCD/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Properties of `Nat.gcd`, `Nat.lcm`, and `Nat.Coprime`

Definitions are provided in batteries.

Generalizations of these are provided in a later file as `GCDMonoid.gcd` and
`GCDMonoid.lcm`.

Note that the global `IsCoprime` is not a straightforward generalization of `Nat.Coprime`, see
`Nat.isCoprime_iff_coprime` for the connection between the two.

Most of this file could be moved to batteries as well.
-/

assert_not_exists IsOrderedMonoid

namespace Nat

variable {a a₁ a₂ b b₁ b₂ c : ℕ}

/-! ### `gcd` -/

theorem gcd_greatest {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : ℕ, e ∣ a → e ∣ b → e ∣ d) :
    d = a.gcd b :=
  (dvd_antisymm (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)) (dvd_gcd hda hdb)).symm

/-! Lemmas where one argument consists of addition of a multiple of the other -/
