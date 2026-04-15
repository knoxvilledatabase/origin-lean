/-
Extracted from RingTheory/WittVector/Domain.lean
Genuine: 3 of 7 | Dissolved: 1 | Infrastructure: 3
-/
import Origin.Core

/-!

# Witt vectors over a domain

This file builds to the proof `WittVector.instIsDomain`,
an instance that says if `R` is an integral domain, then so is `𝕎 R`.
It depends on the API around iterated applications
of `WittVector.verschiebung` and `WittVector.frobenius`
found in `Identities.lean`.

The [proof sketch](https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723)
goes as follows:
any nonzero $x$ is an iterated application of $V$
to some vector $w_x$ whose 0th component is nonzero (`WittVector.verschiebung_nonzero`).
Known identities (`WittVector.iterate_verschiebung_mul`) allow us to transform
the product of two such $x$ and $y$
to the form $V^{m+n}\left(F^n(w_x) \cdot F^m(w_y)\right)$,
the 0th component of which must be nonzero.

## Main declarations

* `WittVector.iterate_verschiebung_mul_coeff` : an identity from [Haze09]
* `WittVector.instIsDomain`

-/

noncomputable section

namespace WittVector

open Function

variable {p : ℕ} {R : Type*}

local notation "𝕎" => WittVector p -- type as `\bbW`

/-!
## The `shift` operator
-/

def shift (x : 𝕎 R) (n : ℕ) : 𝕎 R :=
  @mk' p R fun i => x.coeff (n + i)

variable [hp : Fact p.Prime] [CommRing R]

theorem verschiebung_shift (x : 𝕎 R) (k : ℕ) (h : ∀ i < k + 1, x.coeff i = 0) :
    verschiebung (x.shift k.succ) = x.shift k := by
  ext ⟨j⟩
  · rw [verschiebung_coeff_zero, shift_coeff, h]
    apply Nat.lt_succ_self
  · simp only [verschiebung_coeff_succ, shift]
    congr 1
    rw [Nat.add_succ, add_comm, Nat.add_succ, add_comm]

theorem eq_iterate_verschiebung {x : 𝕎 R} {n : ℕ} (h : ∀ i < n, x.coeff i = 0) :
    x = verschiebung^[n] (x.shift n) := by
  induction n with
  | zero => cases x; simp [shift]
  | succ k ih =>
    dsimp; rw [verschiebung_shift]
    · exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_self _))
    · exact h

-- DISSOLVED: verschiebung_nonzero

/-!
## Witt vectors over a domain

If `R` is an integral domain, then so is `𝕎 R`.
This argument is adapted from
<https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723>.
-/

-- INSTANCE (free from Core): [CharP

-- INSTANCE (free from Core): instIsDomain

end WittVector
