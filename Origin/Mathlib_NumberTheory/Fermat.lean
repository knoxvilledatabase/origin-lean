/-
Extracted from NumberTheory/Fermat.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fermat numbers

The Fermat numbers are a sequence of natural numbers defined as `Nat.fermatNumber n = 2^(2^n) + 1`,
for all natural numbers `n`.

## Main theorems

- `Nat.coprime_fermatNumber_fermatNumber`: two distinct Fermat numbers are coprime.
- `Nat.pepin_primality`: For 0 < n, Fermat number Fₙ is prime if `3 ^ (2 ^ (2 ^ n - 1)) = -1 mod Fₙ`
- `fermat_primeFactors_one_lt`: For 1 < n, Prime factors the Fermat number Fₙ are of
  form `k * 2 ^ (n + 2) + 1`.
-/

open Function

namespace Nat

open Finset Nat ZMod

def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1
