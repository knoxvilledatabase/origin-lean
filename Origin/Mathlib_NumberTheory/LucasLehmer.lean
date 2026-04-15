/-
Extracted from NumberTheory/LucasLehmer.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Lucas-Lehmer test for Mersenne primes

We define `lucasLehmerResidue : Π p : ℕ, ZMod (2^p - 1)`, and
prove `lucasLehmerResidue p = 0 ↔ Prime (mersenne p)`.

We construct a `norm_num` extension to calculate this residue to certify primality of Mersenne
primes using `lucas_lehmer_sufficiency`.


## TODO

- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Kim Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
This tactic was ported by Thomas Murrills to Lean 4, and then it was converted to a `norm_num`
extension and made to use kernel reductions by Kyle Miller.
-/

def mersenne (p : ℕ) : ℕ :=
  2 ^ p - 1

theorem strictMono_mersenne : StrictMono mersenne := fun m n h ↦
  (Nat.sub_lt_sub_iff_right <| Nat.one_le_pow _ _ two_pos).2 <| by gcongr; norm_num1
