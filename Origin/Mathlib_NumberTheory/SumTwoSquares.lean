/-
Extracted from NumberTheory/SumTwoSquares.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sums of two squares

Fermat's theorem on the sum of two squares. Every prime `p` congruent to 1 mod 4 is the
sum of two squares; see `Nat.Prime.sq_add_sq` (which has the weaker assumption `p % 4 ≠ 3`).

We also give the result that characterizes the (positive) natural numbers that are sums
of two squares as those numbers `n` such that for every prime `q` congruent to 3 mod 4, the
exponent of the largest power of `q` dividing `n` is even; see `Nat.eq_sq_add_sq_iff`.

There is an alternative characterization as the numbers of the form `a^2 * b`, where `b` is a
natural number such that `-1` is a square modulo `b`; see `Nat.eq_sq_add_sq_iff_eq_sq_mul`.
-/

section Fermat

open GaussianInt

theorem Nat.Prime.sq_add_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  apply sq_add_sq_of_nat_prime_of_not_irreducible p
  rwa [_root_.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p]

end Fermat

/-!
### Generalities on sums of two squares
-/

section General

theorem sq_add_sq_mul {R} [CommRing R] {a b x y u v : R} (ha : a = x ^ 2 + y ^ 2)
    (hb : b = u ^ 2 + v ^ 2) : ∃ r s : R, a * b = r ^ 2 + s ^ 2 :=
  ⟨x * u - y * v, x * v + y * u, by rw [ha, hb]; ring⟩

theorem Nat.sq_add_sq_mul {a b x y u v : ℕ} (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
    ∃ r s : ℕ, a * b = r ^ 2 + s ^ 2 := by
  zify at ha hb ⊢
  obtain ⟨r, s, h⟩ := _root_.sq_add_sq_mul ha hb
  refine ⟨r.natAbs, s.natAbs, ?_⟩
  simpa only [Int.natCast_natAbs, sq_abs]

end General

/-!
### Results on when -1 is a square modulo a natural number
-/

section NegOneSquare

theorem ZMod.isSquare_neg_one_of_dvd {m n : ℕ} (hd : m ∣ n) (hs : IsSquare (-1 : ZMod n)) :
    IsSquare (-1 : ZMod m) := by
  let f : ZMod n →+* ZMod m := ZMod.castHom hd _
  rw [← map_one f, ← map_neg]
  exact hs.map f

theorem ZMod.isSquare_neg_one_mul {m n : ℕ} (hc : m.Coprime n) (hm : IsSquare (-1 : ZMod m))
    (hn : IsSquare (-1 : ZMod n)) : IsSquare (-1 : ZMod (m * n)) := by
  have : IsSquare (-1 : ZMod m × ZMod n) := by
    rw [show (-1 : ZMod m × ZMod n) = ((-1 : ZMod m), (-1 : ZMod n)) from rfl]
    obtain ⟨x, hx⟩ := hm
    obtain ⟨y, hy⟩ := hn
    rw [hx, hy]
    exact ⟨(x, y), rfl⟩
  simpa only [RingEquiv.map_neg_one] using this.map (ZMod.chineseRemainder hc).symm

theorem Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one {p n : ℕ}
    (hp : p ∈ n.primeFactors) (hs : IsSquare (-1 : ZMod n)) : p % 4 ≠ 3 := by
  obtain ⟨y, h⟩ := ZMod.isSquare_neg_one_of_dvd (Nat.dvd_of_mem_primeFactors hp) hs
  rw [← sq, eq_comm, show (-1 : ZMod p) = -1 ^ 2 by ring] at h
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' one_ne_zero h
