/-
Extracted from FieldTheory/Finite/Extension.lean
Genuine: 8 of 12 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Extensions of finite fields

In this file we develop the theory of extensions of finite fields.

If `k` is a finite field (of cardinality `q = p ^ m`), then there is a unique (up to in general
non-unique isomorphism) extension `l` of `k` of any given degree `n > 0`.

This extension is Galois with cyclic Galois group of degree `n`, and the (arithmetic) Frobenius map
`x ↦ x ^ q` is a generator.


## Main definition

* `FiniteField.Extension k p n` is a non-canonically chosen extension of `k` of degree `n`
  (for `n > 0`).

## Main Results

* `FiniteField.algEquivExtension`: any other field extension `l/k` of degree `n` is (non-uniquely)
isomorphic to our chosen `FiniteField.Extension k p n`.

-/

noncomputable section

variable (k : Type*) [Field k] [Finite k]

variable (p : ℕ) [Fact p.Prime] [CharP k p]

variable (n : ℕ) [NeZero n]

open Polynomial

namespace FiniteField

def Extension [CharP k p] : Type :=
  letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

theorem finrank_zmod_extension [Algebra (ZMod p) k] :
    Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n := by
  letI := ZMod.algebra k p
  convert GaloisField.finrank p (n := Module.finrank (ZMod p) k * n) <|
    mul_ne_zero Module.finrank_pos.ne' <| NeZero.ne n using 4
  subsingleton

theorem nonempty_algHom_extension [Algebra (ZMod p) k] :
    Nonempty (k →ₐ[ZMod p] Extension k p n) :=
  nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Algebra

theorem natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n := by
  letI := ZMod.algebra k p
  rw [← pow_finrank_eq_natCard p, ← pow_finrank_eq_natCard p, finrank_zmod_extension, pow_mul]

theorem finrank_extension : Module.finrank k (Extension k p n) = n := by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card k) ?_
  simp only [← Module.natCard_eq_pow_finrank, natCard_extension]

-- INSTANCE (free from Core): :

example : IsGalois k (Extension k p n) :=

  inferInstance

example : IsCyclic Gal(Extension k p n / k) :=

  inferInstance

theorem natCard_algEquiv_extension : Nat.card Gal(Extension k p n / k) = n :=
  (IsGalois.card_aut_eq_finrank _ _).trans <| finrank_extension k p n

theorem card_algEquiv_extension : Fintype.card Gal(Extension k p n / k) = n :=
  Fintype.card_eq_nat_card.trans <| natCard_algEquiv_extension k p n

noncomputable def Extension.frob :
    Gal(Extension k p n / k) :=
  haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _
