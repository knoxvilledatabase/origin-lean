/-
Extracted from RingTheory/Frobenius.lean
Genuine: 11 of 12 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Frobenius elements

In algebraic number theory, if `L/K` is a finite Galois extension of number fields, with rings of
integers `𝓞L/𝓞K`, and if `q` is prime ideal of `𝓞L` lying over a prime ideal `p` of `𝓞K`, then
there exists a **Frobenius element** `Frob p` in `Gal(L/K)` with the property that
`Frob p x ≡ x ^ #(𝓞K/p) (mod q)` for all `x ∈ 𝓞L`.

Following `Mathlib/RingTheory/Invariant/Basic.lean`, we develop the theory in the setting that
there is a finite group `G` acting on a ring `S`, and `R` is the fixed subring of `S`.

## Main results

Let `S/R` be an extension of rings, `Q` be a prime of `S`,
and `P := R ∩ Q` with finite residue field of cardinality `q`.

- `AlgHom.IsArithFrobAt`: We say that a `φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q`
  if `φ x ≡ x ^ q (mod Q)` for all `x : S`.
- `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`:
  Suppose `S` is a domain and `φ` is a Frobenius at `Q`,
  then `φ ζ = ζ ^ q` for any `m`-th root of unity `ζ` with `q ∤ m`.
- `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`:
  Suppose `S` is Noetherian, `Q` contains all zero-divisors, and the extension is unramified at `Q`.
  Then the Frobenius is unique (if exists).

Let `G` be a finite group acting on a ring `S`, and `R` is the fixed subring of `S`.

- `IsArithFrobAt`: We say that a `σ : G` is an (arithmetic) Frobenius at `Q`
  if `σ • x ≡ x ^ q (mod Q)` for all `x : S`.
- `IsArithFrobAt.mul_inv_mem_inertia`:
  Two Frobenius elements at `Q` differ by an element in the inertia subgroup of `Q`.
- `IsArithFrobAt.conj`: If `σ` is a Frobenius at `Q`, then `τστ⁻¹` is a Frobenius at `σ • Q`.
- `IsArithFrobAt.exists_of_isInvariant`: Frobenius element exists.
-/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def AlgHom.IsArithFrobAt (φ : S →ₐ[R] S) (Q : Ideal S) : Prop :=
  ∀ x, φ x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q

namespace AlgHom.IsArithFrobAt

variable {φ ψ : S →ₐ[R] S} {Q : Ideal S} (H : φ.IsArithFrobAt Q)

include H

lemma mk_apply (x) : Ideal.Quotient.mk Q (φ x) = x ^ Nat.card (R ⧸ Q.under R) := by
  rw [← map_pow, Ideal.Quotient.eq]
  exact H x

lemma finite_quotient : _root_.Finite (R ⧸ Q.under R) := by
  by_contra! h
  obtain rfl : Q = ⊤ := by simpa [Nat.card_eq_zero_of_infinite, ← Ideal.eq_top_iff_one] using H 0
  simp only [Ideal.comap_top] at h
  exact not_finite (R ⧸ (⊤ : Ideal R))

lemma card_pos : 0 < Nat.card (R ⧸ Q.under R) :=
  have := H.finite_quotient
  Nat.card_pos

lemma le_comap : Q ≤ Q.comap φ := by
  intro x hx
  simp_all only [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem (I := Q), H.mk_apply,
    zero_pow_eq, ite_eq_right_iff, H.card_pos.ne', false_implies]

def restrict : S ⧸ Q →ₐ[R ⧸ Q.under R] S ⧸ Q where
  toRingHom := Ideal.quotientMap Q φ H.le_comap
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_arg (Ideal.Quotient.mk Q) (φ.commutes x)

lemma restrict_apply (x : S ⧸ Q) :
    H.restrict x = x ^ Nat.card (R ⧸ Q.under R) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact H.mk_apply x

lemma restrict_injective [Q.IsPrime] :
    Function.Injective H.restrict := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  simpa [restrict_apply, H.card_pos.ne'] using hx

lemma comap_eq [Q.IsPrime] : Q.comap φ = Q := by
  refine le_antisymm (fun x hx ↦ ?_) H.le_comap
  rwa [← Ideal.Quotient.eq_zero_iff_mem, ← H.restrict_injective.eq_iff, map_zero, restrict_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]

lemma apply_of_pow_eq_one [IsDomain S] {ζ : S} {m : ℕ} (hζ : ζ ^ m = 1) (hk' : ↑m ∉ Q) :
    φ ζ = ζ ^ Nat.card (R ⧸ Q.under R) := by
  set q := Nat.card (R ⧸ Q.under R)
  have hm : m ≠ 0 := by rintro rfl; exact hk' (by simp)
  obtain ⟨k, hk, hζ⟩ := IsPrimitiveRoot.exists_pos hζ hm
  have hk' : ↑k ∉ Q := fun h ↦ hk' (Q.mem_of_dvd (Nat.cast_dvd_cast (hζ.2 m ‹_›)) h)
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one (ξ := φ ζ) (by rw [← map_pow, hζ.1, map_one])
  have (j : _) : 1 - ζ ^ ((q + k - i) * j) ∈ Q := by
    rw [← Ideal.mul_unit_mem_iff_mem _ ((hζ.isUnit NeZero.out).pow (i * j)),
      sub_mul, one_mul, ← pow_add, ← add_mul, tsub_add_cancel_of_le (by linarith), add_mul,
        pow_add, pow_mul _ k, hζ.1, one_pow, mul_one, pow_mul, e, ← map_pow, mul_comm, pow_mul]
    exact H _
  have h₁ := sum_mem (t := Finset.range k) fun j _ ↦ this j
  have h₂ := geom_sum_mul (ζ ^ (q + k - i)) k
  rw [pow_right_comm, hζ.1, one_pow, sub_self, mul_eq_zero, sub_eq_zero] at h₂
  rcases h₂ with h₂ | h₂
  · simp [h₂, pow_mul, hk'] at h₁
  replace h₂ := congr($h₂ * ζ ^ i)
  rw [one_mul, ← pow_add, tsub_add_cancel_of_le (by linarith), pow_add, hζ.1, mul_one] at h₂
  rw [h₂, e]

noncomputable

def localize [Q.IsPrime] : Localization.AtPrime Q →ₐ[R] Localization.AtPrime Q where
  toRingHom := Localization.localRingHom _ _ φ H.comap_eq.symm
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      Localization.localRingHom_to_map]
