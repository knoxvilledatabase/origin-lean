/-
Extracted from RingTheory/Teichmuller.lean
Genuine: 13 of 14 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Teichmüller map

Let `R` be an `I`-adically complete ring, and `p` be a prime number with `p ∈ I`.

Then there is a canonical map `Perfection (R ⧸ I) p →*₀ R` that we shall call
`Perfection.teichmuller`, such that it composed with the quotient map `R →+* R ⧸ I` is the
"0-th coefficient" map `Perfection (R ⧸ I) p →+* R ⧸ I`.

-/

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {I : Ideal R} [CharP (R ⧸ I) p]

namespace Perfection

noncomputable def teichmullerAux (x : Perfection (R ⧸ I) p) : ℕ → R
  | 0 => 1
  | n + 1 => (coeff _ p n x).out ^ p ^ n

theorem teichmullerAux_sModEq (x : Perfection (R ⧸ I) p) (m : ℕ) :
    teichmullerAux x m ≡ teichmullerAux x (m + 1) [SMOD I ^ m] := by
  obtain _ | m := m
  · simp
  symm
  rw [teichmullerAux, pow_succ' p, pow_mul]
  exact .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := m) <| by
    simp [SModEq.idealQuotientMk, coeff_pow_p']

noncomputable def teichmullerCauchy (x : Perfection (R ⧸ I) p) :
    AdicCompletion.AdicCauchySequence I R :=
  .mk _ _ (teichmullerAux x) <| by simpa using teichmullerAux_sModEq x

section IsPrecomplete

variable [IsPrecomplete I R]

theorem exists_teichmullerFun (x : Perfection (R ⧸ I) p) :
    ∃ y : R, ∀ n, teichmullerAux x n ≡ y [SMOD I ^ n • (⊤ : Ideal R)] :=
  IsPrecomplete.prec' _ (teichmullerCauchy x).2

noncomputable def teichmullerFun (x : Perfection (R ⧸ I) p) : R :=
  (exists_teichmullerFun x).choose

theorem teichmullerFun_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmullerFun x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] := by
  have := (exists_teichmullerFun x).choose_spec (n + 1)
  rw [smul_eq_mul, Ideal.mul_top] at this
  exact this.symm.trans <| .pow_pow_add_one (I.natCast_mem_of_charP_quotient p) (m := n) <| by
    simp [SModEq.idealQuotientMk, h]

end IsPrecomplete

variable [IsAdicComplete I R]

theorem teichmullerFun_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmullerFun x = y :=
  teichmullerFun_spec' ⟨0, fun n _ ↦ h n⟩

variable (p I) in

noncomputable def teichmuller : Perfection (R ⧸ I) p →* R where
  toFun := teichmullerFun
  map_one' := teichmullerFun_spec fun _ ↦ ⟨1, by simp⟩
  map_mul' x y := by
    refine teichmullerFun_spec fun n ↦ ?_
    refine ⟨(coeff _ p n x).out * (coeff _ p n y).out, by simp, ?_⟩
    rw [mul_pow]
    refine (teichmullerFun_sModEq ?_).symm.mul (teichmullerFun_sModEq ?_).symm <;> simp

theorem teichmuller_sModEq {x : Perfection (R ⧸ I) p} {y : R} {n : ℕ}
    (h : Ideal.Quotient.mk I y = coeff _ p n x) :
    teichmuller p I x ≡ y ^ p ^ n [SMOD I ^ (n + 1)] :=
  teichmullerFun_sModEq h

theorem teichmuller_spec' {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∃ N, ∀ n ≥ N, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧
      z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec' h

theorem teichmuller_spec {x : Perfection (R ⧸ I) p} {y : R}
    (h : ∀ n, ∃ z, Ideal.Quotient.mk I z = coeff _ p n x ∧ z ^ p ^ n ≡ y [SMOD I ^ (n + 1)]) :
    teichmuller p I x = y :=
  teichmullerFun_spec h

theorem teichmuller_zero : teichmuller p I 0 = 0 :=
  have : p ≠ 0 := Nat.Prime.ne_zero Fact.out
  teichmuller_spec fun n ↦ ⟨0, by simp [zero_pow (pow_ne_zero n this)]⟩

variable (p I) in

noncomputable def teichmuller₀ : Perfection (R ⧸ I) p →*₀ R where
  __ := teichmuller p I
  map_zero' := teichmuller_zero
