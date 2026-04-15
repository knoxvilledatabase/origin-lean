/-
Extracted from GroupTheory/PGroup.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

open Fintype MulAction

variable (p : ℕ) (G : Type*) [Group G]

def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

variable {p} {G}

namespace IsPGroup

theorem iff_orderOf [hp : Fact p.Prime] : IsPGroup p G ↔ ∀ g : G, ∃ k : ℕ, orderOf g = p ^ k :=
  forall_congr' fun g =>
    ⟨fun ⟨_, hk⟩ =>
      Exists.imp (fun _ h => h.right)
        ((Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hk)),
      Exists.imp fun k hk => by rw [← hk, pow_orderOf_eq_one]⟩

theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G := fun g =>
  ⟨n, by rw [← hG, pow_card_eq_one']⟩

theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])

theorem iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n := by
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => of_card hn⟩
  suffices ∀ q ∈ (Nat.card G).primeFactorsList, q = p by
    use (Nat.card G).primeFactorsList.length
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem this, Nat.prod_primeFactorsList hG]
  intro q hq
  obtain ⟨hq1, hq2⟩ := (Nat.mem_primeFactorsList hG).mp hq
  haveI : Fact q.Prime := ⟨hq1⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hq2
  obtain ⟨k, hk⟩ := (iff_orderOf.mp h) g
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm

alias ⟨exists_card_eq, _⟩ := iff_card

section GIsPGroup

variable (hG : IsPGroup p G)

include hG

theorem of_injective {H : Type*} [Group H] (ϕ : H →* G) (hϕ : Function.Injective ϕ) :
    IsPGroup p H := by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)

theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.of_injective H.subtype Subtype.coe_injective

theorem of_surjective {H : Type*} [Group H] (ϕ : G →* H) (hϕ : Function.Surjective ϕ) :
    IsPGroup p H := by
  refine fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => ?_) (hG g)
  rw [← hg, ← ϕ.map_pow, hk, ϕ.map_one]

theorem to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H) :=
  hG.of_surjective (QuotientGroup.mk' H) Quotient.mk''_surjective

theorem of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.of_surjective ϕ.toMonoidHom ϕ.surjective

theorem orderOf_coprime {n : ℕ} (hn : p.Coprime n) (g : G) : (orderOf g).Coprime n :=
  let ⟨k, hk⟩ := hG g
  (hn.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)

noncomputable def powEquiv {n : ℕ} (hn : p.Coprime n) : G ≃ G :=
  let h : ∀ g : G, (Nat.card (Subgroup.zpowers g)).Coprime n := fun g =>
    (Nat.card_zpowers g).symm ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
      Subtype.ext_iff.1 <|
        (powCoprime (h (g ^ n))).left_inv
          ⟨g, _, Subtype.ext_iff.1 <| (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
      Subtype.ext_iff.1 <| (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }
