/-
Extracted from FieldTheory/Galois/IsGaloisGroup.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Predicate for Galois Groups

Given an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L` saying that `G` acts faithfully on `L` with fixed field `K`. In particular,
we do not assume that `L` is an algebraic extension of `K`.

## Implementation notes

We actually define `IsGaloisGroup G A B` for extensions of rings `B/A`, with the same definition
(faithful action on `B` with fixed ring `A`). This definition turns out to axiomatize a common
setup in algebraic number theory where a Galois group `Gal(L/K)` acts on an extension of subrings
`B/A` (e.g., rings of integers). In particular, there are theorems in algebraic number theory that
naturally assume `[IsGaloisGroup G A B]` and whose statements would otherwise require assuming
`(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]` (along with predicates relating
`K` and `L` to the rings `A` and `B`) despite `K` and `L` not appearing in the conclusion.

Unfortunately, this definition of `IsGaloisGroup G A B` for extensions of rings `B/A` is
nonstandard and clashes with other notions such as the étale fundamental group. In particular, if
`G` is finite and `A` is integrally closed, then  `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`
(see `IsGaloisGroup.iff_isFractionRing`), rather than `B/A` being étale for instance.

But in the absence of a more suitable name, the utility of the predicate `IsGaloisGroup G A B` for
extensions of rings `B/A` seems to outweigh these terminological issues.
-/

open Module

section CommRing

variable (G A A' B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

class IsGaloisGroup where
  faithful : FaithfulSMul G B
  commutes : SMulCommClass G A B
  isInvariant : Algebra.IsInvariant A B G

variable {G A B} in

theorem IsGaloisGroup.of_mulEquiv [hG : IsGaloisGroup G A B] {H : Type*} [Group H]
    [MulSemiringAction H B] (e : H ≃* G) (he : ∀ h (x : B), (e h) • x = h • x) :
    IsGaloisGroup H A B where
  faithful := ⟨fun h ↦ e.injective <| hG.faithful.eq_of_smul_eq_smul <| by simpa only [he]⟩
  commutes := ⟨fun x a b ↦ by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h ↦
    have he' : ∀ (g : G) (x : B), e.symm g • x = g • x := fun g x ↦ by simp [← he]
    hG.isInvariant.isInvariant b (fun g ↦ by simpa [he'] using h (e.symm g))⟩

-- INSTANCE (free from Core): low]

variable [FaithfulSMul A B] [hA : IsGaloisGroup G A B]
