/-
Extracted from RingTheory/UniqueFactorizationDomain/Finite.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

noncomputable section

/-!
# Finiteness of divisors

## Main results
* `UniqueFactorizationMonoid.fintypeSubtypeDvd`: elements of a UFM with finitely many units have
  finitely many divisors.
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

noncomputable def fintypeSubtypeDvd {M : Type*} [CancelCommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Fintype Mˣ] (y : M) (hy : y ≠ 0) : Fintype { x // x ∣ y } := by
  haveI : Nontrivial M := ⟨⟨y, 0, hy⟩⟩
  haveI : NormalizationMonoid M := UniqueFactorizationMonoid.normalizationMonoid
  haveI := Classical.decEq M
  haveI := Classical.decEq (Associates M)
  -- We'll show `fun (u : Mˣ) (f ⊆ factors y) ↦ u * Π f` is injective
  -- and has image exactly the divisors of `y`.
  refine
    Fintype.ofFinset
      (((normalizedFactors y).powerset.toFinset ×ˢ (Finset.univ : Finset Mˣ)).image fun s =>
        (s.snd : M) * s.fst.prod)
      fun x => ?_
  simp only [exists_prop, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true,
    Multiset.mem_toFinset, Multiset.mem_powerset, exists_eq_right, Multiset.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    show (s.snd : M) * s.fst.prod ∣ y
    rw [(unit_associated_one.mul_right s.fst.prod).dvd_iff_dvd_left, one_mul,
      ← (normalizedFactors_prod hy).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hs
  · rintro (h : x ∣ y)
    have hx : x ≠ 0 := by
      refine mt (fun hx => ?_) hy
      rwa [hx, zero_dvd_iff] at h
    obtain ⟨u, hu⟩ := normalizedFactors_prod hx
    refine ⟨⟨normalizedFactors x, u⟩, ?_, (mul_comm _ _).trans hu⟩
    exact (dvd_iff_normalizedFactors_le_normalizedFactors hx hy).mp h

end UniqueFactorizationMonoid
