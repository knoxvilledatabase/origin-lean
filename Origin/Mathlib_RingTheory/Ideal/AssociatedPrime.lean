/-
Extracted from RingTheory/Ideal/AssociatedPrime.lean
Genuine: 9 of 16 | Dissolved: 2 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!

# Associated primes of a module

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `IsAssociatedPrime`: `IsAssociatedPrime I M` if the prime ideal `I` is the
  annihilator of some `x : M`.
- `associatedPrimes`: The set of associated primes of a module.

## Main results
- `exists_le_isAssociatedPrime_of_isNoetherianRing`: In a noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associatedPrimes.eq_singleton_of_isPrimary`: In a noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## TODO

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

-/

variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

def IsAssociatedPrime : Prop :=
  I.IsPrime ∧ ∃ x : M, I = (R ∙ x).annihilator

variable (R)

def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }

variable {I J M R}

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')

theorem AssociatePrimes.mem_iff : I ∈ associatedPrimes R M ↔ IsAssociatedPrime I M := Iff.rfl

theorem IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime := h.1

theorem IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Function.Injective f) :
    IsAssociatedPrime I M' := by
  obtain ⟨x, rfl⟩ := h.2
  refine ⟨h.1, ⟨f x, ?_⟩⟩
  ext r
  rw [Submodule.mem_annihilator_span_singleton, Submodule.mem_annihilator_span_singleton, ←
    map_smul, ← f.map_zero, hf.eq_iff]

theorem LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') :
    IsAssociatedPrime I M ↔ IsAssociatedPrime I M' :=
  ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩

theorem not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrime I M := by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  rwa [Subsingleton.elim x 0, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.annihilator_bot]
    at hx

variable (R)

-- DISSOLVED: exists_le_isAssociatedPrime_of_isNoetherianRing

variable {R}

theorem associatedPrimes.subset_of_injective (hf : Function.Injective f) :
    associatedPrimes R M ⊆ associatedPrimes R M' := fun _I h => h.map_of_injective f hf

theorem LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') :
    associatedPrimes R M = associatedPrimes R M' :=
  le_antisymm (associatedPrimes.subset_of_injective l l.injective)
    (associatedPrimes.subset_of_injective l.symm l.symm.injective)

theorem associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPrimes R M = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]
  apply not_isAssociatedPrime_of_subsingleton

variable (R M)

theorem associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] :
    (associatedPrimes R M).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩

-- DISSOLVED: biUnion_associatedPrimes_eq_zero_divisors

variable {R M}

theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator ≤ I := by
  obtain ⟨hI, x, rfl⟩ := h
  exact Submodule.annihilator_mono le_top

theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  have : x ≠ 0 := by
    rintro rfl
    apply hJ.1
    rwa [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.annihilator_bot] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  replace e : ∀ {y}, y ∈ J ↔ x * y ∈ I := by
    intro y
    rw [e, Submodule.mem_annihilator_span_singleton, ← map_smul, smul_eq_mul, mul_comm,
      Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_eq_zero]
  apply le_antisymm
  · intro y hy
    exact ((Ideal.isPrimary_iff.1 hI).2 <| e.mp hy).resolve_left
      ((Submodule.Quotient.mk_eq_zero I).not.mp this)
  · rw [hJ.radical_le_iff]
    intro y hy
    exact e.mpr (I.mul_mem_left x hy)

theorem associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) :
    associatedPrimes R (R ⧸ I) = {I.radical} := by
  ext J
  rw [Set.mem_singleton_iff]
  refine ⟨IsAssociatedPrime.eq_radical hI, ?_⟩
  rintro rfl
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I : _) 1, (Ideal.Quotient.mk I : _) 0, ?_⟩
    rw [Ne, Ideal.Quotient.eq, sub_zero, ← Ideal.eq_top_iff_one]
    exact hI.1
  obtain ⟨a, ha⟩ := associatedPrimes.nonempty R (R ⧸ I)
  exact ha.eq_radical hI ▸ ha
