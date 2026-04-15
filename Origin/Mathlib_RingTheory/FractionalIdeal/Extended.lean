/-
Extracted from RingTheory/FractionalIdeal/Extended.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extension of fractional ideals

This file defines the extension of a fractional ideal along a ring homomorphism.

## Main definitions

* `FractionalIdeal.extended`: Let `A` and `B` be commutative rings with respective localizations
  `IsLocalization M K` and `IsLocalization N L`. Let `f : A →+* B` be a ring homomorphism with
  `hf : M ≤ Submonoid.comap f N`. If `I : FractionalIdeal M K`, then the extension of `I` along
  `f` is `extended L hf I : FractionalIdeal N L`.
* `FractionalIdeal.extendedHom`: The ring homomorphism version of `FractionalIdeal.extended`.
* `FractionalIdeal.extendedHomₐ`: For `A ⊆ B` an extension of domains, the ring homomorphism that
  sends a fractional ideal of `A` to a fractional ideal of `B`.

## Main results

* `FractionalIdeal.extendedHomₐ_injective`: the map `FractionalIdeal.extendedHomₐ` is injective.
* `Ideal.map_algebraMap_injective`: For `A ⊆ B` an extension of Dedekind domains, the map that
  sends an ideal `I` of `A` to `I·B` is injective.

## Tags

fractional ideal, fractional ideals, extended, extension
-/

open IsLocalization FractionalIdeal Module Submodule

namespace FractionalIdeal

section RingHom

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {f : A →+* B}

variable {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]

variable (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]

variable (hf : M ≤ Submonoid.comap f N)

variable (I : FractionalIdeal M K) (J : FractionalIdeal M K)

def extended (I : FractionalIdeal M K) : FractionalIdeal N L where
  val := span B <| (IsLocalization.map (S := K) L f hf) '' I
  property := by
    have ⟨a, ha, frac⟩ := I.isFractional
    refine ⟨f a, hf ha, fun b hb ↦ ?_⟩
    refine span_induction (fun x hx ↦ ?_) ⟨0, by simp⟩
      (fun x y _ _ hx hy ↦ smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c _ hc ↦ ?_) hb
    · rcases hx with ⟨k, kI, rfl⟩
      obtain ⟨c, hc⟩ := frac k kI
      exact ⟨f c, by simp [← IsLocalization.map_smul, ← hc]⟩
    · rw [← smul_assoc, smul_eq_mul, mul_comm (f a), ← smul_eq_mul, smul_assoc]
      exact isInteger_smul hc

local notation "map_f" => (IsLocalization.map (S := K) L f hf)

lemma mem_extended_iff (x : L) : x ∈ I.extended L hf ↔ x ∈ span B (map_f '' I) := by
  constructor <;> { intro hx; simpa }
