/-
Extracted from RingTheory/RingHom/Surjective.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# The meta properties of surjective ring homomorphisms.

## Main results

Let `R` be a commutative ring, `M` be a submonoid of `R`.

* `surjective_localizationPreserves` :  `M⁻¹R →+* M⁻¹S` is surjective if `R →+* S` is surjective.
* `surjective_ofLocalizationSpan` : `R →+* S` is surjective if there exists a set `{ r }` that
  spans `R` such that `Rᵣ →+* Sᵣ` is surjective.
* `surjective_localRingHom_of_surjective` : A surjective ring homomorphism `R →+* S` induces a
  surjective homomorphism `R_{f⁻¹(P)} →+* S_P` for every prime ideal `P` of `S`.

-/

namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

universe u

local notation "surjective" => fun {X Y : Type _} [CommRing X] [CommRing Y] => fun f : X →+* Y =>

  Function.Surjective f

theorem surjective_stableUnderComposition : StableUnderComposition surjective := by
  introv R hf hg; exact hg.comp hf

theorem surjective_respectsIso : RespectsIso surjective := by
  apply surjective_stableUnderComposition.respectsIso
  intro _ _ _ _ e
  exact e.surjective

theorem surjective_localizationPreserves :
    LocalizationPreserves surjective := by
  introv R H x
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (M.map f) x
  obtain ⟨y, rfl⟩ := H x
  use IsLocalization.mk' R' y ⟨s, hs⟩
  rw [IsLocalization.map_mk']

theorem surjective_ofLocalizationSpan : OfLocalizationSpan surjective := by
  introv R e H
  rw [← Set.range_eq_univ, Set.eq_univ_iff_forall]
  letI := f.toAlgebra
  intro x
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (LinearMap.range (Algebra.linearMap R S)) s e
  intro r
  obtain ⟨a, e'⟩ := H r (algebraMap _ _ x)
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (r : R)) a
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk', eq_comm,
    IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, Subtype.coe_mk, ← map_mul] at e'
  obtain ⟨⟨_, n', rfl⟩, e''⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f r)) _).mp e'
  dsimp only at e''
  rw [mul_comm x, ← mul_assoc, ← map_pow, ← map_mul, ← map_mul, ← pow_add] at e''
  exact ⟨n' + n, _, e''.symm⟩

theorem surjective_localRingHom_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : Function.Surjective f) (P : Ideal S) [P.IsPrime] :
    Function.Surjective (Localization.localRingHom (P.comap f) P f rfl) :=
  have : IsLocalization (Submonoid.map f (Ideal.comap f P).primeCompl) (Localization.AtPrime P) :=
    (Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization
  surjective_localizationPreserves _ _ _ _ h

end RingHom
