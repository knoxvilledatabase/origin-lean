/-
Extracted from RingTheory/RingHom/Locally.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Target local closure of ring homomorphism properties

If `P` is a property of ring homomorphisms, we call `Locally P` the closure of `P` with
respect to standard open coverings on the (algebraic) target (i.e. geometric source). Hence
for `f : R →+* S`, the property `Locally P` holds if it holds locally on `S`, i.e. if there exists
a subset `{ t }` of `S` generating the unit ideal, such that `P` holds for all compositions
`R →+* Sₜ`.

Assuming without further mention that `P` is stable under composition with isomorphisms,
`Locally P` is local on the target by construction, i.e. it satisfies
`RingHom.OfLocalizationSpanTarget`. If `P` itself is local on the target,
`Locally P` coincides with `P`.

The `Locally` construction preserves various properties of `P`, e.g. if `P` is stable under
composition, base change, etc., so is `Locally P`.

## Main results

- `RingHom.locally_ofLocalizationSpanTarget`: `Locally P` is local on the target.
- `RingHom.locally_holdsForLocalizationAway`: `Locally P` holds for localization away maps
  if `P` does.
- `RingHom.locally_isStableUnderBaseChange`: `Locally P` is stable under base change if `P` is.
- `RingHom.locally_stableUnderComposition`: `Locally P` is stable under composition
  if `P` is and `P` is preserved under localizations.
- `RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget` and
  `RingHom.locally_stableUnderCompositionWithLocalizationAwaySource`: `Locally P` is stable under
  composition with localization away maps if `P` is.
- `RingHom.locally_localizationPreserves`: If `P` is preserved by localizations, then so is
  `Locally P`.

-/

universe u v

open TensorProduct

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

def Locally {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∃ (s : Set S) (_ : Ideal.span s = ⊤),
    ∀ t ∈ s, P ((algebraMap S (Localization.Away t)).comp f)

variable {R S : Type u} [CommRing R] [CommRing S]

lemma locally_iff_finite (f : R →+* S) :
    Locally P f ↔ ∃ (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      ∀ t ∈ s, P ((algebraMap S (Localization.Away t)).comp f) := by
  constructor
  · intro ⟨s, hsone, hs⟩
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hsone
    exact ⟨s', h₂, fun t ht ↦ hs t (h₁ ht)⟩
  · intro ⟨s, hsone, hs⟩
    use s, hsone, hs

variable {P}

lemma locally_of_exists (hP : RespectsIso P) (f : R →+* S) {ι : Type*} (s : ι → S)
    (hsone : Ideal.span (Set.range s) = ⊤)
    (Sₜ : ι → Type u) [∀ i, CommRing (Sₜ i)] [∀ i, Algebra S (Sₜ i)]
    [∀ i, IsLocalization.Away (s i) (Sₜ i)] (hf : ∀ i, P ((algebraMap S (Sₜ i)).comp f)) :
    Locally P f := by
  use Set.range s, hsone
  rintro - ⟨i, rfl⟩
  let e : Localization.Away (s i) ≃+* Sₜ i :=
    (IsLocalization.algEquiv (Submonoid.powers (s i)) _ _).toRingEquiv
  have : algebraMap S (Localization.Away (s i)) = e.symm.toRingHom.comp (algebraMap S (Sₜ i)) :=
    RingHom.ext (fun x ↦ (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _).symm _).symm)
  rw [this, RingHom.comp_assoc]
  exact hP.left _ _ (hf i)

lemma locally_iff_exists (hP : RespectsIso P) (f : R →+* S) :
    Locally P f ↔ ∃ (ι : Type u) (s : ι → S) (_ : Ideal.span (Set.range s) = ⊤) (Sₜ : ι → Type u)
      (_ : (i : ι) → CommRing (Sₜ i)) (_ : (i : ι) → Algebra S (Sₜ i))
      (_ : (i : ι) → IsLocalization.Away (s i : S) (Sₜ i)),
      ∀ i, P ((algebraMap S (Sₜ i)).comp f) :=
  ⟨fun ⟨s, hsone, hs⟩ ↦ ⟨s, fun t : s ↦ (t : S), by simpa, fun t ↦ Localization.Away (t : S),
      inferInstance, inferInstance, inferInstance, fun t ↦ hs t.val t.property⟩,
    fun ⟨ι, s, hsone, Sₜ, _, _, hislocal, hs⟩ ↦ locally_of_exists hP f s hsone Sₜ hs⟩

lemma locally_iff_isLocalization (hP : RespectsIso P) (f : R →+* S) :
    Locally P f ↔ ∃ (s : Finset S) (_ : Ideal.span (s : Set S) = ⊤),
      ∀ t ∈ s, ∀ (Sₜ : Type u) [CommRing Sₜ] [Algebra S Sₜ] [IsLocalization.Away t Sₜ],
      P ((algebraMap S Sₜ).comp f) := by
  rw [locally_iff_finite P f]
  refine ⟨fun ⟨s, hsone, hs⟩ ↦ ⟨s, hsone, fun t ht Sₜ _ _ _ ↦ ?_⟩, fun ⟨s, hsone, hs⟩ ↦ ?_⟩
  · let e : Localization.Away t ≃+* Sₜ :=
      (IsLocalization.algEquiv (Submonoid.powers t) _ _).toRingEquiv
    have : algebraMap S Sₜ = e.toRingHom.comp (algebraMap S (Localization.Away t)) :=
      RingHom.ext (fun x ↦ (AlgEquiv.commutes (IsLocalization.algEquiv _ _ _) _).symm)
    rw [this, RingHom.comp_assoc]
    exact hP.left _ _ (hs t ht)
  · exact ⟨s, hsone, fun t ht ↦ hs t ht _⟩

lemma locally_of (hP : RespectsIso P) (f : R →+* S) (hf : P f) : Locally P f := by
  use {1}
  let e : S ≃+* Localization.Away (1 : S) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).toRingEquiv
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  exact hP.left f e hf

lemma locally_of_locally {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hPQ : ∀ {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}, P f → Q f)
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S} (hf : Locally P f) : Locally Q f := by
  obtain ⟨s, hsone, hs⟩ := hf
  exact ⟨s, hsone, fun t ht ↦ hPQ (hs t ht)⟩

lemma locally_iff_of_localizationSpanTarget (hPi : RespectsIso P)
    (hPs : OfLocalizationSpanTarget P) {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Locally P f ↔ P f :=
  ⟨fun ⟨s, hsone, hs⟩ ↦ hPs f s hsone (fun a ↦ hs a.val a.property), locally_of hPi f⟩

section OfLocalizationSpanTarget

lemma locally_ofLocalizationSpanTarget (hP : RespectsIso P) :
    OfLocalizationSpanTarget (Locally P) := by
  intro R S _ _ f s hsone hs
  choose t htone ht using hs
  rw [locally_iff_exists hP]
  refine ⟨(a : s) × t a, IsLocalization.Away.mulNumerator s t,
      IsLocalization.Away.span_range_mulNumerator_eq_top hsone htone,
      fun ⟨a, b⟩ ↦ Localization.Away b.val, inferInstance, inferInstance, fun ⟨a, b⟩ ↦ ?_, ?_⟩
  · haveI : IsLocalization.Away ((algebraMap S (Localization.Away a.val))
        (IsLocalization.Away.sec a.val b.val).1) (Localization.Away b.val) := by
      apply IsLocalization.Away.of_associated (r := b.val)
      rw [← IsLocalization.Away.sec_spec]
      apply associated_mul_unit_right
      rw [map_pow _ _]
      exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
    apply IsLocalization.Away.mul' (Localization.Away a.val) (Localization.Away b.val)
  · intro ⟨a, b⟩
    rw [IsScalarTower.algebraMap_eq S (Localization.Away a.val) (Localization.Away b.val)]
    apply ht _ _ b.property

end OfLocalizationSpanTarget

section Stability

lemma locally_respectsIso (hPi : RespectsIso P) : RespectsIso (Locally P) where
  left {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ ↦ by
    refine ⟨e '' s, ?_, ?_⟩
    · rw [← Ideal.map_span, hsone, Ideal.map_top]
    · rintro - ⟨a, ha, rfl⟩
      let e' : Localization.Away a ≃+* Localization.Away (e a) :=
        IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e a)
      have : (algebraMap T (Localization.Away (e a))).comp e.toRingHom =
          e'.toRingHom.comp (algebraMap S (Localization.Away a)) := by
        ext x
        simp [e']
      rw [← RingHom.comp_assoc, this, RingHom.comp_assoc]
      apply hPi.left
      exact hs a ha
  right {R S T} _ _ _ f e := fun ⟨s, hsone, hs⟩ ↦
    ⟨s, hsone, fun a ha ↦ (RingHom.comp_assoc _ _ _).symm ▸ hPi.right _ _ (hs a ha)⟩

lemma locally_holdsForLocalizationAway (hPa : HoldsForLocalizationAway P) :
    HoldsForLocalizationAway (Locally P) := by
  introv R _
  use {1}
  simp only [Set.mem_singleton_iff, forall_eq, Ideal.span_singleton_one, exists_const]
  let e : S ≃ₐ[R] (Localization.Away (1 : S)) :=
    (IsLocalization.atUnits S (Submonoid.powers 1) (by simp)).restrictScalars R
  haveI : IsLocalization.Away r (Localization.Away (1 : S)) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) e
  rw [← IsScalarTower.algebraMap_eq]
  apply hPa _ r

lemma locally_stableUnderComposition (hPi : RespectsIso P) (hPl : LocalizationPreserves P)
    (hPc : StableUnderComposition P) :
    StableUnderComposition (Locally P) := by
  classical
  intro R S T _ _ _ f g hf hg
  rw [locally_iff_finite] at hf hg
  obtain ⟨sf, hsfone, hsf⟩ := hf
  obtain ⟨sg, hsgone, hsg⟩ := hg
  rw [locally_iff_exists hPi]
  refine ⟨sf × sg, fun (a, b) ↦ g a * b, ?_,
      fun (a, b) ↦ Localization.Away ((algebraMap T (Localization.Away b.val)) (g a.val)),
      inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [eq_top_iff, ← hsgone, Ideal.span_le]
    intro t ht
    have : 1 ∈ Ideal.span (Set.range <| fun a : sf ↦ a.val) := by simp [hsfone]
    simp only [Ideal.mem_span_range_iff_exists_fun, SetLike.mem_coe] at this ⊢
    obtain ⟨cf, hcf⟩ := this
    let cg : sg → T := Pi.single ⟨t, ht⟩ 1
    use fun (a, b) ↦ g (cf a) * cg b
    simp [cg, Pi.single_apply, Fintype.sum_prod_type, ← mul_assoc, ← Finset.sum_mul, ← map_mul,
      ← map_sum, hcf] at hcf ⊢
  · intro ⟨a, b⟩
    let g' := (algebraMap T (Localization.Away b.val)).comp g
    let a' := (algebraMap T (Localization.Away b.val)) (g a.val)
    have : (algebraMap T <| Localization.Away a').comp (g.comp f) =
        (Localization.awayMap g' a.val).comp ((algebraMap S (Localization.Away a.val)).comp f) := by
      ext x
      simp only [coe_comp, Function.comp_apply, a']
      change _ = Localization.awayMap g' a.val (algebraMap S _ (f x))
      simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
      rfl
    simp only [this, a']
    apply hPc _ _ (hsf a.val a.property)
    apply @hPl _ _ _ _ g' _ _ _ _ _ _ _ _ ?_ (hsg b.val b.property)
    exact IsLocalization.Away.instMapRingHomPowersOfCoe (Localization.Away (g' a.val)) a.val

lemma locally_stableUnderCompositionWithLocalizationAwayTarget
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) :
    StableUnderCompositionWithLocalizationAwayTarget (Locally P) := by
  intro R S T _ _ _ _ t _ f hf
  obtain ⟨s, hsone, hs⟩ := hf
  refine ⟨algebraMap S T '' s, ?_, ?_⟩
  · rw [← Ideal.map_span, hsone, Ideal.map_top]
  · rintro - ⟨a, ha, rfl⟩
    letI : Algebra (Localization.Away a) (Localization.Away (algebraMap S T a)) :=
      (IsLocalization.Away.map _ _ (algebraMap S T) a).toAlgebra
    have : (algebraMap (Localization.Away a) (Localization.Away (algebraMap S T a))).comp
        (algebraMap S (Localization.Away a)) =
        (algebraMap T (Localization.Away (algebraMap S T a))).comp (algebraMap S T) := by
      simp [algebraMap_toAlgebra, IsLocalization.Away.map]
    rw [← comp_assoc, ← this, comp_assoc]
    haveI : IsScalarTower S (Localization.Away a) (Localization.Away ((algebraMap S T) a)) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      simp [algebraMap_toAlgebra, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply]
    haveI : IsLocalization.Away (algebraMap S (Localization.Away a) t)
        (Localization.Away (algebraMap S T a)) :=
      IsLocalization.Away.commutes _ T ((Localization.Away (algebraMap S T a))) a t
    apply hPa _ (algebraMap S (Localization.Away a) t)
    apply hs a ha
