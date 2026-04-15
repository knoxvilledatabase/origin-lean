/-
Extracted from AlgebraicGeometry/Geometrically/Basic.lean
Genuine: 11 of 13 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Geometrically-`P` schemes over a field

In this file we define the basic interface for properties like geometrically reduced,
geometrically irreducible, geometrically connected etc. In this file
we treat an abstract property of schemes `P` and derive the general properties that are
shared by all of these variants.

A morphism of schemes `f : X ⟶ Y` is geometrically `P` if for any field `K` and
morphism `Spec K ⟶ Y`, the base change `X ×[Y] Spec K` satisfies `P`.

## Main definitions and results

- `AlgebraicGeometry.geometrically`: The morphism property of geometrically-`P` morphisms
- `AlgebraicGeometry.geometrically_iff_forall_fiberToSpecResidueField`: `f : X ⟶ Y` is
  geometrically-`P` if and only if for every `y : Y`, the fiber `f ⁻¹ {y}` is geometrically-`P`
  over `Spec κ(y)`.

## Notes

This contribution was created as part of the Formalising Algebraic Geometry workshop 2025 in
Heidelberg.
-/

universe u

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

def geometrically (P : ObjectProperty Scheme.{u}) : MorphismProperty Scheme.{u} :=
  fun X Y f ↦ ∀ ⦃K : Type u⦄ [Field K] (y : Spec (.of K) ⟶ Y)
    ⦃Z : Scheme.{u}⦄ (fst : Z ⟶ X) (snd : Z ⟶ Spec (.of K)),
    IsPullback fst snd f y → P Z

lemma geometrically_eq_universally (P : ObjectProperty Scheme.{u}) :
    geometrically P = .universally fun X Y _ ↦ IsIntegral Y → Subsingleton Y → P X := by
  ext X Y f
  refine ⟨fun hf Z W snd q fst h _ _ ↦ ?_, fun hf aK y Z W fst snd h ↦ ?_⟩
  · let := (isField_of_isIntegral_of_subsingleton W).toField
    apply hf (W.isoSpec.inv ≫ q) snd (fst ≫ W.isoSpec.hom)
    apply h.flip.of_iso (.refl _) (.refl _) W.isoSpec (.refl _) <;> simp
  · exact hf _ _ _ h.flip inferInstance inferInstance

lemma geometrically_inf (P Q : ObjectProperty Scheme.{u}) :
    geometrically (P ⊓ Q) = geometrically P ⊓ geometrically Q := by
  simp only [geometrically_eq_universally, ← MorphismProperty.universally_inf]
  congr with X Y f
  exact ⟨fun H ↦ ⟨(H · · |>.1), (H · · |>.2)⟩, fun H a b ↦ ⟨H.1 a b, H.2 a b⟩⟩

variable (P : ObjectProperty Scheme.{u})

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [P.IsClosedUnderIsomorphisms]

section geometrically

variable {P : ObjectProperty Scheme.{u}} {X Y : Scheme.{u}} {f : X ⟶ Y}

lemma pullback_of_geometrically (hf : geometrically P f) (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ Y) : P (Limits.pullback f y) :=
  hf _ _ _ (.of_hasPullback _ _)

lemma pullback_of_geometrically' (hf : geometrically P f) (K : Type u) [Field K]
    (y : Spec (.of K) ⟶ Y) : P (Limits.pullback y f) :=
  hf _ _ _ (.flip <| .of_hasPullback _ _)

lemma geometrically_iff_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    geometrically P f ↔
      ∀ (K : Type u) [Field K] (y : Spec (.of K) ⟶ Y), P (Limits.pullback f y) := by
  refine ⟨fun h K _ _ ↦ pullback_of_geometrically h _ _, fun H K _ _ Y fst snd h ↦ ?_⟩
  exact P.prop_of_iso h.isoPullback.symm (H _ _)

lemma fiber_of_geometrically (hf : geometrically P f) (y : Y) : P (f.fiber y) :=
  pullback_of_geometrically hf _ _

set_option backward.isDefEq.respectTransparency false in

lemma geometrically_iff_forall_fiberToSpecResidueField :
    geometrically P f ↔ ∀ (y : Y), geometrically P (f.fiberToSpecResidueField y) := by
  refine ⟨fun hf y ↦ (geometrically P).pullback_snd _ _ hf, fun H ↦ ?_⟩
  intro K _ y Z fst snd h
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField _ _).symm.surjective y
  let p : Z ⟶ f.fiber y :=
    pullback.lift fst (snd ≫ Spec.map φ) (by simp [h.w, Scheme.SpecToEquivOfField])
  apply H y (Spec.map φ) p snd
  simp only [Scheme.SpecToEquivOfField, Equiv.coe_fn_symm_mk] at h
  refine .flip (.of_bot (.flip ?_) ?_ (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip)
  · convert h
    simp [p]
  · simp [p, Scheme.Hom.fiberToSpecResidueField]

lemma self_of_isIntegral_of_geometrically [IsIntegral Y] [Subsingleton Y] (hf : geometrically P f) :
    P X := by
  rw [geometrically_eq_universally] at hf
  exact MorphismProperty.universally_le _ _ hf ‹_› ‹_›

variable {P : ObjectProperty Scheme.{u}} {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)}

lemma geometrically_iff_of_commRing :
    geometrically P f ↔ ∀ ⦃K : Type u⦄ [Field K] [Algebra R K] ⦃Y : Scheme.{u}⦄ (fst : Y ⟶ X)
      (snd : Y ⟶ Spec (.of K)), IsPullback fst snd f (Spec.map <| ofHom (algebraMap R K)) →
      P Y := by
  refine ⟨fun hs K _ _ Z fst snd h ↦ hs _ _ _ h, fun H K _ y Z fst snd h ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  exact H fst snd h

lemma geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    geometrically P f ↔ ∀ (K : Type u) [Field K] [Algebra R K],
      P (Limits.pullback f (Spec.map <| ofHom <| algebraMap R K)) := by
  refine ⟨fun hf K _ _ ↦ pullback_of_geometrically hf _ _, fun H ↦ ?_⟩
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  exact H K

end geometrically

end AlgebraicGeometry
