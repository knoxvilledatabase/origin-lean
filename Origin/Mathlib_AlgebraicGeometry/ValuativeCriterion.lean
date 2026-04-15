/-
Extracted from AlgebraicGeometry/ValuativeCriterion.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Valuative criterion

## Main results

- `AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`:
  A morphism is universally closed if and only if
  it is quasi-compact and satisfies the existence part of the valuative criterion.
- `AlgebraicGeometry.IsSeparated.eq_valuativeCriterion`:
  A morphism is separated if and only if
  it is quasi-separated and satisfies the uniqueness part of the valuative criterion.
- `AlgebraicGeometry.IsProper.eq_valuativeCriterion`:
  A morphism is proper if and only if
  it is qcqs and of finite type and satisfies the valuative criterion.

## Future projects
Show that it suffices to check discrete valuation rings when the base is Noetherian.

-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

structure ValuativeCommSq {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The valuation ring of a valuative commutative square. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The field of fractions of a valuative commutative square. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The top map in a valuative commutative map. -/
  (i₁ : Spec (.of K) ⟶ X)
  /-- The bottom map in a valuative commutative map. -/
  (i₂ : Spec (.of R) ⟶ Y)
  (commSq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂)

namespace ValuativeCommSq

attribute [instance] commRing domain valuationRing field algebra isFractionRing

end ValuativeCommSq

def ValuativeCriterion.Existence : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, S.commSq.HasLift

def ValuativeCriterion.Uniqueness : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, Subsingleton S.commSq.LiftStruct

def ValuativeCriterion : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, Nonempty (Unique (S.commSq.LiftStruct))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma ValuativeCriterion.iff {f : X ⟶ Y} :
    ValuativeCriterion f ↔ Existence f ∧ Uniqueness f := by
  change (∀ _, _) ↔ (∀ _, _) ∧ (∀ _, _)
  simp_rw [← forall_and, unique_iff_subsingleton_and_nonempty, and_comm, CommSq.HasLift.iff]

lemma ValuativeCriterion.eq :
    ValuativeCriterion = Existence ⊓ Uniqueness := by
  ext X Y f
  exact iff

lemma ValuativeCriterion.existence {f : X ⟶ Y} (h : ValuativeCriterion f) :
    ValuativeCriterion.Existence f := (iff.mp h).1

lemma ValuativeCriterion.uniqueness {f : X ⟶ Y} (h : ValuativeCriterion f) :
    ValuativeCriterion.Uniqueness f := (iff.mp h).2

namespace ValuativeCriterion.Existence

open IsLocalRing
