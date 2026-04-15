/-
Extracted from AlgebraicGeometry/AlgClosed/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Schemes over algebraically closed fields

We show that if `X` is locally of finite type over an algebraically closed field `k`,
then the closed points of `X` are in bijection with the `k`-points of `X`.
See `AlgebraicGeometry.pointEquivClosedPoint`.

-/

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x})

def residueFieldIsoBase : X.residueField x ≅ .of K :=
  letI : IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f)) := by
    have : IsFinite (X.fromSpecResidueField x ≫ f) := by
      rw [isClosed_singleton_iff_isClosedImmersion] at hx
      rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  (asIso (Spec.preimage (X.fromSpecResidueField x ≫ f))).symm
