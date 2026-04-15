/-
Extracted from AlgebraicGeometry/Artinian.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Artinian and Locally Artinian Schemes

We define and prove basic properties about Artinian and locally Artinian Schemes.

## Main definitions

* `AlgebraicGeometry.IsLocallyArtinian`: A scheme is locally Artinian if for all open affines,
  the section ring is an Artinian ring.

* `AlgebraicGeometry.IsArtinianScheme`: A scheme is Artinian if it is locally Artinian and
  quasi-compact.

## Main results

* `AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology`: A scheme is
  locally Artinian if and only if it is LocallyNoetherian and it has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology`: A scheme is Artinian
  if and only if it is Noetherian and has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.finite`: An Artinian scheme is finite.

* `AlgebraicGeometry.Scheme.isArtinianScheme_Spec`: A commutative ring R is Artinian if and only if
  Spec R is Artinian.

-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

class IsLocallyArtinian (X : Scheme) : Prop where
  isArtinianRing_presheaf_obj : ∀ (U : X.affineOpens),
    IsArtinianRing Γ(X, U) := by infer_instance

attribute [instance] IsLocallyArtinian.isArtinianRing_presheaf_obj

-- INSTANCE (free from Core): IsLocallyArtinian.isLocallyNoetherian

-- INSTANCE (free from Core): IsLocallyArtinian.isArtinianRing_of_isAffine

lemma IsLocallyArtinian.of_topologicalKrullDim_le_zero
    [IsLocallyNoetherian X] (h : topologicalKrullDim X ≤ 0) : IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U := by
    have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff, ← ringKrullDim,
      Nat.cast_zero, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
    change topologicalKrullDim (Spec Γ(X, U)) ≤ 0
    rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_subspace_le X U).trans h

theorem IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
    [IsLocallyNoetherian X] [DiscreteTopology X] :
    IsLocallyArtinian X :=
  .of_topologicalKrullDim_le_zero (topologicalKrullDim_zero_of_discreteTopology X)

private lemma IsLocallyArtinian.of_isOpenImmersion [IsOpenImmersion f] [IsLocallyArtinian Y] :
    IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U :=
    have : IsArtinianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, U.2.image_of_isOpenImmersion f⟩
    (f.appIso U).commRingCatIsoToRingEquiv.surjective.isArtinianRing

-- INSTANCE (free from Core): [IsLocallyArtinian

-- INSTANCE (free from Core): [IsLocallyArtinian

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (priority
