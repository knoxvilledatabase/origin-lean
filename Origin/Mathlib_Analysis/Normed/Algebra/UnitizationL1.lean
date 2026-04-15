/-
Extracted from Analysis/Normed/Algebra/UnitizationL1.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-! # Unitization equipped with the $L^1$ norm

In another file, the `Unitization 𝕜 A` of a non-unital normed `𝕜`-algebra `A` is equipped with the
norm inherited as the pullback via a map (closely related to) the left-regular representation of the
algebra on itself (see `Unitization.instNormedRing`).

However, this construction is only valid (and an isometry) when `A` is a `RegularNormedAlgebra`.
Sometimes it is useful to consider the unitization of a non-unital algebra with the $L^1$ norm
instead. This file provides that norm on the type synonym `WithLp 1 (Unitization 𝕜 A)`, along
with the algebra isomorphism between `Unitization 𝕜 A` and `WithLp 1 (Unitization 𝕜 A)`.
Note that `TrivSqZeroExt` is also equipped with the $L^1$ norm in the analogous way, but it is
registered as an instance without the type synonym.

One application of this is a straightforward proof that the quasispectrum of an element in a
non-unital Banach algebra is compact, which can be established by passing to the unitization.
-/

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A]

variable [NormedSpace 𝕜 A]

namespace WithLp

open Unitization

noncomputable def unitization_addEquiv_prod : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A) :=
  (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toAddEquiv.trans <|
    (addEquiv 𝕜 A).trans (WithLp.linearEquiv 1 𝕜 (𝕜 × A)).symm.toAddEquiv

-- INSTANCE (free from Core): instUnitizationNormedAddCommGroup

noncomputable def uniformEquiv_unitization_addEquiv_prod :
    WithLp 1 (Unitization 𝕜 A) ≃ᵤ WithLp 1 (𝕜 × A) :=
  { unitization_addEquiv_prod 𝕜 A with
    uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id
    uniformContinuous_toFun := uniformContinuous_iff.mpr le_rfl }

-- INSTANCE (free from Core): instCompleteSpace

variable {𝕜 A}

open ENNReal in

lemma unitization_nnnorm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖₊ = ‖(ofLp x).fst‖₊ + ‖(ofLp x).snd‖₊ :=
  Subtype.ext <| unitization_norm_def x

lemma unitization_norm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖ = ‖x‖ := by
  simp [unitization_norm_def]

lemma unitization_nnnorm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖₊ = ‖x‖₊ := by
  simp [unitization_nnnorm_def]

lemma unitization_isometry_inr : Isometry fun x : A ↦ toLp 1 (x : Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm
    ((WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.comp <| Unitization.inrHom 𝕜 A)
    unitization_norm_inr

variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

-- INSTANCE (free from Core): instUnitizationRing
