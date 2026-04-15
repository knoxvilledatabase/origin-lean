/-
Extracted from RingTheory/Artinian/Instances.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Instances related to Artinian rings

We show that every reduced Artinian ring and the polynomial ring over it
are decomposition monoids, and every reduced Artinian ring is semisimple.
-/

theorem StrongRankCondition.of_isArtinian (R) [Semiring R] [Nontrivial R]
    [∀ n, IsArtinian R (Fin n → R)] : StrongRankCondition R :=
  (strongRankCondition_iff_succ R).2 fun n f hf ↦
    have e := LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
    not_subsingleton R <| IsArtinian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

namespace IsArtinianRing

variable (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]

attribute [local instance] fieldOfSubtypeIsMaximal

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end IsArtinianRing
