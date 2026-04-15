/-
Extracted from RingTheory/AdicCompletion/LocalRing.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic Properties of Complete Local Ring

In this file we prove that a ring that is adic complete with respect to a maximal ideal
ia a local ring (complete local ring).

-/

variable {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal]

theorem isLocalRing_of_isAdicComplete_maximal [IsAdicComplete m R] : IsLocalRing R :=
  IsLocalRing.of_unique_max_ideal ⟨m, ‹m.IsMaximal›, fun _ hJ ↦
    (‹m.IsMaximal›.eq_of_le hJ.ne_top <|
      (IsAdicComplete.le_jacobson_bot m).trans <| sInf_le ⟨bot_le, hJ⟩).symm⟩
