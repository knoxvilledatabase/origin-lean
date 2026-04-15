/-
Extracted from RingTheory/Valuation/PrimeMultiplicity.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `multiplicity` of a prime in an integral domain as an additive valuation
-/

variable {R : Type*} [CommRing R] [IsDomain R] {p : R}

noncomputable def multiplicity_addValuation (hp : Prime p) : AddValuation R ℕ∞ :=
  AddValuation.of (emultiplicity p) (emultiplicity_zero _) (emultiplicity_of_one_right hp.not_unit)
    (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp
