/-
Extracted from RingTheory/LocalRing/ResidueField/Instances.lean
Genuine: 1 of 8 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-! # Instances on residue fields -/

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (p : Ideal A) (q : Ideal B) [q.LiesOver p]

attribute [local instance] Ideal.Quotient.field

-- INSTANCE (free from Core): [p.IsMaximal]

-- INSTANCE (free from Core): [p.IsMaximal]

variable {p q} in

lemma Algebra.isSeparable_residueField_iff [p.IsMaximal] [q.IsMaximal] :
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

-- INSTANCE (free from Core): [p.IsPrime]

-- INSTANCE (free from Core): [p.IsPrime]

namespace IsLocalRing

variable {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k]

-- INSTANCE (free from Core): ResidueField.algebraOfIsIntegral

-- INSTANCE (free from Core): ResidueField.isScalarTowerOfIsIntegral

-- INSTANCE (free from Core): [Module.Finite

end IsLocalRing
