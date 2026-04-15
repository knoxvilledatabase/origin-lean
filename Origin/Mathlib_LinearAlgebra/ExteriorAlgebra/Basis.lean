/-
Extracted from LinearAlgebra/ExteriorAlgebra/Basis.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basis for `ExteriorAlgebra`
-/

namespace ExteriorAlgebra

open Module Set Set.powersetCard exteriorPower

variable {R M : Type*} {m n : ℕ} {I : Type*} [LinearOrder I] [CommRing R]
  [AddCommGroup M] [Module R M] (b : Module.Basis I R M)

-- INSTANCE (free from Core): :

noncomputable def _root_.Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M) :=
  .reindex
    ((DirectSum.Decomposition.isInternal (fun n => ⋀[R]^n M)).collectedBasis b.exteriorPower)
    Set.powersetCard.prodEquiv

lemma basis_apply (s : Finset I) :
    b.ExteriorAlgebra s = ιMulti_family R s.card b (prodEquiv.symm s).2 := by
  simp [Basis.ExteriorAlgebra]

lemma basis_apply_ofCard {s : Finset I} (s_card : s.card = n) :
    b.ExteriorAlgebra s = ιMulti_family R n b (ofCard s_card) := by
  subst s_card
  simp [basis_apply]

variable (s : powersetCard I m) (t : powersetCard I n)

lemma basis_apply_powersetCard :
    b.ExteriorAlgebra s = ιMulti_family R m b s := by
  simp [basis_apply_ofCard]

lemma basis_eq_coe_basis :
    b.ExteriorAlgebra s = (b.exteriorPower m s : ExteriorAlgebra R M) := by
  rw [basis_apply_powersetCard, exteriorPower.basis_apply, ιMulti_family_apply_coe]

lemma basis_mul_of_not_disjoint (h : ¬Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t = 0 := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_not_disjoint R b s t h

lemma basis_mul_of_disjoint (h : Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t =
      (permOfDisjoint h).sign • b.ExteriorAlgebra (disjUnion h) := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_disjoint R b s t h

end ExteriorAlgebra
