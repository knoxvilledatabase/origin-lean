/-
Extracted from NumberTheory/MulChar/Lemmas.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Further Results on multiplicative characters
-/

namespace MulChar

section CommMonoid

variable {R : Type*} [CommMonoid R] {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
  {R' : Type*} [CommMonoidWithZero R']

lemma eq_iff {g : Rˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g) (χ₁ χ₂ : MulChar R R') :
    χ₁ = χ₂ ↔ χ₁ g.val = χ₂ g.val := by
  rw [← Equiv.apply_eq_iff_eq equivToUnitHom, MonoidHom.eq_iff_eq_on_generator hg,
    ← coe_equivToUnitHom, ← coe_equivToUnitHom, Units.ext_iff]

theorem restrict_ofUnitHom (f : Rˣ →* R'ˣ) (S : Submonoid R) :
    restrict S (ofUnitHom f) =
      ofUnitHom ((f.restrict S.units).comp S.unitsEquivUnitsType.symm) := by
  ext x
  simp only [ofUnitHom_eq, restrict_apply, Units.isUnit, reduceIte, equivToUnitHom_symm_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MonoidHom.restrict_apply]
  rw [← Submonoid.val_unitsEquivUnitsType_symm_apply_coe S x, equivToUnitHom_symm_coe]

variable (R')
