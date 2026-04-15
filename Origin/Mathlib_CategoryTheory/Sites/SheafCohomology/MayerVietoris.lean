/-
Extracted from CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Mayer-Vietoris exact sequence in sheaf cohomology

Let `C` be a category equipped with a Grothendieck topology `J`.
Let `S : J.MayerVietorisSquare` be a Mayer-Vietoris square for `J`.
Let `F` be an abelian sheaf on `(C, J)`.

In this file, we obtain a long exact Mayer-Vietoris sequence:

`... ⟶ H^n(S.X₄, F) ⟶ H^n(S.X₂, F) ⊞ H^n(S.X₃, F) ⟶ H^n(S.X₁, F) ⟶ H^{n + 1}(S.X₄, F) ⟶ ...`

-/

universe w v u

namespace CategoryTheory

open Category Opposite Limits Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

namespace GrothendieckTopology.MayerVietorisSquare

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

noncomputable def toBiprod (n : ℕ) :
    F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃ :=
  biprod.lift ((F.cohomologyPresheaf n).map S.f₂₄.op)
      ((F.cohomologyPresheaf n).map S.f₃₄.op)

lemma toBiprod_apply {n : ℕ} (y : F.H' n S.X₄) :
    S.toBiprod F n y = (AddCommGrpCat.biprodIsoProd _ _).inv
      ⟨(F.cohomologyPresheaf n).map S.f₂₄.op y,
        (F.cohomologyPresheaf n).map S.f₃₄.op y⟩ := by
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  dsimp [toBiprod]
  ext
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_fst, Iso.inv_hom_id_apply]
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_snd, Iso.inv_hom_id_apply]

noncomputable def fromBiprod (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)
