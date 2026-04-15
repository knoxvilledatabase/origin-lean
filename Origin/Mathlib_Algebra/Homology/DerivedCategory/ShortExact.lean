/-
Extracted from Algebra/Homology/DerivedCategory/ShortExact.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The distinguished triangle attached to a short exact sequence of cochain complexes

Given a short exact short complex `S` in the category `CochainComplex C ℤ`,
we construct a distinguished triangle
`Q.obj S.X₁ ⟶ Q.obj S.X₂ ⟶ Q.obj S.X₃ ⟶ (Q.obj S.X₃)⟦1⟧`
in the derived category of `C`.
(See `triangleOfSES` and `triangleOfSES_distinguished`.)

-/

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Category Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

noncomputable def triangleOfSESδ :
    Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  inv (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
    (Q.commShiftIso (1 : ℤ)).hom.app S.X₁
