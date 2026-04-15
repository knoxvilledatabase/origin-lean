/-
Extracted from Algebra/Homology/BifunctorShift.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Behavior of the action of a bifunctor on cochain complexes with respect to shifts

In this file, given cochain complexes `K₁ : CochainComplex C₁ ℤ`, `K₂ : CochainComplex C₂ ℤ` and
a functor `F : C₁ ⥤ C₂ ⥤ D`, we define an isomorphism of cochain complexes in `D`:
- `CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x` of type
  `mapBifunctor (K₁⟦x⟧) K₂ F ≅ (mapBifunctor K₁ K₂ F)⟦x⟧` for `x : ℤ`.
- `CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y` of type
  `mapBifunctor K₁ (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦y⟧` for `y : ℤ`.

In the lemma `CochainComplex.mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso`, we obtain
that the two ways to deduce an isomorphism
`mapBifunctor (K₁⟦x⟧) (K₂⟦y⟧) F ≅ (mapBifunctor K₁ K₂ F)⟦x + y⟧` differ by the sign
`(x * y).negOnePow`.

These definitions and properties can be summarised by saying that the bifunctor
`F.map₂CochainComplex : CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ`
commutes with shifts by `ℤ`.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace CochainComplex

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]

abbrev HasMapBifunctor := HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

noncomputable abbrev mapBifunctor [HasMapBifunctor K₁ K₂ F] : CochainComplex D ℤ :=
  HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)

noncomputable abbrev ιMapBifunctor [HasMapBifunctor K₁ K₂ F] (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n) :
    (F.obj (K₁.X n₁)).obj (K₂.X n₂) ⟶ (mapBifunctor K₁ K₂ F).X n :=
  HomologicalComplex.ιMapBifunctor K₁ K₂ F _ _ _ _ h

end

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : CochainComplex C₁ ℤ) (f₁ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)
  [HasMapBifunctor K₁ K₂ F]

set_option backward.isDefEq.respectTransparency false in
