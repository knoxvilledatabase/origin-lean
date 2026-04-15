/-
Extracted from Algebra/Homology/DerivedCategory/Ext/Map.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Map between Ext groups induced by an exact functor

In this file, we define the map `Ext^k (M, N) → Ext^k (F(M), F(N))`,
where `F` is an exact functor between abelian categories.

# Main Definition and results

* `CategoryTheory.Abelian.Ext.mapExactFunctor` : The map between `Ext` induced by
  `CategoryTheory.LocalizerMorphism.smallShiftedHomMap`.

* `CategoryTheory.Functor.mapExtAddHom` : Upgraded of `CategoryTheory.Abelian.Ext.mapExactFunctor`
  into an additive homomorphism.

* `CategoryTheory.Functor.mapExtLinearMap` : Upgrade of `F.mapExtAddHom` assuming `F` is linear.

* `Ext.mapExactFunctor_mk₀` : `Ext.mapExactFunctor` commutes with `Ext.mk₀`

* `Ext.mapExactFunctor_comp` : `Ext.mapExactFunctor` preserves `Ext.comp`

* `mapExactFunctor_extClass` :
  `Ext.mapExactFunctor` commutes with `ShortComplex.ShortExact.extClass`

-/

universe t t' w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

open DerivedCategory

set_option backward.isDefEq.respectTransparency false in

lemma DerivedCategory.map_triangleOfSESδ [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    dsimp% F.mapDerivedCategory.map (triangleOfSESδ hS) =
    (F.mapDerivedCategoryFactors.hom.app S.X₃) ≫
      triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex _)) ≫
        (F.mapDerivedCategoryFactors.inv.app S.X₁)⟦1⟧' ≫
          (F.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  rw [← cancel_epi (F.mapDerivedCategory.map
    (Q.map (CochainComplex.mappingCone.descShortComplex S))), ← Functor.map_comp,
    descShortComplex_triangleOfSESδ, F.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex,
    Functor.map_comp_assoc, descShortComplex_triangleOfSESδ_assoc, Category.assoc,
    ← Functor.map_comp_assoc]
  dsimp
  rw [← CochainComplex.mappingCone.map_δ, Functor.map_comp_assoc,
    ← F.mapDerivedCategoryFactors_hom_naturality_assoc, Functor.map_comp]
  simp [NatTrans.shift_app, Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app,
    ← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
