/-
Extracted from CategoryTheory/Limits/Sifted.lean
Genuine: 11 of 21 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Sifted categories

A category `C` is sifted if `C` is nonempty and the diagonal functor `C ⥤ C × C` is final.
Sifted categories can be characterized as those such that the colimit functor `(C ⥤ Type) ⥤ Type `
preserves finite products. We achieve this characterization in this file.

## Main results
- `isSifted_of_hasBinaryCoproducts_and_nonempty`: A nonempty category with binary coproducts is
  sifted.
- `IsSifted.colimPreservesFiniteProductsOfIsSifted`: The `Type`-valued colimit functor for sifted
  diagrams preserves finite products.
- `IsSifted.of_colimit_preservesFiniteProducts`: The converse: if the `Type`-valued colimit functor
  preserves finite products, the category is sifted.
- `IsSifted.of_final_functor_from_sifted`: A category admitting a final functor from a sifted
  category is itself sifted.

## References
- [nLab, *Sifted category*](https://ncatlab.org/nlab/show/sifted+category)
- [*Algebraic Theories*, Chapter 2.][Adamek_Rosicky_Vitale_2010]
-/

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Limits Functor

variable (C : Type u) [Category.{v} C]

abbrev IsSiftedOrEmpty : Prop := Final (diag C)

class IsSifted : Prop extends IsSiftedOrEmpty C where
  [nonempty : Nonempty C]

attribute [scoped instance] IsSifted.nonempty

namespace IsSifted

variable {C}

lemma isSifted_of_equiv [IsSifted C] {D : Type u₁} [Category.{v₁} D] (e : D ≌ C) : IsSifted D :=
  letI : Final (diag D) := by
    letI : D × D ≌ C × C := Equivalence.prod e e
    have sq : (e.inverse ⋙ diag D ⋙ this.functor ≅ diag C) :=
        NatIso.ofComponents (fun c ↦ by dsimp [this]
                                        exact Iso.prod (e.counitIso.app c) (e.counitIso.app c))
    apply_rules [final_iff_comp_equivalence _ this.functor |>.mpr,
      final_iff_final_comp e.inverse _ |>.mpr, final_of_natIso sq.symm]
  letI : _root_.Nonempty D := ⟨e.inverse.obj (_root_.Nonempty.some IsSifted.nonempty)⟩
  ⟨⟩

lemma isSifted_iff_asSmallIsSifted : IsSifted C ↔ IsSifted (AsSmall.{w} C) where
  mp _ := isSifted_of_equiv AsSmall.equiv.symm
  mpr _ := isSifted_of_equiv AsSmall.equiv

-- INSTANCE (free from Core): [IsSifted

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): [HasBinaryCoproducts

-- INSTANCE (free from Core): isSifted_of_hasBinaryCoproducts_and_nonempty

end IsSifted

end

variable {C : Type u} [Category.{v} C] [IsSiftedOrEmpty C] {D : Type u₁} [Category.{v₁} D]
  {D' : Type u₂} [Category.{v₂} D'] (F : C ⥤ D) (G : C ⥤ D')

-- INSTANCE (free from Core): [F.Final]

end

noncomputable section SmallCategory

open MonoidalCategory CartesianMonoidalCategory

namespace IsSifted

variable {C : Type u} [SmallCategory C]

open scoped MonoidalCategory.ExternalProduct

variable (X Y : C ⥤ Type u)

set_option backward.isDefEq.respectTransparency false in

lemma factorization_prodComparison_colim :
    (HasColimit.isoOfNatIso ((externalProductCompDiagIso _ _).app (X, Y)).symm).hom ≫
      colimit.pre (X ⊠ Y) (diag C) ≫
        (PreservesColimit₂.isoColimitUncurryWhiskeringLeft₂ X Y <|
          curriedTensor <| Type u).hom =
    CartesianMonoidalCategory.prodComparison colim X Y := by
  apply colimit.hom_ext
  intro j
  dsimp [externalProductBifunctor, CartesianMonoidalCategory.prodComparison,
    externalProductBifunctorCurried, externalProduct]
  cat_disch

variable [IsSifted C]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): colim_preservesLimits_pair_of_sSifted

-- INSTANCE (free from Core): colim_preservesBinaryProducts_of_isSifted

-- INSTANCE (free from Core): colim_preservesTerminal_of_isSifted

-- INSTANCE (free from Core): colim_preservesLimitsOfShape_pempty_of_isSifted

-- INSTANCE (free from Core): colim_preservesFiniteProducts_of_isSifted

end

variable (C)

open Opposite in

open scoped MonoidalCategory.ExternalProduct in

theorem isSiftedOrEmpty_of_colim_preservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSiftedOrEmpty C := by
  apply final_of_colimit_comp_coyoneda_iso_pUnit
  rintro ⟨c₁, c₂⟩
  calc colimit <| diag C ⋙ coyoneda.obj (op (c₁, c₂))
    _ ≅ colimit <| _ ⋙ (coyoneda.obj _) ⊠ (coyoneda.obj _) :=
      HasColimit.isoOfNatIso <| isoWhiskerLeft _ <| .refl _
    _ ≅ colimit (_ ⊗ _) := HasColimit.isoOfNatIso <| .refl _
    _ ≅ (colimit _) ⊗ (colimit _) := CartesianMonoidalCategory.prodComparisonIso colim _ _
    _ ≅ PUnit ⊗ PUnit :=
      (Coyoneda.colimitCoyonedaIso _) ⊗ᵢ (Coyoneda.colimitCoyonedaIso _)
    _ ≅ PUnit := λ_ _

lemma isSiftedOrEmpty_of_colim_preservesFiniteProducts
    [h : PreservesFiniteProducts (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSiftedOrEmpty C :=
  isSiftedOrEmpty_of_colim_preservesBinaryProducts C

lemma nonempty_of_colim_preservesLimitsOfShapeFinZero
    [PreservesLimitsOfShape (Discrete (Fin 0)) (colim : (C ⥤ Type u) ⥤ Type u)] :
    Nonempty C := by
  suffices connected : IsConnected C by infer_instance
  rw [Types.isConnected_iff_colimit_constPUnitFunctor_iso_pUnit]
  constructor
  haveI : PreservesLimitsOfShape (Discrete PEmpty) (colim : (C ⥤ _) ⥤ Type u) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence finZeroEquiv') _
  apply HasColimit.isoOfNatIso (_ : Types.constPUnitFunctor C ≅ (⊤_ (C ⥤ Type u))) |>.trans
  · apply PreservesTerminal.iso colim |>.trans
    exact Types.terminalIso
  · apply_rules [IsTerminal.uniqueUpToIso _ terminalIsTerminal, evaluationJointlyReflectsLimits]
    intro _
    exact isLimitChangeEmptyCone _ Types.isTerminalPUnit _ <| Iso.refl _

theorem of_colim_preservesFiniteProducts
    [h : PreservesFiniteProducts (colim : (C ⥤ Type u) ⥤ Type u)] :
    IsSifted C := by
  have := isSiftedOrEmpty_of_colim_preservesFiniteProducts C
  have := nonempty_of_colim_preservesLimitsOfShapeFinZero C
  constructor

variable {C}

theorem of_final_functor_from_sifted'
    {D : Type u} [SmallCategory D] [IsSifted C] (F : C ⥤ D) [Final F] : IsSifted D := by
  have : PreservesFiniteProducts (colim : (D ⥤ Type u) ⥤ _) :=
    ⟨fun n ↦ preservesLimitsOfShape_of_natIso (Final.colimIso F)⟩
  exact of_colim_preservesFiniteProducts D

end

end IsSifted

end SmallCategory

variable {C : Type u} [Category.{v} C]

theorem IsSifted.of_final_functor_from_sifted {D : Type u₁} [Category.{v₁} D] [h₁ : IsSifted C]
    (F : C ⥤ D) [Final F] : IsSifted D := by
  rw [isSifted_iff_asSmallIsSifted] at h₁ ⊢
  exact of_final_functor_from_sifted' <|
    AsSmall.equiv.{_, _, max u₁ v₁}.inverse ⋙ F ⋙ AsSmall.equiv.{_, _, max u v}.functor

end CategoryTheory
