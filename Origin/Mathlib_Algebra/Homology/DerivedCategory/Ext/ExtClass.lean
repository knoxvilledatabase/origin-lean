/-
Extracted from Algebra/Homology/DerivedCategory/Ext/ExtClass.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The Ext class of a short exact sequence

In this file, given a short exact short complex `S : ShortComplex C`
in an abelian category, we construct the associated class in
`Ext S.X₃ S.X₁ 1`.

-/

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated

open Abelian

namespace ShortComplex

variable (S : ShortComplex C)

namespace ShortExact

variable {S}

variable (hS : S.ShortExact)

local notation "W" => HomologicalComplex.quasiIso C (ComplexShape.up ℤ)

local notation "S'" => S.map (CochainComplex.singleFunctor C 0)

local notation "hS'" => hS.map_of_exact (HomologicalComplex.single _ _ _)

local notation "K" => CochainComplex.mappingCone (ShortComplex.f S')

local notation "qis" => CochainComplex.mappingCone.descShortComplex S'

local notation "hqis" => CochainComplex.mappingCone.quasiIso_descShortComplex hS'

local notation "δ" => Triangle.mor₃ (CochainComplex.mappingCone.triangle (ShortComplex.f S'))

-- INSTANCE (free from Core): :

set_option backward.privateInPublic true in

include hS in

private lemma hasSmallLocalizedHom_S'_X₃_K :
    HasSmallLocalizedHom.{w} W (S').X₃ K := by
  rw [Localization.hasSmallLocalizedHom_iff_target W (S').X₃ qis hqis]
  dsimp
  apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := ℤ)

set_option backward.privateInPublic true in

include hS in

private lemma hasSmallLocalizedShiftedHom_K_S'_X₁ :
    HasSmallLocalizedShiftedHom.{w} W ℤ K (S').X₁ := by
  rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W ℤ qis hqis (S').X₁]
  infer_instance

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

noncomputable def extClass : Ext.{w} S.X₃ S.X₁ 1 := by
  have := hS.hasSmallLocalizedHom_S'_X₃_K
  have := hS.hasSmallLocalizedShiftedHom_K_S'_X₁
  change SmallHom W (S').X₃ ((S').X₁⟦(1 : ℤ)⟧)
  exact (SmallHom.mkInv qis hqis).comp (SmallHom.mk W δ)

set_option backward.isDefEq.respectTransparency false in
