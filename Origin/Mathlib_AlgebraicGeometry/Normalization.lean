/-
Extracted from AlgebraicGeometry/Normalization.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relative Normalization

Given a qcqs morphism `f : X ⟶ Y`, we define the relative normalization `f.normalization`,
along with the maps that `f` factor into:
- `f.toNormalization : X ⟶ f.normalization`: a dominant morphism
- `f.fromNormalization : f.normalization ⟶ Y`: an integral morphism

It satisfies the universal property:
For any factorization `X ⟶ T ⟶ Y` with `T ⟶ Y` integral,
the map `X ⟶ T` factors through `f.normalization` uniquely.
The factorization map is `AlgebraicGeometry.Scheme.Hom.normalizationDesc`, and the uniqueness result
is `AlgebraicGeometry.Scheme.Hom.normalization.hom_ext`.

We also show that normalization commutes with disjoint unions and smooth base change.

-/

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open AffineZariskiSite

set_option backward.isDefEq.respectTransparency false in

def normalizationDiagram : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U :=
    letI := (f.app U.unop).hom.toAlgebra
    .of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx ↦ by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rfl⟩ := Opposite.op_surjective V
      algebraize [(f.app U).hom, (f.app V).hom, (Y.presheaf.map i).hom,
        (X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom,
        (f.appLE V (f ⁻¹ᵁ U) (f.preimage_mono i.unop.le)).hom]
      have : IsScalarTower Γ(Y, V) Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' <| by
        simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]; rfl
      have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
      exact (hx.map (IsScalarTower.toAlgHom Γ(Y, V) _ Γ(X, f ⁻¹ᵁ U))).tower_top)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono j.unop.le) (f.preimage_mono i.unop.le), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

def normalizationDiagramMap : Y.presheaf ⟶ f.normalizationDiagram where
  app U :=
    letI := (f.app U.unop).hom.toAlgebra
    CommRingCat.ofHom (algebraMap Γ(Y, U.unop) (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

variable [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in

lemma coequifibered_normalizationDiagramMap :
    ((toOpensFunctor Y).op.whiskerLeft f.normalizationDiagramMap).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app (U.basicOpen r).1).hom.toAlgebra
  let : Algebra (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) :=
    ((normalizationDiagram f).map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    U.2.isLocalization_basicOpen _
  have : IsLocalization.Away ((algebraMap ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ U.1)) r)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  change IsLocalization.Away ((algebraMap Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) r)
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
  letI : Algebra ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.appLE _ _ (f.preimage_mono (Y.basicOpen_le _))).hom.toAlgebra
  have : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE, AffineZariskiSite.basicOpen]
  have : IsScalarTower (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
    Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := .of_algebraMap_eq' rfl
  exact IsLocalization.Away.integralClosure r
