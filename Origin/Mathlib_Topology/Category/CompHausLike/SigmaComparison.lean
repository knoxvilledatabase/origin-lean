/-
Extracted from Topology/Category/CompHausLike/SigmaComparison.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# The sigma-comparison map

This file defines the map `CompHausLike.sigmaComparison` associated to a presheaf `X` on
`CompHausLike P`, and a finite family `S₁,...,Sₙ` of spaces in `CompHausLike P`, where `P` is
stable under taking finite disjoint unions.

The map `sigmaComparison` is the canonical map `X(S₁ ⊔ ... ⊔ Sₙ) ⟶ X(S₁) × ... × X(Sₙ)` induced by
the inclusion maps `Sᵢ ⟶ S₁ ⊔ ... ⊔ Sₙ`, and it is an isomorphism when `X` preserves finite
products.
-/

universe u w

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} → Prop} [HasExplicitFiniteCoproducts.{u} P]
  (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)) [PreservesFiniteProducts X]
  {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]
  [∀ a, HasProp P (σ a)]

-- INSTANCE (free from Core): :

def sigmaComparison : X.obj ⟨(of P ((a : α) × σ a))⟩ ⟶ ((a : α) → X.obj ⟨of P (σ a)⟩) :=
  TypeCat.ofHom fun x a ↦ X.map (ofHom _ ⟨Sigma.mk a, continuous_sigmaMk⟩).op x

set_option backward.isDefEq.respectTransparency false in

theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ =
    (X.mapIso (opCoproductIsoProduct'
      (finiteCoproduct.isColimit.{u, u} (fun a ↦ of P (σ a)))
      (productIsProduct fun x ↦ Opposite.op (of P (σ x))))).hom ≫
    (PreservesProduct.iso X fun a ↦ ⟨of P (σ a)⟩).hom ≫
    (Types.productIso.{u, max u w} fun a ↦ X.obj ⟨of P (σ a)⟩).hom := by
  ext x a
  simp only [TypeCat.Fun.toFun_apply, Cofan.mk_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, comp_apply, Types.productIso_hom_comp_eval_apply]
  have := ConcreteCategory.congr_hom (piComparison_comp_π X (fun a ↦ ⟨of P (σ a)⟩) a)
  simp only [comp_apply] at this
  rw [this, ← comp_apply, ← Functor.map_comp]
  simp only [sigmaComparison, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
  apply ConcreteCategory.congr_hom
  congr 2
  rw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  simp only [opCoproductIsoProduct, ← unop_comp, opCoproductIsoProduct'_comp_self]
  erw [IsColimit.fac]
  rfl

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): isIsoSigmaComparison

end CompHausLike
