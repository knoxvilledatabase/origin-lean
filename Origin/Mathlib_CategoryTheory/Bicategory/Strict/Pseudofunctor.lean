/-
Extracted from CategoryTheory/Bicategory/Strict/Pseudofunctor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pseudofunctors from strict bicategory

This file provides an API for pseudofunctors `F` from a strict bicategory `B`. In
particular, this shall apply to pseudofunctors from locally discrete bicategories.

Firstly, we study the compatibilities of the flexible variants `mapId'` and `mapComp'`
of `mapId` and `mapComp` with respect to the composition with identities and the
associativity.

Secondly, given a commutative square `t ≫ r = l ≫ b` in `B`, we construct an
isomorphism `F.map t ≫ F.map r ≅ F.map l ≫ F.map b`
(see `Pseudofunctor.isoMapOfCommSq`).

-/

namespace CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

open Bicategory

namespace Pseudofunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᵖ C)

lemma mapComp'_comp_id {b₀ b₁ : B} (f : b₀ ⟶ b₁) :
    F.mapComp' f (𝟙 b₁) f = (ρ_ _).symm ≪≫ whiskerLeftIso _ (F.mapId b₁).symm := by
  ext
  rw [mapComp']
  dsimp
  rw [F.mapComp_id_right_hom f, Strict.rightUnitor_eqToIso, eqToIso.hom,
    ← F.map₂_comp_assoc, eqToHom_trans, eqToHom_refl, PrelaxFunctor.map₂_id,
    Category.id_comp]
