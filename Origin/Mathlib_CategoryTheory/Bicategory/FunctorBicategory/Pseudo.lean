/-
Extracted from CategoryTheory/Bicategory/FunctorBicategory/Pseudo.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The bicategory of pseudofunctors

Given bicategories `B` and `C`, we define a bicategory structure on `Pseudofunctor B C` whose
* objects are pseudofunctors,
* 1-morphisms are strong natural transformations, and
* 2-morphisms are modifications.

We scope this instance to the `CategoryTheory.Pseudofunctor.StrongTrans` namespace to avoid
potential future conflicts with other bicategory instances on `Pseudofunctor B C`.
-/

namespace CategoryTheory.Pseudofunctor

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

namespace StrongTrans

variable {F G H I : Pseudofunctor B C}

set_option backward.isDefEq.respectTransparency false in

abbrev whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
      simp }

set_option backward.isDefEq.respectTransparency false in

abbrev whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp
      simp_rw [Category.assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
      simp }

set_option backward.isDefEq.respectTransparency false in

abbrev associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a))

set_option backward.isDefEq.respectTransparency false in

abbrev leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => λ_ (η.app a))

set_option backward.isDefEq.respectTransparency false in

abbrev rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)
