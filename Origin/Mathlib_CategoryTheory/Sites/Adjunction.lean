/-
Extracted from CategoryTheory/Sites/Adjunction.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

In this file, we show that an adjunction `G ⊣ F` induces an adjunction between
categories of sheaves. We also show that `G` preserves sheafification.

-/

namespace CategoryTheory

open GrothendieckTopology Limits Opposite Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type*} [Category* E]

variable {F : D ⥤ E} {G : E ⥤ D}

abbrev sheafForget {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [HasSheafCompose J (forget D)] : Sheaf J D ⥤ Sheaf J (Type _) :=
  sheafCompose J (forget D)

namespace Sheaf

noncomputable section

def adjunction [HasWeakSheafify J D] [HasSheafCompose J F] (adj : G ⊣ F) :
    composeAndSheafify J G ⊣ sheafCompose J F :=
  Adjunction.restrictFullyFaithful ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J D))
    (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
