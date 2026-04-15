/-
Extracted from Topology/Category/TopCat/Limits/Pullbacks.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Pullbacks and pushouts in the category of topological spaces
-/

open TopologicalSpace Topology

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [Category.{w} J]

section Pullback

variable {X Y Z : TopCat.{u}}

abbrev pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ X :=
  ofHom ⟨Prod.fst ∘ Subtype.val, by fun_prop⟩

abbrev pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.of { p : X × Y // f p.1 = g p.2 } ⟶ Y :=
  ofHom ⟨Prod.snd ∘ Subtype.val, by fun_prop⟩

def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g)
    (by
      dsimp [pullbackFst, pullbackSnd, Function.comp_def]
      ext ⟨x, h⟩
      simpa)

def pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux' _
    (by
      intro S
      constructor; swap
      · exact ofHom
          { toFun := fun x =>
              ⟨⟨S.fst x, S.snd x⟩, by simpa using ConcreteCategory.congr_hom S.condition x⟩
            continuous_toFun := by fun_prop }
      refine ⟨?_, ?_, ?_⟩
      · delta pullbackCone
        ext a
        dsimp
      · delta pullbackCone
        ext a
        dsimp
      · intro m h₁ h₂
        ext x
        -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be `ext x`.
        apply Subtype.ext
        apply Prod.ext
        · simpa using ConcreteCategory.congr_hom h₁ x
        · simpa using ConcreteCategory.congr_hom h₂ x)

def pullbackIsoProdSubtype (f : X ⟶ Z) (g : Y ⟶ Z) :
    pullback f g ≅ TopCat.of { p : X × Y // f p.1 = g p.2 } :=
  (limit.isLimit _).conePointUniqueUpToIso (pullbackConeIsLimit f g)

set_option backward.isDefEq.respectTransparency false in
