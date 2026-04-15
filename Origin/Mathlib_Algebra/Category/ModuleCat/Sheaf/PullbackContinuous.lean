/-
Extracted from Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Pullback of sheaves of modules

Let `S` and `R` be sheaves of rings over sites `(C, J)` and `(D, K)` respectively.
Let `F : C ⥤ D` be a continuous functor between these sites, and
let `φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R` be a morphism
of sheaves of rings.

In this file, we define the pullback functor for sheaves of modules
`pullback.{v} φ : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R`
that is left adjoint to `pushforward.{v} φ`. We show that it exists
under suitable assumptions, and prove that the pullback of (pre)sheaves of
modules commutes with the sheafification.

From the compatibility of `pushforward` with respect to composition, we deduce
similar pseudofunctor-like properties of the `pullback` functors.

-/

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [(pushforward.{v} φ).IsRightAdjoint]

noncomputable def pullback : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint

noncomputable def pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)

-- INSTANCE (free from Core): :

end

variable [(PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace PullbackConstruction

set_option backward.isDefEq.respectTransparency false in

noncomputable def adjunction :
    (forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
      PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)) ⊣ pushforward.{v} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G ↦
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
            (((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).homEquiv F.val G.val).trans
              ((fullyFaithfulForget S).homEquiv (Y := (pushforward φ).obj G)).symm)
      homEquiv_naturality_left_symm := by
        intros
        dsimp [Functor.FullyFaithful.homEquiv]
        -- these erw seem difficult to remove
        erw [Adjunction.homEquiv_naturality_left_symm,
          Adjunction.homEquiv_naturality_left_symm]
        dsimp [pushforward_obj_val]
        simp only [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        tauto }

end PullbackConstruction

-- INSTANCE (free from Core): :

noncomputable def pullbackIso :
    pullback.{v} φ ≅
      forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction φ)
    (PullbackConstruction.adjunction φ)

variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

noncomputable def sheafificationCompPullback :
    PresheafOfModules.sheafification (𝟙 S.obj) ⋙ pullback.{v} φ ≅
      PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).comp
      (pullbackPushforwardAdjunction φ))
    ((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)))

end

end

-- INSTANCE (free from Core): :

variable (S) in

noncomputable def pullbackId : pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _ :=
  ((pullbackPushforwardAdjunction.{v} (F := 𝟭 C) (𝟙 S))).leftAdjointIdIso (pushforwardId S)

variable (S) in
