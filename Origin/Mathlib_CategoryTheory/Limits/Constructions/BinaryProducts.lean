/-
Extracted from CategoryTheory/Limits/Constructions/BinaryProducts.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Constructing binary product from pullbacks and terminal object.

The product is the pullback over the terminal objects. In particular, if a category
has pullbacks and a terminal object, then it has binary products.

We also provide the dual.
-/

universe v v' u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

def isBinaryProductOfIsTerminalIsPullback (F : Discrete WalkingPair ⥤ C) (c : Cone F) {X : C}
    (hX : IsTerminal X) (f : F.obj ⟨WalkingPair.left⟩ ⟶ X) (g : F.obj ⟨WalkingPair.right⟩ ⟶ X)
    (hc : IsLimit
      (PullbackCone.mk (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩ :) <|
        hX.hom_ext (_ ≫ f) (_ ≫ g))) : IsLimit c where
  lift s :=
    hc.lift
      (PullbackCone.mk (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingCospan.left) (hc.fac _ WalkingCospan.right)
  uniq s m J := by
    let c' :=
      PullbackCone.mk (m ≫ c.π.app ⟨WalkingPair.left⟩) (m ≫ c.π.app ⟨WalkingPair.right⟩ :)
        (hX.hom_ext (_ ≫ f) (_ ≫ g))
    dsimp; rw [← J, ← J]
    apply hc.hom_ext
    rintro (_ | (_ | _)) <;> simp only [PullbackCone.mk_π_app]
    exacts [(Category.assoc _ _ _).symm.trans (hc.fac_assoc c' WalkingCospan.left f).symm,
      (hc.fac c' WalkingCospan.left).symm, (hc.fac c' WalkingCospan.right).symm]

def isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z)
    (H₂ : IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsLimit (BinaryFan.mk h k) := by
  apply isBinaryProductOfIsTerminalIsPullback _ _ H₁
  exact H₂

def isPullbackOfIsTerminalIsProduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z) (H₂ : IsLimit (BinaryFan.mk h k)) :
    IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply PullbackCone.isLimitAux'
  intro s
  use H₂.lift (BinaryFan.mk s.fst s.snd)
  use H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩
  use H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.right⟩
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩).symm
  · exact h₂.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.right⟩).symm

noncomputable def limitConeOfTerminalAndPullbacks [HasTerminal C] [HasPullbacks C]
    (F : Discrete WalkingPair ⥤ C) : LimitCone F where
  cone :=
    { pt :=
        pullback (terminal.from (F.obj ⟨WalkingPair.left⟩))
          (terminal.from (F.obj ⟨WalkingPair.right⟩))
      π :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pullback.fst _ _) (pullback.snd _ _) }
  isLimit :=
    isBinaryProductOfIsTerminalIsPullback F _ terminalIsTerminal _ _ (pullbackIsPullback _ _)

variable (C) in

theorem hasBinaryProducts_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasBinaryProducts C :=
  { has_limit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }

lemma preservesBinaryProducts_of_preservesTerminal_and_pullbacks [HasTerminal C]
    [HasPullbacks C] [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]
    [PreservesLimitsOfShape WalkingCospan F] : PreservesLimitsOfShape (Discrete WalkingPair) F :=
  ⟨fun {K} =>
    preservesLimit_of_preserves_limit_cone (limitConeOfTerminalAndPullbacks K).2
      (by
        apply
          isBinaryProductOfIsTerminalIsPullback _ _ (isLimitOfHasTerminalOfPreservesLimit F)
        apply isLimitOfHasPullbackOfPreservesLimit)⟩

noncomputable def prodIsoPullback [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
  limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)
