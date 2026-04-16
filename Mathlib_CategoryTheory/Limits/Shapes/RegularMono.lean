/-
Extracted from CategoryTheory/Limits/Shapes/RegularMono.lean
Genuine: 15 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Lean.Expr.Basic

noncomputable section

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

We give the constructions
* `IsSplitMono → RegularMono` and
* `RegularMono → Mono`
as well as the dual constructions for regular epimorphisms. Additionally, we give the construction
* `RegularEpi ⟶ StrongEpi`.

We also define classes `RegularMonoCategory` and `RegularEpiCategory` for categories in which
every monomorphism or epimorphism is regular, and deduce that these categories are
`StrongMonoCategory`s resp. `StrongEpiCategory`s.

-/

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

class RegularMono (f : X ⟶ Y) where
  /-- An object in `C` -/
  Z : C -- Porting note: violates naming but what is better?
  /-- A map from the codomain of `f` to `Z` -/
  left : Y ⟶ Z
  /-- Another map from the codomain of `f` to `Z` -/
  right : Y ⟶ Z
  /-- `f` equalizes the two maps -/
  w : f ≫ left = f ≫ right := by aesop_cat
  /-- `f` is the equalizer of the two maps -/
  isLimit : IsLimit (Fork.ofι f w)

attribute [reassoc] RegularMono.w

instance (priority := 100) RegularMono.mono (f : X ⟶ Y) [RegularMono f] : Mono f :=
  mono_of_isLimit_fork RegularMono.isLimit

instance equalizerRegular (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    RegularMono (equalizer.ι g h) where
  Z := Y
  left := g
  right := h
  w := equalizer.condition g h
  isLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s) (by simp) fun s m w => by
      apply equalizer.hom_ext
      simp [← w]

instance (priority := 100) RegularMono.ofIsSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    RegularMono f where
  Z := Y
  left := 𝟙 Y
  right := retraction f ≫ f
  isLimit := isSplitMonoEqualizes f

def RegularMono.lift' {W : C} (f : X ⟶ Y) [RegularMono f] (k : W ⟶ Y)
    (h : k ≫ (RegularMono.left : Y ⟶ @RegularMono.Z _ _ _ _ f _) = k ≫ RegularMono.right) :
    { l : W ⟶ X // l ≫ f = k } :=
  Fork.IsLimit.lift' RegularMono.isLimit _ h

def regularOfIsPullbackSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hr : RegularMono h] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono g where
  Z := hr.Z
  left := k ≫ hr.left
  right := k ≫ hr.right
  w := by
    repeat (rw [← Category.assoc, ← eq_whisker comm])
    simp only [Category.assoc, hr.w]
  isLimit := by
    apply Fork.IsLimit.mk' _ _
    intro s
    have l₁ : (Fork.ι s ≫ k) ≫ RegularMono.left = (Fork.ι s ≫ k) ≫ hr.right := by
      rw [Category.assoc, s.condition, Category.assoc]
    obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hr.isLimit _ l₁
    obtain ⟨p, _, hp₂⟩ := PullbackCone.IsLimit.lift' t _ _ hl
    refine ⟨p, hp₂, ?_⟩
    intro m w
    have z : m ≫ g = p ≫ g := w.trans hp₂.symm
    apply t.hom_ext
    apply (PullbackCone.mk f g comm).equalizer_ext
    · erw [← cancel_mono h, Category.assoc, Category.assoc, comm]
      simp only [← Category.assoc, eq_whisker z]
    · exact z

def regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [RegularMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono f :=
  regularOfIsPullbackSndOfRegular comm.symm (PullbackCone.flipIsLimit t)

instance (priority := 100) strongMono_of_regularMono (f : X ⟶ Y) [RegularMono f] : StrongMono f :=
  StrongMono.mk' (by
      intro A B z hz u v sq
      have : v ≫ (RegularMono.left : Y ⟶ RegularMono.Z f) = v ≫ RegularMono.right := by
        apply (cancel_epi z).1
        repeat (rw [← Category.assoc, ← eq_whisker sq.w])
        simp only [Category.assoc, RegularMono.w]
      obtain ⟨t, ht⟩ := RegularMono.lift' _ _ this
      refine CommSq.HasLift.mk' ⟨t, (cancel_mono f).1 ?_, ht⟩
      simp only [Arrow.mk_hom, Arrow.homMk'_left, Category.assoc, ht, sq.w])

theorem isIso_of_regularMono_of_epi (f : X ⟶ Y) [RegularMono f] [Epi f] : IsIso f :=
  isIso_of_epi_of_strongMono _

section

variable (C)

class RegularMonoCategory where
  /-- Every monomorphism is a regular monomorphism -/
  regularMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], RegularMono f

end

def regularMonoOfMono [RegularMonoCategory C] (f : X ⟶ Y) [Mono f] : RegularMono f :=
  RegularMonoCategory.regularMonoOfMono _

instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
    RegularMonoCategory C where
  regularMonoOfMono f _ := by
    haveI := isSplitMono_of_mono f
    infer_instance

instance (priority := 100) strongMonoCategory_of_regularMonoCategory [RegularMonoCategory C] :
    StrongMonoCategory C where
  strongMono_of_mono f _ := by
    haveI := regularMonoOfMono f
    infer_instance

class RegularEpi (f : X ⟶ Y) where
  /-- An object from `C` -/
  W : C -- Porting note: violates naming convention but what is better?
  /-- Two maps to the domain of `f` -/
  (left right : W ⟶ X)
  /-- `f` coequalizes the two maps -/
  w : left ≫ f = right ≫ f := by aesop_cat
  /-- `f` is the coequalizer -/
  isColimit : IsColimit (Cofork.ofπ f w)

attribute [reassoc] RegularEpi.w

instance (priority := 100) RegularEpi.epi (f : X ⟶ Y) [RegularEpi f] : Epi f :=
  epi_of_isColimit_cofork RegularEpi.isColimit

instance coequalizerRegular (g h : X ⟶ Y) [HasColimit (parallelPair g h)] :
    RegularEpi (coequalizer.π g h) where
  W := X
  left := g
  right := h
  w := coequalizer.condition g h
  isColimit :=
    Cofork.IsColimit.mk _ (fun s => colimit.desc _ s) (by simp) fun s m w => by
      apply coequalizer.hom_ext
      simp [← w]

noncomputable def regularEpiOfKernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := hc

instance (priority := 100) RegularEpi.ofSplitEpi (f : X ⟶ Y) [IsSplitEpi f] : RegularEpi f where
  W := X
  left := 𝟙 X
  right := f ≫ section_ f
  isColimit := isSplitEpiCoequalizes f

def RegularEpi.desc' {W : C} (f : X ⟶ Y) [RegularEpi f] (k : X ⟶ W)
    (h : (RegularEpi.left : RegularEpi.W f ⟶ X) ≫ k = RegularEpi.right ≫ k) :
    { l : Y ⟶ W // f ≫ l = k } :=
  Cofork.IsColimit.desc' RegularEpi.isColimit _ h

def regularOfIsPushoutSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [gr : RegularEpi g] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi h where
  W := gr.W
  left := gr.left ≫ f
  right := gr.right ≫ f
  w := by rw [Category.assoc, Category.assoc, comm]; simp only [← Category.assoc, eq_whisker gr.w]
  isColimit := by
    apply Cofork.IsColimit.mk' _ _
    intro s
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π := by
      rw [← Category.assoc, ← Category.assoc, s.condition]
    obtain ⟨l, hl⟩ := Cofork.IsColimit.desc' gr.isColimit (f ≫ Cofork.π s) l₁
    obtain ⟨p, hp₁, _⟩ := PushoutCocone.IsColimit.desc' t _ _ hl.symm
    refine ⟨p, hp₁, ?_⟩
    intro m w
    have z := w.trans hp₁.symm
    apply t.hom_ext
    apply (PushoutCocone.mk _ _ comm).coequalizer_ext
    · exact z
    · erw [← cancel_epi g, ← Category.assoc, ← eq_whisker comm]
      erw [← Category.assoc, ← eq_whisker comm]
      dsimp at z; simp only [Category.assoc, z]

def regularOfIsPushoutFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [RegularEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi k :=
  regularOfIsPushoutSndOfRegular comm.symm (PushoutCocone.flipIsColimit t)

instance (priority := 100) strongEpi_of_regularEpi (f : X ⟶ Y) [RegularEpi f] : StrongEpi f :=
  StrongEpi.mk'
    (by
      intro A B z hz u v sq
      have : (RegularEpi.left : RegularEpi.W f ⟶ X) ≫ u = RegularEpi.right ≫ u := by
        apply (cancel_mono z).1
        simp only [Category.assoc, sq.w, RegularEpi.w_assoc]
      obtain ⟨t, ht⟩ := RegularEpi.desc' f u this
      exact
        CommSq.HasLift.mk'
          ⟨t, ht,
            (cancel_epi f).1
              (by simp only [← Category.assoc, ht, ← sq.w, Arrow.mk_hom, Arrow.homMk'_right])⟩)

theorem isIso_of_regularEpi_of_mono (f : X ⟶ Y) [RegularEpi f] [Mono f] : IsIso f :=
  isIso_of_mono_of_strongEpi _

section

variable (C)

class RegularEpiCategory where
  /-- Everyone epimorphism is a regular epimorphism -/
  regularEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], RegularEpi f

end

def regularEpiOfEpi [RegularEpiCategory C] (f : X ⟶ Y) [Epi f] : RegularEpi f :=
  RegularEpiCategory.regularEpiOfEpi _

instance (priority := 100) regularEpiCategoryOfSplitEpiCategory [SplitEpiCategory C] :
    RegularEpiCategory C where
  regularEpiOfEpi f _ := by
    haveI := isSplitEpi_of_epi f
    infer_instance

instance (priority := 100) strongEpiCategory_of_regularEpiCategory [RegularEpiCategory C] :
    StrongEpiCategory C where
  strongEpi_of_epi f _ := by
    haveI := regularEpiOfEpi f
    infer_instance

end CategoryTheory
