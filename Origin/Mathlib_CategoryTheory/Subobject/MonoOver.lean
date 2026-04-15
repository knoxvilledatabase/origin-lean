/-
Extracted from CategoryTheory/Subobject/MonoOver.lean
Genuine: 31 | Conflates: 0 | Dissolved: 0 | Infrastructure: 22
-/
import Origin.Core
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Monomorphisms over a fixed object

As preparation for defining `Subobject X`, we set up the theory for
`MonoOver X := { f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not yet a partial order.

`Subobject X` will be defined as the skeletalization of `MonoOver X`.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X`
* `def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y`
* `def «exists» [HasImages C] (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y`
and prove their basic properties and relationships.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

-/

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}

variable {D : Type u₂} [Category.{v₂} D]

def MonoOver (X : C) :=
  FullSubcategory fun f : Over X => Mono f.hom

instance (X : C) : Category (MonoOver X) :=
  FullSubcategory.category _

namespace MonoOver

@[simps]
def mk' {X A : C} (f : A ⟶ X) [hf : Mono f] : MonoOver X where
  obj := Over.mk f
  property := hf

def forget (X : C) : MonoOver X ⥤ Over X :=
  fullSubcategoryInclusion _

instance : CoeOut (MonoOver X) C where coe Y := Y.obj.left

@[simp]
theorem forget_obj_left {f} : ((forget X).obj f).left = (f : C) :=
  rfl

@[simp]
theorem mk'_coe' {X A : C} (f : A ⟶ X) [Mono f] : (mk' f : C) = A :=
  rfl

abbrev arrow (f : MonoOver X) : (f : C) ⟶ X :=
  ((forget X).obj f).hom

@[simp]
theorem mk'_arrow {X A : C} (f : A ⟶ X) [Mono f] : (mk' f).arrow = f :=
  rfl

@[simp]
theorem forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow :=
  rfl

def fullyFaithfulForget (X : C) : (forget X).FullyFaithful :=
  fullyFaithfulFullSubcategoryInclusion _

instance : (forget X).Full :=
  FullSubcategory.full _

instance : (forget X).Faithful :=
  FullSubcategory.faithful _

instance mono (f : MonoOver X) : Mono f.arrow :=
  f.property

instance isThin {X : C} : Quiver.IsThin (MonoOver X) := fun f g =>
  ⟨by
    intro h₁ h₂
    apply Over.OverMorphism.ext
    erw [← cancel_mono g.arrow, Over.w h₁, Over.w h₂]⟩

@[reassoc]
theorem w {f g : MonoOver X} (k : f ⟶ g) : k.left ≫ g.arrow = f.arrow :=
  Over.w _

abbrev homMk {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left)
    (w : h ≫ g.arrow = f.arrow := by aesop_cat) : f ⟶ g :=
  Over.homMk h w

@[simps]
def isoMk {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left)
    (w : h.hom ≫ g.arrow = f.arrow := by aesop_cat) : f ≅ g where
  hom := homMk h.hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])

@[simp]
def mk'ArrowIso {X : C} (f : MonoOver X) : mk' f.arrow ≅ f :=
  isoMk (Iso.refl _)

@[simps]
def lift {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    MonoOver Y ⥤ MonoOver X where
  obj f := ⟨_, h f⟩
  map k := (MonoOver.forget Y ⋙ F).map k

def liftIso {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂) : lift F₁ h₁ ≅ lift F₂ h₂ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)

def liftComp {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂) :
    lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) fun f => h₂ ⟨_, h₁ f⟩ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

def liftId : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

@[simp]
theorem lift_comm (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    lift F h ⋙ MonoOver.forget X = MonoOver.forget Y ⋙ F :=
  rfl

@[simp]
theorem lift_obj_arrow {Y : D} (F : Over Y ⥤ Over X)
    (h : ∀ f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) (f : MonoOver Y) :
    ((lift F h).obj f).arrow = (F.obj ((forget Y).obj f)).hom :=
  rfl

def slice {A : C} {f : Over A}
    (h₁ : ∀ (g : MonoOver f),
      Mono ((Over.iteratedSliceEquiv f).functor.obj ((forget f).obj g)).hom)
    (h₂ : ∀ (g : MonoOver f.left),
      Mono ((Over.iteratedSliceEquiv f).inverse.obj ((forget f.left).obj g)).hom) :
    MonoOver f ≌ MonoOver f.left where
  functor := MonoOver.lift f.iteratedSliceEquiv.functor h₁
  inverse := MonoOver.lift f.iteratedSliceEquiv.inverse h₂
  unitIso :=
    MonoOver.liftId.symm ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.unitIso ≪≫ (MonoOver.liftComp _ _ _ _).symm
  counitIso :=
    MonoOver.liftComp _ _ _ _ ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.counitIso ≪≫ MonoOver.liftId

section Pullback

variable [HasPullbacks C]

def pullback (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X :=
  MonoOver.lift (Over.pullback f) (fun g => by
    haveI : Mono ((forget Y).obj g).hom := (inferInstance : Mono g.arrow)
    apply pullback.snd_of_mono)

def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm

def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.pullbackId ≪≫ liftId

@[simp]
theorem pullback_obj_left (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g : C) = Limits.pullback g.arrow f :=
  rfl

@[simp]
theorem pullback_obj_arrow (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g).arrow = pullback.snd _ _ :=
  rfl

end Pullback

section Map

def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y :=
  lift (Over.map f) fun g => mono_comp g.arrow f

def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : map (f ≫ g) ≅ map f ⋙ map g :=
  liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm

variable (X)

def mapId : map (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ (Over.mapId X) ≪≫ liftId

variable {X}

@[simp]
theorem map_obj_left (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g : C) = g.obj.left :=
  rfl

@[simp]
theorem map_obj_arrow (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g).arrow = g.arrow ≫ f :=
  rfl

instance full_map (f : X ⟶ Y) [Mono f] : Functor.Full (map f) where
  map_surjective {g h} e := by
    refine ⟨homMk e.left ?_, rfl⟩
    · rw [← cancel_mono f, assoc]
      apply w e

instance faithful_map (f : X ⟶ Y) [Mono f] : Functor.Faithful (map f) where

@[simps]
def mapIso {A B : C} (e : A ≅ B) : MonoOver A ≌ MonoOver B where
  functor := map e.hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)

section

variable (X)

@[simps]
def congr (e : C ≌ D) : MonoOver X ≌ MonoOver (e.functor.obj X) where
  functor :=
    lift (Over.post e.functor) fun f => by
      dsimp
      infer_instance
  inverse :=
    (lift (Over.post e.inverse) fun f => by
        dsimp
        infer_instance) ⋙
      (mapIso (e.unitIso.symm.app X)).functor
  unitIso := NatIso.ofComponents fun Y => isoMk (e.unitIso.app Y)
  counitIso := NatIso.ofComponents fun Y => isoMk (e.counitIso.app Y)

end

section

variable [HasPullbacks C]

def mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful (fullyFaithfulForget X) (fullyFaithfulForget Y)
    (Iso.refl _) (Iso.refl _)

def pullbackMapSelf (f : X ⟶ Y) [Mono f] : map f ⋙ pullback f ≅ 𝟭 _ :=
  (asIso (MonoOver.mapPullbackAdj f).unit).symm

end

end Map

section Image

variable (f : X ⟶ Y) [HasImage f]

def imageMonoOver (f : X ⟶ Y) [HasImage f] : MonoOver Y :=
  MonoOver.mk' (image.ι f)

@[simp]
theorem imageMonoOver_arrow (f : X ⟶ Y) [HasImage f] : (imageMonoOver f).arrow = image.ι f :=
  rfl

end Image

section Image

variable [HasImages C]

@[simps]
def image : Over X ⥤ MonoOver X where
  obj f := imageMonoOver f.hom
  map {f g} k := by
    apply (forget X).preimage _
    apply Over.homMk _ _
    · exact
        image.lift
          { I := Limits.image _
            m := image.ι g.hom
            e := k.left ≫ factorThruImage g.hom }
    · apply image.lift_fac

def imageForgetAdj : image ⊣ forget X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun f g =>
        { toFun := fun k => by
            apply Over.homMk (factorThruImage f.hom ≫ k.left) _
            change (factorThruImage f.hom ≫ k.left) ≫ _ = f.hom
            rw [assoc, Over.w k]
            apply image.fac
          invFun := fun k => by
            refine Over.homMk ?_ ?_
            · exact
                image.lift
                  { I := g.obj.left
                    m := g.arrow
                    e := k.left
                    fac := Over.w k }
            · apply image.lift_fac
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun k => by
            ext1
            change factorThruImage _ ≫ image.lift _ = _
            rw [← cancel_mono g.arrow, assoc, image.lift_fac, image.fac f.hom]
            exact (Over.w k).symm } }

instance : (forget X).IsRightAdjoint :=
  ⟨_, ⟨imageForgetAdj⟩⟩

instance reflective : Reflective (forget X) where
  adj := imageForgetAdj

def forgetImage : forget X ⋙ image ≅ 𝟭 (MonoOver X) :=
  asIso (Adjunction.counit imageForgetAdj)

end Image

section Exists

variable [HasImages C]

def «exists» (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y :=
  forget _ ⋙ Over.map f ⋙ image

instance faithful_exists (f : X ⟶ Y) : Functor.Faithful («exists» f) where

def existsIsoMap (f : X ⟶ Y) [Mono f] : «exists» f ≅ map f :=
  NatIso.ofComponents (by
    intro Z
    suffices (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z) by
      apply (forget _).preimageIso this
    apply Over.isoMk _ _
    · apply imageMonoIsoSource (Z.arrow ≫ f)
    · apply imageMonoIsoSource_hom_self)

def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  ((Over.mapPullbackAdj f).comp imageForgetAdj).restrictFullyFaithful
    (fullyFaithfulForget X) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end Exists

end MonoOver

end CategoryTheory
