/-
Extracted from CategoryTheory/Skeletal.lean
Genuine: 31 of 46 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Thin

/-!
# Skeleton of a category

Define skeletal categories as categories in which any two isomorphic objects are equal.

Construct the skeleton of an arbitrary category by taking isomorphism classes, and show it is a
skeleton of the original category.

In addition, construct the skeleton of a thin category as a partial ordering, and (noncomputably)
show it is a skeleton of the original category. The advantage of this special case being handled
separately is that lemmas and definitions about orderings can be used directly, for example for the
subobject lattice. In addition, some of the commutative diagrams about the functors commute
definitionally on the nose which is convenient in practice.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category

variable (C : Type u₁) [Category.{v₁} C]

variable (D : Type u₂) [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

def Skeletal : Prop :=
  ∀ ⦃X Y : C⦄, IsIsomorphic X Y → X = Y

structure IsSkeletonOf (F : D ⥤ C) : Prop where
  /-- The category `D` has isomorphic objects equal -/
  skel : Skeletal D
  /-- The functor `F` is an equivalence -/
  eqv : F.IsEquivalence := by infer_instance

attribute [local instance] isIsomorphicSetoid

variable {C D}

theorem Functor.eq_of_iso {F₁ F₂ : D ⥤ C} [Quiver.IsThin C] (hC : Skeletal C) (hF : F₁ ≅ F₂) :
    F₁ = F₂ :=
  Functor.ext (fun X => hC ⟨hF.app X⟩) fun _ _ _ => Subsingleton.elim _ _

theorem functor_skeletal [Quiver.IsThin C] (hC : Skeletal C) : Skeletal (D ⥤ C) := fun _ _ h =>
  h.elim (Functor.eq_of_iso hC)

variable (C D)

def Skeleton : Type u₁ := InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out

instance [Inhabited C] : Inhabited (Skeleton C) :=
  ⟨⟦default⟧⟩

noncomputable instance : Category (Skeleton C) := by
  apply InducedCategory.category

noncomputable instance {α} [CoeSort C α] : CoeSort (Skeleton C) α :=
  inferInstanceAs (CoeSort (InducedCategory _ _) _)

@[simps!]
noncomputable def fromSkeleton : Skeleton C ⥤ C :=
  inducedFunctor _

noncomputable instance : (fromSkeleton C).Full := by
  apply InducedCategory.full

noncomputable instance : (fromSkeleton C).Faithful := by
  apply InducedCategory.faithful

instance : (fromSkeleton C).EssSurj where mem_essImage X := ⟨Quotient.mk' X, Quotient.mk_out X⟩

noncomputable instance fromSkeleton.isEquivalence : (fromSkeleton C).IsEquivalence where

variable {C}

abbrev toSkeleton (X : C) : Skeleton C := ⟦X⟧

noncomputable def preCounitIso (X : C) : (fromSkeleton C).obj (toSkeleton X) ≅ X :=
  Nonempty.some (Quotient.mk_out X)

variable (C)

@[simps] noncomputable def toSkeletonFunctor : C ⥤ Skeleton C where
  obj := toSkeleton
  map {X Y} f := by apply (preCounitIso X).hom ≫ f ≫ (preCounitIso Y).inv
  map_id _ := by aesop
  map_comp _ _ := by change _ = CategoryStruct.comp (obj := C) _ _; simp

@[simps] noncomputable def skeletonEquivalence : Skeleton C ≌ C where
  functor := fromSkeleton C
  inverse := toSkeletonFunctor C
  unitIso := NatIso.ofComponents
    (fun X ↦ InducedCategory.isoMk (Nonempty.some <| Quotient.mk_out X.out).symm)
    fun _ ↦ .symm <| Iso.inv_hom_id_assoc _ _
  counitIso := NatIso.ofComponents preCounitIso
  functor_unitIso_comp _ := Iso.inv_hom_id _

theorem skeleton_skeletal : Skeletal (Skeleton C) := by
  rintro X Y ⟨h⟩
  have : X.out ≈ Y.out := ⟨(fromSkeleton C).mapIso h⟩
  simpa using Quotient.sound this

lemma skeleton_isSkeleton : IsSkeletonOf C (Skeleton C) (fromSkeleton C) where
  skel := skeleton_skeletal C
  eqv := fromSkeleton.isEquivalence C

section

variable {C D}

noncomputable def Equivalence.skeletonEquiv (e : C ≌ D) : Skeleton C ≃ Skeleton D :=
  let f := ((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm
  { toFun := f.functor.obj
    invFun := f.inverse.obj
    left_inv := fun X => skeleton_skeletal C ⟨(f.unitIso.app X).symm⟩
    right_inv := fun Y => skeleton_skeletal D ⟨f.counitIso.app Y⟩ }

end

def ThinSkeleton : Type u₁ :=
  Quotient (isIsomorphicSetoid C)

instance inhabitedThinSkeleton [Inhabited C] : Inhabited (ThinSkeleton C) :=
  ⟨@Quotient.mk' C (isIsomorphicSetoid C) default⟩

instance ThinSkeleton.preorder : Preorder (ThinSkeleton C) where
  le :=
    @Quotient.lift₂ C C _ (isIsomorphicSetoid C) (isIsomorphicSetoid C)
      (fun X Y => Nonempty (X ⟶ Y))
        (by
          rintro _ _ _ _ ⟨i₁⟩ ⟨i₂⟩
          exact
            propext
              ⟨Nonempty.map fun f => i₁.inv ≫ f ≫ i₂.hom,
                Nonempty.map fun f => i₁.hom ≫ f ≫ i₂.inv⟩)
  le_refl := by
    refine Quotient.ind fun a => ?_
    exact ⟨𝟙 _⟩
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Nonempty.map2 (· ≫ ·)

@[simps]
def toThinSkeleton : C ⥤ ThinSkeleton C where
  obj := @Quotient.mk' C _
  map f := homOfLE (Nonempty.intro f)

/-!
The constructions here are intended to be used when the category `C` is thin, even though
some of the statements can be shown without this assumption.
-/

namespace ThinSkeleton

instance thin : Quiver.IsThin (ThinSkeleton C) := fun _ _ =>
  ⟨by
    rintro ⟨⟨f₁⟩⟩ ⟨⟨_⟩⟩
    rfl⟩

variable {C} {D}

@[simps]
def map (F : C ⥤ D) : ThinSkeleton C ⥤ ThinSkeleton D where
  obj := Quotient.map F.obj fun _ _ ⟨hX⟩ => ⟨F.mapIso hX⟩
  map {X} {Y} := Quotient.recOnSubsingleton₂ X Y fun _ _ k => homOfLE (k.le.elim fun t => ⟨F.map t⟩)

theorem comp_toThinSkeleton (F : C ⥤ D) : F ⋙ toThinSkeleton D = toThinSkeleton C ⋙ map F :=
  rfl

def mapNatTrans {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : map F₁ ⟶ map F₂ where
  app X := Quotient.recOnSubsingleton X fun x => ⟨⟨⟨k.app x⟩⟩⟩

def map₂ObjMap (F : C ⥤ D ⥤ E) : ThinSkeleton C → ThinSkeleton D → ThinSkeleton E :=
  fun x y =>
    @Quotient.map₂ C D (isIsomorphicSetoid C) (isIsomorphicSetoid D) E (isIsomorphicSetoid E)
      (fun X Y => (F.obj X).obj Y)
          (fun X₁ _ ⟨hX⟩ _ Y₂ ⟨hY⟩ => ⟨(F.obj X₁).mapIso hY ≪≫ (F.mapIso hX).app Y₂⟩) x y

def map₂Functor (F : C ⥤ D ⥤ E) : ThinSkeleton C → ThinSkeleton D ⥤ ThinSkeleton E :=
  fun x =>
    { obj := fun y => map₂ObjMap F x y
      map := fun {y₁} {y₂} => @Quotient.recOnSubsingleton C (isIsomorphicSetoid C)
        (fun x => (y₁ ⟶ y₂) → (map₂ObjMap F x y₁ ⟶ map₂ObjMap F x y₂)) _ x fun X
          => Quotient.recOnSubsingleton₂ y₁ y₂ fun _ _ hY =>
            homOfLE (hY.le.elim fun g => ⟨(F.obj X).map g⟩) }

def map₂NatTrans (F : C ⥤ D ⥤ E) : {x₁ x₂ : ThinSkeleton C} → (x₁ ⟶ x₂) →
    (map₂Functor F x₁ ⟶ map₂Functor F x₂) := fun {x₁} {x₂} =>
  @Quotient.recOnSubsingleton₂ C C (isIsomorphicSetoid C) (isIsomorphicSetoid C)
    (fun x x' : ThinSkeleton C => (x ⟶ x') → (map₂Functor F x ⟶ map₂Functor F x')) _ x₁ x₂
    (fun X₁ X₂ f => { app := fun y =>
      Quotient.recOnSubsingleton y fun Y => homOfLE (f.le.elim fun f' => ⟨(F.map f').app Y⟩) })

@[simps]
def map₂ (F : C ⥤ D ⥤ E) : ThinSkeleton C ⥤ ThinSkeleton D ⥤ ThinSkeleton E where
  obj := map₂Functor F
  map := map₂NatTrans F

variable (C)

section

variable [Quiver.IsThin C]

instance toThinSkeleton_faithful : (toThinSkeleton C).Faithful where

@[simps]
noncomputable def fromThinSkeleton : ThinSkeleton C ⥤ C where
  obj := Quotient.out
  map {x} {y} :=
    Quotient.recOnSubsingleton₂ x y fun X Y f =>
      (Nonempty.some (Quotient.mk_out X)).hom ≫ f.le.some ≫ (Nonempty.some (Quotient.mk_out Y)).inv

noncomputable def equivalence : ThinSkeleton C ≌ C where
  functor := fromThinSkeleton C
  inverse := toThinSkeleton C
  counitIso := NatIso.ofComponents fun X => Nonempty.some (Quotient.mk_out X)
  unitIso := NatIso.ofComponents fun x => Quotient.recOnSubsingleton x fun X =>
    eqToIso (Quotient.sound ⟨(Nonempty.some (Quotient.mk_out X)).symm⟩)

noncomputable instance fromThinSkeleton_isEquivalence : (fromThinSkeleton C).IsEquivalence :=
  (equivalence C).isEquivalence_functor

variable {C}

theorem equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
  ⟨iso_of_both_ways f g⟩

instance thinSkeletonPartialOrder : PartialOrder (ThinSkeleton C) :=
  { CategoryTheory.ThinSkeleton.preorder C with
    le_antisymm :=
      Quotient.ind₂
        (by
          rintro _ _ ⟨f⟩ ⟨g⟩
          apply Quotient.sound (equiv_of_both_ways f g)) }

theorem skeletal : Skeletal (ThinSkeleton C) := fun X Y =>
  Quotient.inductionOn₂ X Y fun _ _ h => h.elim fun i => i.1.le.antisymm i.2.le

theorem map_comp_eq (F : E ⥤ D) (G : D ⥤ C) : map (F ⋙ G) = map F ⋙ map G :=
  Functor.eq_of_iso skeletal <|
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

theorem map_id_eq : map (𝟭 C) = 𝟭 (ThinSkeleton C) :=
  Functor.eq_of_iso skeletal <|
    NatIso.ofComponents fun X => Quotient.recOnSubsingleton X fun _ => Iso.refl _

theorem map_iso_eq {F₁ F₂ : D ⥤ C} (h : F₁ ≅ F₂) : map F₁ = map F₂ :=
  Functor.eq_of_iso skeletal
    { hom := mapNatTrans h.hom
      inv := mapNatTrans h.inv }

lemma thinSkeleton_isSkeleton : IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C) where
  skel := skeletal

instance isSkeletonOfInhabited :
    Inhabited (IsSkeletonOf C (ThinSkeleton C) (fromThinSkeleton C)) :=
  ⟨thinSkeleton_isSkeleton⟩

end

variable {C}

def lowerAdjunction (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R) :
    ThinSkeleton.map L ⊣ ThinSkeleton.map R where
  unit :=
    { app := fun X => by
        letI := isIsomorphicSetoid C
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.unit.app x⟩ }
      -- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
  counit :=
    { app := fun X => by
        letI := isIsomorphicSetoid D
        exact Quotient.recOnSubsingleton X fun x => homOfLE ⟨h.counit.app x⟩ }

end ThinSkeleton

open ThinSkeleton

section

variable {C} {α : Type*} [PartialOrder α]

noncomputable def Equivalence.thinSkeletonOrderIso [Quiver.IsThin C] (e : C ≌ α) :
    ThinSkeleton C ≃o α :=
  ((ThinSkeleton.equivalence C).trans e).toOrderIso

end

end CategoryTheory
