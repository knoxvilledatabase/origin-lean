/-
Extracted from CategoryTheory/Grothendieck.lean
Genuine: 26 of 36 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `Grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

`Grothendieck.functor` makes the Grothendieck construction into a functor from the functor category
`C ⥤ Cat` to the over category `Over C` in the category of categories.

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : f ⟶ (F.map (op β)).obj f'`.

## References

See also `CategoryTheory.Functor.Elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/

universe w u v u₁ v₁ u₂ v₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable {D : Type u₁} [Category.{v₁} D]

variable (F : C ⥤ Cat.{v₂, u₂})

structure Grothendieck where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F.obj base

namespace Grothendieck

variable {F}

structure Hom (X Y : Grothendieck F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the pushforward to the source fiber object to the target fiber object. -/
  fiber : (F.map base).obj X.fiber ⟶ Y.fiber

@[ext (iff := false)]
theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : eqToHom (by rw [w_base]) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  aesop_cat

def id (X : Grothendieck F) : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber])

instance (X : Grothendieck F) : Inhabited (Hom X X) :=
  ⟨id X⟩

def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber :=
    eqToHom (by erw [Functor.map_comp, Functor.comp_obj]) ≫ (F.map g.base).map f.fiber ≫ g.fiber

attribute [local simp] eqToHom_map

instance : Category (Grothendieck F) where
  Hom X Y := Grothendieck.Hom X Y
  id X := Grothendieck.id X
  comp := @fun _ _ _ f g => Grothendieck.comp f g
  comp_id := @fun X Y f => by
    dsimp; ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_id Y.base)) f.fiber]
      simp
  id_comp := @fun X Y f => by dsimp; ext <;> simp [comp, id]
  assoc := @fun W X Y Z f g h => by
    dsimp; ext
    · simp [comp, id]
    · dsimp [comp, id]
      rw [← NatIso.naturality_2 (eqToIso (F.map_comp _ _)) f.fiber]
      simp

@[simp]
theorem id_base (X : Grothendieck F) :
    Hom.base (𝟙 X) = 𝟙 X.base := by
  rfl

@[simp]
theorem id_fiber (X : Grothendieck F) :
    Hom.fiber (𝟙 X) = eqToHom (by erw [CategoryTheory.Functor.map_id, Functor.id_obj X.fiber]) :=
  rfl

@[simp]
theorem comp_base {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_fiber {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.fiber (f ≫ g) =
    eqToHom (by erw [Functor.map_comp, Functor.comp_obj]) ≫
    (F.map g.base).map f.fiber ≫ g.fiber :=
  rfl

theorem congr {X Y : Grothendieck F} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber := by
  subst h
  dsimp
  simp

lemma eqToHom_eq {X Y : Grothendieck F} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl), fiber := eqToHom (by subst hF; simp) } := by
  subst hF
  rfl

section

variable (F)

@[simps!]
def forget : Grothendieck F ⥤ C where
  obj X := X.1
  map := @fun _ _ f => f.1

end

section

variable {G : C ⥤ Cat}

@[simps!]
def map (α : F ⟶ G) : Grothendieck F ⥤ Grothendieck G where
  obj X :=
  { base := X.base
    fiber := (α.app X.base).obj X.fiber }
  map {X Y} f :=
  { base := f.base
    fiber := (eqToHom (α.naturality f.base).symm).app X.fiber ≫ (α.app Y.base).map f.fiber }
  map_id X := by simp only [Cat.eqToHom_app, id_fiber, eqToHom_map, eqToHom_trans]; rfl
  map_comp {X Y Z} f g := by
    dsimp
    congr 1
    simp only [comp_fiber f g, ← Category.assoc, Functor.map_comp, eqToHom_map]
    congr 1
    simp only [Cat.eqToHom_app, Cat.comp_obj, eqToHom_trans, eqToHom_map, Category.assoc]
    erw [Functor.congr_hom (α.naturality g.base).symm f.fiber]
    simp

theorem map_obj {α : F ⟶ G} (X : Grothendieck F) :
    (Grothendieck.map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl

theorem map_map {α : F ⟶ G} {X Y : Grothendieck F} {f : X ⟶ Y} :
    (Grothendieck.map α).map f =
    ⟨f.base, (eqToHom (α.naturality f.base).symm).app X.fiber ≫ (α.app Y.base).map f.fiber⟩ := rfl

theorem functor_comp_forget {α : F ⟶ G} :
    Grothendieck.map α ⋙ Grothendieck.forget G = Grothendieck.forget F := rfl

theorem map_id_eq : map (𝟙 F) = 𝟙 (Cat.of <| Grothendieck <| F) := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

def mapIdIso : map (𝟙 F) ≅ 𝟙 (Cat.of <| Grothendieck <| F) := eqToIso map_id_eq

variable {H : C ⥤ Cat}

theorem map_comp_eq (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, map_obj_base, NatTrans.comp_app, Cat.comp_obj, Cat.comp_map,
      eqToHom_refl, Functor.comp_map, Functor.map_comp, Category.comp_id, Category.id_comp]
    fapply Grothendieck.ext
    · rfl
    · simp

def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β := eqToIso (map_comp_eq α β)

variable (F)

@[simps]
def compAsSmallFunctorEquivalenceInverse :
    Grothendieck F ⥤ Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) where
  obj X := ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩

@[simps]
def compAsSmallFunctorEquivalenceFunctor :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ⥤ Grothendieck F where
  obj X := ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id _ := by apply Grothendieck.ext <;> simp
  map_comp _ _ := by apply Grothendieck.ext <;> simp [down_comp]

@[simps]
def compAsSmallFunctorEquivalence :
    Grothendieck (F ⋙ Cat.asSmallFunctor.{w}) ≌ Grothendieck F where
  functor := compAsSmallFunctorEquivalenceFunctor F
  inverse := compAsSmallFunctorEquivalenceInverse F
  counitIso := Iso.refl _
  unitIso := Iso.refl _

def mapWhiskerRightAsSmallFunctor (α : F ⟶ G) :
    map (whiskerRight α Cat.asSmallFunctor.{w}) ≅
    (compAsSmallFunctorEquivalence F).functor ⋙ map α ⋙
      (compAsSmallFunctorEquivalence G).inverse :=
  NatIso.ofComponents
    (fun X => Iso.refl _)
    (fun f => by
      fapply Grothendieck.ext
      · simp [compAsSmallFunctorEquivalenceInverse]
      · simp only [compAsSmallFunctorEquivalence_functor, compAsSmallFunctorEquivalence_inverse,
          Functor.comp_obj, compAsSmallFunctorEquivalenceInverse_obj_base, map_obj_base,
          compAsSmallFunctorEquivalenceFunctor_obj_base, Cat.asSmallFunctor_obj, Cat.of_α,
          Iso.refl_hom, Functor.comp_map, comp_base, id_base,
          compAsSmallFunctorEquivalenceInverse_map_base, map_map_base,
          compAsSmallFunctorEquivalenceFunctor_map_base, Cat.asSmallFunctor_map, map_obj_fiber,
          whiskerRight_app, AsSmall.down_obj, AsSmall.up_obj_down,
          compAsSmallFunctorEquivalenceInverse_obj_fiber,
          compAsSmallFunctorEquivalenceFunctor_obj_fiber, comp_fiber, map_map_fiber,
          AsSmall.down_map, down_comp, eqToHom_down, AsSmall.up_map_down, Functor.map_comp,
          eqToHom_map, id_fiber, Category.assoc, eqToHom_trans_assoc,
          compAsSmallFunctorEquivalenceInverse_map_fiber,
          compAsSmallFunctorEquivalenceFunctor_map_fiber, eqToHom_comp_iff, comp_eqToHom_iff]
        simp only [eqToHom_trans_assoc, Category.assoc, conj_eqToHom_iff_heq']
        rw [G.map_id]
        simp )

end

def functor {E : Cat.{v,u}} : (E ⥤ Cat.{v,u}) ⥤ Over (T := Cat.{v,u}) E where
  obj F := Over.mk (X := E) (Y := Cat.of (Grothendieck F)) (Grothendieck.forget F)
  map {_ _} α := Over.homMk (X:= E) (Grothendieck.map α) Grothendieck.functor_comp_forget
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    simp [Grothendieck.map_comp_eq α β]
    rfl

variable (G : C ⥤ Type w)

@[simps!]
def grothendieckTypeToCatFunctor : Grothendieck (G ⋙ typeToCat) ⥤ G.Elements where
  obj X := ⟨X.1, X.2.as⟩
  map f := ⟨f.1, f.2.1.1⟩

@[simps! obj_base obj_fiber_as map_base]
def grothendieckTypeToCatInverse : G.Elements ⥤ Grothendieck (G ⋙ typeToCat) where
  obj X := ⟨X.1, ⟨X.2⟩⟩
  map f := ⟨f.1, ⟨⟨f.2⟩⟩⟩

@[simps! functor_obj_fst functor_obj_snd functor_map_coe inverse_obj_base inverse_obj_fiber_as
  inverse_map_base unitIso_hom_app_base unitIso_hom_app_fiber unitIso_inv_app_base
  unitIso_inv_app_fiber counitIso_hom_app_coe counitIso_inv_app_coe]
def grothendieckTypeToCat : Grothendieck (G ⋙ typeToCat) ≌ G.Elements where
  functor := grothendieckTypeToCatFunctor G
  inverse := grothendieckTypeToCatInverse G
  unitIso :=
    NatIso.ofComponents
      (fun X => by
        rcases X with ⟨_, ⟨⟩⟩
        exact Iso.refl _)
      (by
        rintro ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ ⟨base, ⟨⟨f⟩⟩⟩
        dsimp at *
        simp
        rfl)
  counitIso :=
    NatIso.ofComponents
      (fun X => by
        cases X
        exact Iso.refl _)
      (by
        rintro ⟨⟩ ⟨⟩ ⟨f, e⟩
        dsimp at *
        simp
        rfl)
  functor_unitIso_comp := by
    rintro ⟨_, ⟨⟩⟩
    dsimp
    simp
    rfl

variable (F) in

@[simps]
def pre (G : D ⥤ C) : Grothendieck (G ⋙ F) ⥤ Grothendieck F where
  obj X := ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := Grothendieck.ext _ _ (G.map_id _) (by simp)
  map_comp f g := Grothendieck.ext _ _ (G.map_comp _ _) (by simp)

section FunctorFrom

variable {E : Type*} [Category E]

variable (F) in

@[simps obj map]
def ι (c : C) : F.obj c ⥤ Grothendieck F where
  obj d := ⟨c, d⟩
  map f := ⟨𝟙 _, eqToHom (by simp) ≫ f⟩
  map_id d := by
    dsimp
    congr
    simp only [Category.comp_id]
  map_comp f g := by
    apply Grothendieck.ext _ _ (by simp)
    simp only [comp_base, ← Category.assoc, eqToHom_trans, comp_fiber, Functor.map_comp,
      eqToHom_map]
    congr 1
    simp only [eqToHom_comp_iff, Category.assoc, eqToHom_trans_assoc]
    apply Functor.congr_hom (F.map_id _).symm

instance faithful_ι (c : C) : (ι F c).Faithful where
  map_injective f := by
    injection f with _ f
    rwa [cancel_epi] at f

@[simps]
def ιNatTrans {X Y : C} (f : X ⟶ Y) : ι F X ⟶ F.map f ⋙ ι F Y where
  app d := ⟨f, 𝟙 _⟩
  naturality _ _ _ := by
    simp only [ι, Functor.comp_obj, Functor.comp_map]
    exact Grothendieck.ext _ _ (by simp) (by simp [eqToHom_map])

variable (fib : ∀ c, F.obj c ⥤ E) (hom : ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ F.map f ⋙ fib c')

variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl))

variable (hom_comp : ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
  hom f ≫ whiskerLeft (F.map f) (hom g) ≫ eqToHom (by simp only [Functor.map_comp]; rfl))

@[simps]
def functorFrom : Grothendieck F ⥤ E where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (hom f.base).app X.fiber ≫ (fib Y.base).map f.fiber
  map_id X := by simp [hom_id]
  map_comp f g := by simp [hom_comp]

def ιCompFunctorFrom (c : C) : ι F c ⋙ (functorFrom fib hom hom_id hom_comp) ≅ fib c :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [hom_id])

end FunctorFrom

end Grothendieck

end CategoryTheory
