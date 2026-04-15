/-
Extracted from CategoryTheory/DiscreteCategory.lean
Genuine: 23 | Conflates: 0 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Data.ULift

/-!
# Discrete categories

We define `Discrete α` as a structure containing a term `a : α` for any type `α`,
and use this type alias to provide a `SmallCategory` instance
whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `Discrete α` as `X = Y`,
one might define it as `PLift (X = Y)`.
In fact, to allow `Discrete α` to be a `SmallCategory`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ULift (PLift (X = Y))`.

`Discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`Discrete.functor f : Discrete I ⥤ C`.

Similarly, `Discrete.natTrans` and `Discrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

@[ext, aesop safe cases (rule_sets := [CategoryTheory])]
structure Discrete (α : Type u₁) where
  /-- A wrapper for promoting any type to a category,
  with the only morphisms being equalities. -/
  as : α

@[simp]
theorem Discrete.mk_as {α : Type u₁} (X : Discrete α) : Discrete.mk X.as = X := by
  rfl

@[simps]
def discreteEquiv {α : Type u₁} : Discrete α ≃ α where
  toFun := Discrete.as
  invFun := Discrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat

instance {α : Type u₁} [DecidableEq α] : DecidableEq (Discrete α) :=
  discreteEquiv.decidableEq

instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom X Y := ULift (PLift (X.as = Y.as))
  id _ := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g

namespace Discrete

variable {α : Type u₁}

instance [Inhabited α] : Inhabited (Discrete α) :=
  ⟨⟨default⟩⟩

instance [Subsingleton α] : Subsingleton (Discrete α) :=
  ⟨by aesop_cat⟩

instance instSubsingletonDiscreteHom (X Y : Discrete α) : Subsingleton (X ⟶ Y) :=
  show Subsingleton (ULift (PLift _)) from inferInstance

macro "discrete_cases" : tactic =>

  `(tactic| fail_if_no_progress casesm* Discrete _, (_ : Discrete _) ⟶ (_ : Discrete _), PLift _)

open Lean Elab Tactic in

def discreteCases : TacticM Unit := do
  evalTactic (← `(tactic| discrete_cases))

instance [Unique α] : Unique (Discrete α) :=
  Unique.mk' (Discrete α)

theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=
  i.down.down

protected abbrev eqToHom {X Y : Discrete α} (h : X.as = Y.as) : X ⟶ Y :=
  eqToHom (by aesop_cat)

protected abbrev eqToIso {X Y : Discrete α} (h : X.as = Y.as) : X ≅ Y :=
  eqToIso (by aesop_cat)

abbrev eqToHom' {a b : α} (h : a = b) : Discrete.mk a ⟶ Discrete.mk b :=
  Discrete.eqToHom h

abbrev eqToIso' {a b : α} (h : a = b) : Discrete.mk a ≅ Discrete.mk b :=
  Discrete.eqToIso h

@[simp]
theorem id_def (X : Discrete α) : ULift.up (PLift.up (Eq.refl X.as)) = 𝟙 X :=
  rfl

variable {C : Type u₂} [Category.{v₂} C]

instance {I : Type u₁} {i j : Discrete I} (f : i ⟶ j) : IsIso f :=
  ⟨⟨Discrete.eqToHom (eq_of_hom f).symm, by aesop_cat⟩⟩

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])]
  CategoryTheory.Discrete.discreteCases

def functor {I : Type u₁} (F : I → C) : Discrete I ⥤ C where
  obj := F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)

@[simp]
theorem functor_obj {I : Type u₁} (F : I → C) (i : I) :
    (Discrete.functor F).obj (Discrete.mk i) = F i :=
  rfl

@[simp]
theorem functor_map {I : Type u₁} (F : I → C) {i : Discrete I} (f : i ⟶ i) :
    (Discrete.functor F).map f = 𝟙 (F i.as) := by aesop_cat

alias CategoryTheory.FreeMonoidalCategory.discrete_functor_map_eq_id := functor_map

@[simp]
theorem functor_obj_eq_as {I : Type u₁} (F : I → C) (X : Discrete I) :
    (Discrete.functor F).obj X = F X.as :=
  rfl

alias CategoryTheory.FreeMonoidalCategory.discrete_functor_obj_eq_as := functor_obj_eq_as

@[simps!]
def functorComp {I : Type u₁} {J : Type u₁'} (f : J → C) (g : I → J) :
    Discrete.functor (f ∘ g) ≅ Discrete.functor (Discrete.mk ∘ g) ⋙ Discrete.functor f :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simps]
def natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ⟶ G.obj i) :
    F ⟶ G where
  app := f
  naturality := fun {X Y} ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

@[simps!]
def natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) :
    F ≅ G :=
  NatIso.ofComponents f fun ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp

instance {I : Type*} {F G : Discrete I ⥤ C} (f : ∀ i, F.obj i ⟶ G.obj i) [∀ i, IsIso (f i)] :
    IsIso (Discrete.natTrans f) := by
  change IsIso (Discrete.natIso (fun i => asIso (f i))).hom
  infer_instance

@[simp]
theorem natIso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i)
    (i : Discrete I) : (Discrete.natIso f).app i = f i := by aesop_cat

@[simp]
def natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor (F.obj ∘ Discrete.mk) :=
  natIso fun _ => Iso.refl _

@[simp]
def compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I → C) (G : C ⥤ D) :
    Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F) :=
  natIso fun _ => Iso.refl _

@[simps]
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discrete J where
  functor := Discrete.functor (Discrete.mk ∘ (e : I → J))
  inverse := Discrete.functor (Discrete.mk ∘ (e.symm : J → I))
  unitIso :=
    Discrete.natIso fun i => eqToIso (by aesop_cat)
  counitIso :=
    Discrete.natIso fun j => eqToIso (by aesop_cat)

@[simps]
def equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β) : α ≃ β where
  toFun := Discrete.as ∘ h.functor.obj ∘ Discrete.mk
  invFun := Discrete.as ∘ h.inverse.obj ∘ Discrete.mk
  left_inv a := by simpa using eq_of_hom (h.unitIso.app (Discrete.mk a)).2
  right_inv a := by simpa using eq_of_hom (h.counitIso.app (Discrete.mk a)).1

end Discrete

namespace Discrete

variable {J : Type v₁}

open Opposite

@[simps! functor_obj_as inverse_obj]
protected def opposite (α : Type u₁) : (Discrete α)ᵒᵖ ≌ Discrete α :=
  let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  { functor := F.leftOp
    inverse := F
    unitIso := NatIso.ofComponents fun ⟨_⟩ => Iso.refl _
    counitIso := Discrete.natIso fun ⟨_⟩ => Iso.refl _ }

variable {C : Type u₂} [Category.{v₂} C]

@[simp]
theorem functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) :
    F.map f = 𝟙 (F.obj j) := by
  have h : f = 𝟙 j := by aesop_cat
  rw [h]
  simp

end Discrete

@[simps]
def piEquivalenceFunctorDiscrete (J : Type u₂) (C : Type u₁) [Category.{v₁} C] :
    (J → C) ≌ (Discrete J ⥤ C) where
  functor :=
    { obj := fun F => Discrete.functor F
      map := fun f => Discrete.natTrans (fun j => f j.as) }
  inverse :=
    { obj := fun F j => F.obj ⟨j⟩
      map := fun f j => f.app ⟨j⟩ }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents (fun F => (NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      rintro ⟨x⟩ ⟨y⟩ f
      obtain rfl : x = y := Discrete.eq_of_hom f
      obtain rfl : f = 𝟙 _ := rfl
      simp))) (by aesop_cat)

class IsDiscrete (C : Type*) [Category C] : Prop where
  subsingleton (X Y : C) : Subsingleton (X ⟶ Y) := by infer_instance
  eq_of_hom {X Y : C} (f : X ⟶ Y) : X = Y

attribute [instance] IsDiscrete.subsingleton

lemma obj_ext_of_isDiscrete {C : Type*} [Category C] [IsDiscrete C]
    {X Y : C} (f : X ⟶ Y) : X = Y := IsDiscrete.eq_of_hom f

instance Discrete.isDiscrete (C : Type*) : IsDiscrete (Discrete C) where
  eq_of_hom := by rintro ⟨_⟩ ⟨_⟩ ⟨⟨rfl⟩⟩; rfl

instance (C : Type*) [Category C] [IsDiscrete C] : IsDiscrete Cᵒᵖ where
  eq_of_hom := by
    rintro ⟨_⟩ ⟨_⟩ ⟨f⟩
    obtain rfl := obj_ext_of_isDiscrete f
    rfl

end CategoryTheory
