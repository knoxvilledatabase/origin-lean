/-
Extracted from CategoryTheory/Sums/Basic.lean
Genuine: 12 | Conflates: 0 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.CategoryTheory.Equivalence

noncomputable section

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_`      : the functor `C ⥤ C ⊕ D`
* `inr_`      : the functor `D ⥤ C ⊕ D`
* `swap`      : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/

namespace CategoryTheory

universe v₁ u₁

open Sum

section

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

instance sum : Category.{v₁} (C ⊕ D) where
  Hom X Y :=
    match X, Y with
    | inl X, inl Y => X ⟶ Y
    | inl _, inr _ => PEmpty
    | inr _, inl _ => PEmpty
    | inr X, inr Y => X ⟶ Y
  id X :=
    match X with
    | inl X => 𝟙 X
    | inr X => 𝟙 X
  comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl _, inl _, inl _, f, g => f ≫ g
    | inr _, inr _, inr _, f, g => f ≫ g
  assoc {W X Y Z} f g h :=
    match X, Y, Z, W with
    | inl _, inl _, inl _, inl _ => Category.assoc f g h
    | inr _, inr _, inr _, inr _ => Category.assoc f g h

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
theorem hom_inl_inr_false {X : C} {Y : D} (f : Sum.inl X ⟶ Sum.inr Y) : False := by
  cases f

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
theorem hom_inr_inl_false {X : C} {Y : D} (f : Sum.inr X ⟶ Sum.inl Y) : False := by
  cases f

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₁) [Category.{v₁} D]

@[simps]
def inl_ : C ⥤ C ⊕ D where
  obj X := inl X
  map {_ _} f := f

@[simps]
def inr_ : D ⥤ C ⊕ D where
  obj X := inr X
  map {_ _} f := f

def swap : C ⊕ D ⥤ D ⊕ C where
  obj X :=
    match X with
    | inl X => inr X
    | inr X => inl X
  map := @fun X Y f =>
    match X, Y, f with
    | inl _, inl _, f => f
    | inr _, inr _, f => f
  map_comp := fun {X} {Y} {Z} _ _ =>
    match X, Y, Z with
    | inl X, inl Y, inl Z => by rfl
    | inr X, inr Y, inr Z => by rfl

namespace Swap

@[simps functor inverse]
def equivalence : C ⊕ D ≌ D ⊕ C where
  functor := swap C D
  inverse := swap D C
  unitIso := NatIso.ofComponents (by rintro (_|_) <;> exact Iso.refl _)
  counitIso := NatIso.ofComponents (by rintro (_|_) <;> exact Iso.refl _)

instance isEquivalence : (swap C D).IsEquivalence :=
  (by infer_instance : (equivalence C D).functor.IsEquivalence)

def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C ⊕ D) :=
  (equivalence C D).unitIso.symm

end Swap

end Sum

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₁} [Category.{v₁} B] {C : Type u₁}
  [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]

namespace Functor

def sum (F : A ⥤ B) (G : C ⥤ D) : A ⊕ C ⥤ B ⊕ D where
  obj X :=
    match X with
    | inl X => inl (F.obj X)
    | inr X => inr (G.obj X)
  map {X Y} f :=
    match X, Y, f with
    | inl _, inl _, f => F.map f
    | inr _, inr _, f => G.map f
  map_id {X} := by cases X <;> (erw [Functor.map_id]; rfl)
  map_comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl X, inl Y, inl Z, f, g => by erw [F.map_comp]; rfl
    | inr X, inr Y, inr Z, f, g => by erw [G.map_comp]; rfl

def sum' (F : A ⥤ C) (G : B ⥤ C) : A ⊕ B ⥤ C where
  obj X :=
    match X with
    | inl X => F.obj X
    | inr X => G.obj X
  map {X Y} f :=
    match X, Y, f with
    | inl _, inl _, f => F.map f
    | inr _, inr _, f => G.map f
  map_id {X} := by cases X <;> erw [Functor.map_id]
  map_comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | inl _, inl _, inl _, f, g => by erw [F.map_comp]
    | inr _, inr _, inr _, f, g => by erw [G.map_comp]

@[simps!]
def inlCompSum' (F : A ⥤ C) (G : B ⥤ C) : Sum.inl_ A B ⋙ F.sum' G ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simps!]
def inrCompSum' (F : A ⥤ C) (G : B ⥤ C) : Sum.inr_ A B ⋙ F.sum' G ≅ G :=
  NatIso.ofComponents fun _ => Iso.refl _

end Functor

namespace NatTrans

def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f :=
    match X, Y, f with
    | inl X, inl Y, f => by erw [α.naturality]; rfl
    | inr X, inr Y, f => by erw [β.naturality]; rfl

end NatTrans

end CategoryTheory
