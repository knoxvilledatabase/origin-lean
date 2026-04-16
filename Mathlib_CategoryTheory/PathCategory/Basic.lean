/-
Extracted from CategoryTheory/PathCategory/Basic.lean
Genuine: 21 | Conflates: 0 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Quotient
import Mathlib.Combinatorics.Quiver.Path

noncomputable section

/-!
# The category paths on a quiver.
When `C` is a quiver, `paths C` is the category of paths.

## When the quiver is itself a category
We provide `path_composition : paths C ⥤ C`.

We check that the quotient of the path category of a category by the canonical relation
(paths are related if they compose to the same path) is equivalent to the original category.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

def Paths (V : Type u₁) : Type u₁ := V

instance (V : Type u₁) [Inhabited V] : Inhabited (Paths V) := ⟨(default : V)⟩

variable (V : Type u₁) [Quiver.{v₁ + 1} V]

namespace Paths

instance categoryPaths : Category.{max u₁ v₁} (Paths V) where
  Hom := fun X Y : V => Quiver.Path X Y
  id _ := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g

variable {V}

@[simps]
def of : V ⥤q Paths V where
  obj X := X
  map f := f.toPath

lemma induction_fixed_source {a : Paths V} (P : ∀ {b : Paths V}, (a ⟶ b) → Prop)
    (id : P (𝟙 a))
    (comp : ∀ {u v : V} (p : a ⟶ of.obj u) (q : u ⟶ v), P p → P (p ≫ of.map q)) :
    ∀ {b : Paths V} (f : a ⟶ b), P f := by
  intro _ f
  induction f with
  | nil => exact id
  | cons _ w h => exact comp _ w h

lemma induction_fixed_target {b : Paths V} (P : ∀ {a : Paths V}, (a ⟶ b) → Prop)
    (id : P (𝟙 b))
    (comp : ∀ {u v : V} (p : of.obj v ⟶ b) (q : u ⟶ v), P p → P (of.map q ≫ p)) :
    ∀ {a : Paths V} (f : a ⟶ b), P f := by
  intro a f
  generalize h : f.length = k
  induction k generalizing f a with
  | zero => cases f with
    | nil => exact id
    | cons _ _ => simp at h
  | succ k h' =>
    obtain ⟨c, f, q, hq, rfl⟩ := f.eq_toPath_comp_of_length_eq_succ h
    exact comp _ _ (h' _ hq)

lemma induction (P : ∀ {a b : Paths V}, (a ⟶ b) → Prop)
    (id : ∀ {v : V}, P (𝟙 (of.obj v)))
    (comp : ∀ {u v w : V} (p : of.obj u ⟶ of.obj v) (q : v ⟶ w), P p → P (p ≫ of.map q)) :
    ∀ {a b : Paths V} (f : a ⟶ b), P f :=
  fun {_} ↦ induction_fixed_source _ id comp

lemma induction' (P : ∀ {a b : Paths V}, (a ⟶ b) → Prop)
    (id : ∀ {v : V}, P (𝟙 (of.obj v)))
    (comp : ∀ {u v w : V} (p : u ⟶ v) (q : of.obj v ⟶ of.obj w), P q → P (of.map p ≫ q)) :
    ∀ {a b : Paths V} (f : a ⟶ b), P f := by
  intro a b
  revert a
  exact induction_fixed_target (P := fun f ↦ P f) id (fun _ _ ↦ comp _ _)

attribute [local ext (iff := false)] Functor.ext

def lift {C} [Category C] (φ : V ⥤q C) : Paths V ⥤ C where
  obj := φ.obj
  map {X} {Y} f :=
    @Quiver.Path.rec V _ X (fun Y _ => φ.obj X ⟶ φ.obj Y) (𝟙 <| φ.obj X)
      (fun _ f ihp => ihp ≫ φ.map f) Y f
  map_id _ := rfl
  map_comp f g := by
    induction g with
    | nil =>
      rw [Category.comp_id]
      rfl
    | cons g' p ih =>
      have : f ≫ Quiver.Path.cons g' p = (f ≫ g').cons p := by apply Quiver.Path.comp_cons
      rw [this]
      simp only at ih ⊢
      rw [ih, Category.assoc]

@[simp]
theorem lift_nil {C} [Category C] (φ : V ⥤q C) (X : V) :
    (lift φ).map Quiver.Path.nil = 𝟙 (φ.obj X) := rfl

@[simp]
theorem lift_cons {C} [Category C] (φ : V ⥤q C) {X Y Z : V} (p : Quiver.Path X Y) (f : Y ⟶ Z) :
    (lift φ).map (p.cons f) = (lift φ).map p ≫ φ.map f := rfl

@[simp]
theorem lift_toPath {C} [Category C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y) :
    (lift φ).map f.toPath = φ.map f := by
  dsimp [Quiver.Hom.toPath, lift]
  simp

theorem lift_spec {C} [Category C] (φ : V ⥤q C) : of ⋙q (lift φ).toPrefunctor = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rcases φ with ⟨φo, φm⟩
    dsimp [lift, Quiver.Hom.toPath]
    simp only [Category.id_comp]

theorem lift_unique {C} [Category C] (φ : V ⥤q C) (Φ : Paths V ⥤ C)
    (hΦ : of ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  subst_vars
  fapply Functor.ext
  · rintro X
    rfl
  · rintro X Y f
    dsimp [lift]
    induction f with
    | nil =>
      simp only [Category.comp_id]
      apply Functor.map_id
    | cons p f' ih =>
      simp only [Category.comp_id, Category.id_comp] at ih ⊢
      -- Porting note: Had to do substitute `p.cons f'` and `f'.toPath` by their fully qualified
      -- versions in this `have` clause (elsewhere too).
      have : Φ.map (Quiver.Path.cons p f') = Φ.map p ≫ Φ.map (Quiver.Hom.toPath f') := by
        convert Functor.map_comp Φ p (Quiver.Hom.toPath f')
      rw [this, ih]

@[ext (iff := false)]
theorem ext_functor {C} [Category C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
    (h : ∀ (a b : V) (e : a ⟶ b), F.map e.toPath =
        eqToHom (congr_fun h_obj a) ≫ G.map e.toPath ≫ eqToHom (congr_fun h_obj.symm b)) :
    F = G := by
  fapply Functor.ext
  · intro X
    rw [h_obj]
  · intro X Y f
    induction' f with Y' Z' g e ih
    · erw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    · erw [F.map_comp g (Quiver.Hom.toPath e), G.map_comp g (Quiver.Hom.toPath e), ih, h]
      simp only [Category.id_comp, eqToHom_refl, eqToHom_trans_assoc, Category.assoc]

end Paths

variable (W : Type u₂) [Quiver.{v₂ + 1} W]

@[simp]
theorem Prefunctor.mapPath_comp' (F : V ⥤q W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.mapPath (f ≫ g) = (F.mapPath f).comp (F.mapPath g) :=
  Prefunctor.mapPath_comp _ _ _

end

section

variable {C : Type u₁} [Category.{v₁} C]

open Quiver

def composePath {X : C} : ∀ {Y : C} (_ : Path X Y), X ⟶ Y
  | _, .nil => 𝟙 X
  | _, .cons p e => composePath p ≫ e

@[simp] lemma composePath_nil {X : C} : composePath (Path.nil : Path X X) = 𝟙 X := rfl

@[simp] lemma composePath_cons {X Y Z : C} (p : Path X Y) (e : Y ⟶ Z) :
  composePath (p.cons e) = composePath p ≫ e := rfl

@[simp]
theorem composePath_toPath {X Y : C} (f : X ⟶ Y) : composePath f.toPath = f := Category.id_comp _

@[simp]
theorem composePath_comp {X Y Z : C} (f : Path X Y) (g : Path Y Z) :
    composePath (f.comp g) = composePath f ≫ composePath g := by
  induction' g with Y' Z' g e ih
  · simp
  · simp [ih]

@[simp]
theorem composePath_id {X : Paths C} : composePath (𝟙 X) = 𝟙 (id X : C) := rfl

@[simp]
theorem composePath_comp' {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    composePath (f ≫ g) = composePath f ≫ composePath g :=
  composePath_comp f g

variable (C)

@[simps]
def pathComposition : Paths C ⥤ C where
  obj X := X
  map f := composePath f

@[simp]
def pathsHomRel : HomRel (Paths C) := fun _ _ p q =>
  (pathComposition C).map p = (pathComposition C).map q

@[simps]
def toQuotientPaths : C ⥤ Quotient (pathsHomRel C) where
  obj X := Quotient.mk X
  map f := Quot.mk _ f.toPath
  map_id X := Quot.sound (Quotient.CompClosure.of _ _ _ (by simp))
  map_comp f g := Quot.sound (Quotient.CompClosure.of _ _ _ (by simp))

@[simps!]
def quotientPathsTo : Quotient (pathsHomRel C) ⥤ C :=
  Quotient.lift _ (pathComposition C) fun _ _ _ _ w => w

def quotientPathsEquiv : Quotient (pathsHomRel C) ≌ C where
  functor := quotientPathsTo C
  inverse := toQuotientPaths C
  unitIso :=
    NatIso.ofComponents
      (fun X => by cases X; rfl)
      (Quot.ind fun f => by
        apply Quot.sound
        apply Quotient.CompClosure.of
        simp [Category.comp_id, Category.id_comp, pathsHomRel])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp [Quot.liftOn_mk])
  functor_unitIso_comp X := by
    cases X
    simp only [pathsHomRel, pathComposition_obj, pathComposition_map, Functor.id_obj,
               quotientPathsTo_obj, Functor.comp_obj, toQuotientPaths_obj_as,
               NatIso.ofComponents_hom_app, Iso.refl_hom, quotientPathsTo_map, Category.comp_id]
    rfl

end

end CategoryTheory
