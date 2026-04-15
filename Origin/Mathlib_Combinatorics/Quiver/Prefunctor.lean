/-
Extracted from Combinatorics/Quiver/Prefunctor.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Combinatorics.Quiver.Basic

/-!
# Morphisms of quivers
-/

universe v₁ v₂ u u₁ u₂

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : V → W
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

namespace Prefunctor

lemma mk_obj {V W : Type*} [Quiver V] [Quiver W] {obj : V → W} {map} {X : V} :
    (Prefunctor.mk obj map).obj X = obj X := rfl

lemma mk_map {V W : Type*} [Quiver V] [Quiver W] {obj : V → W} {map} {X Y : V} {f : X ⟶ Y} :
    (Prefunctor.mk obj map).map f = map f := rfl

@[ext (iff := false)]
theorem ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
    (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y : V) (f : X ⟶ Y),
      F.map f = Eq.recOn (h_obj Y).symm (Eq.recOn (h_obj X).symm (G.map f))) : F = G := by
  obtain ⟨F_obj, _⟩ := F
  obtain ⟨G_obj, _⟩ := G
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f

@[simps]
def id (V : Type*) [Quiver V] : Prefunctor V V where
  obj := fun X => X
  map f := f

instance (V : Type*) [Quiver V] : Inhabited (Prefunctor V V) :=
  ⟨id V⟩

@[simps]
def comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
    (F : Prefunctor U V) (G : Prefunctor V W) : Prefunctor U W where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

@[simp]
theorem comp_id {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    F.comp (id _) = F := rfl

@[simp]
theorem id_comp {U V : Type*} [Quiver U] [Quiver V] (F : Prefunctor U V) :
    (id _).comp F = F := rfl

@[simp]
theorem comp_assoc {U V W Z : Type*} [Quiver U] [Quiver V] [Quiver W] [Quiver Z]
    (F : Prefunctor U V) (G : Prefunctor V W) (H : Prefunctor W Z) :
    (F.comp G).comp H = F.comp (G.comp H) :=
  rfl

infixl:50 " ⥤q " => Prefunctor

infixl:60 " ⋙q " => Prefunctor.comp

notation "𝟭q" => id

theorem congr_map {U V : Type*} [Quiver U] [Quiver V] (F : U ⥤q V) {X Y : U} {f g : X ⟶ Y}
    (h : f = g) : F.map f = F.map g := by
  rw [h]

end Prefunctor
