/-
Extracted from CategoryTheory/Category/Factorisation.lean
Genuine: 11 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The Factorisation Category of a Category

`Factorisation f` is the category containing as objects all factorisations of a morphism `f`.

We show that `Factorisation f` always has an initial and a terminal object.

TODO: Show that `Factorisation f` is isomorphic to a comma category in two ways.

TODO: Make `MonoFactorisation f` a special case of a `Factorisation f`.
-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

structure Factorisation {X Y : C} (f : X ⟶ Y) where
  /-- The midpoint of the factorisation. -/
  mid : C
  /-- The morphism into the factorisation midpoint. -/
  ι   : X ⟶ mid
  /-- The morphism out of the factorisation midpoint. -/
  π   : mid ⟶ Y
  /-- The factorisation condition. -/
  ι_π : ι ≫ π = f := by aesop_cat

attribute [simp] Factorisation.ι_π

namespace Factorisation

variable {X Y : C} {f : X ⟶ Y}

@[ext]
protected structure Hom (d e : Factorisation f) : Type (max u v) where
  /-- The morphism between the midpoints of the factorizations. -/
  h : d.mid ⟶ e.mid
  /-- The left commuting triangle of the factorization morphism. -/
  ι_h : d.ι ≫ h = e.ι := by aesop_cat
  /-- The right commuting triangle of the factorization morphism. -/
  h_π : h ≫ e.π = d.π := by aesop_cat

attribute [simp] Factorisation.Hom.ι_h Factorisation.Hom.h_π

@[simps]
protected def Hom.id (d : Factorisation f) : Factorisation.Hom d d where
  h := 𝟙 _

@[simps]
protected def Hom.comp {d₁ d₂ d₃ : Factorisation f}
    (f : Factorisation.Hom d₁ d₂) (g : Factorisation.Hom d₂ d₃) : Factorisation.Hom d₁ d₃ where
  h := f.h ≫ g.h
  ι_h := by rw [← Category.assoc, f.ι_h, g.ι_h]
  h_π := by rw [Category.assoc, g.h_π, f.h_π]

instance : Category.{max u v} (Factorisation f) where
  Hom d e := Factorisation.Hom d e
  id d := Factorisation.Hom.id d
  comp f g := Factorisation.Hom.comp f g

variable (d : Factorisation f)

@[simps]
protected def initial : Factorisation f where
  mid := X
  ι := 𝟙 _
  π := f

@[simps]
protected def initialHom (d : Factorisation f) :
    Factorisation.Hom (Factorisation.initial : Factorisation f) d where
  h := d.ι

instance : Unique ((Factorisation.initial : Factorisation f) ⟶ d) where
  default := Factorisation.initialHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.ι_h]

@[simps]
protected def terminal : Factorisation f where
  mid := Y
  ι := f
  π := 𝟙 _

@[simps]
protected def terminalHom (d : Factorisation f) :
    Factorisation.Hom d (Factorisation.terminal : Factorisation f) where
  h := d.π

instance : Unique (d ⟶ (Factorisation.terminal : Factorisation f)) where
  default := Factorisation.terminalHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.h_π]

open Limits

def IsInitial_initial : IsInitial (Factorisation.initial : Factorisation f) := IsInitial.ofUnique _

instance : HasInitial (Factorisation f) := Limits.hasInitial_of_unique Factorisation.initial

def IsTerminal_terminal : IsTerminal (Factorisation.terminal : Factorisation f) :=

IsTerminal.ofUnique _

instance : HasTerminal (Factorisation f) := Limits.hasTerminal_of_unique Factorisation.terminal

@[simps]
def forget : Factorisation f ⥤ C where
  obj := Factorisation.mid
  map f := f.h

end Factorisation

end CategoryTheory
