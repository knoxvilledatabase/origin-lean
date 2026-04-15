/-
Extracted from CategoryTheory/Limits/Pi.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ Pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have limits for each of `F ⋙ Pi.eval C i`, we can produce a
   `HasLimit F` instance
-/

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.pi

universe v₁ v₂ u₁ u₂

variable {I : Type v₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

variable {J : Type v₁} [SmallCategory J]

variable {F : J ⥤ ∀ i, C i}

def coneCompEval (c : Cone F) (i : I) : Cone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }

def coconeCompEval (c : Cocone F) (i : I) : Cocone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }

def coneOfConeCompEval (c : ∀ i, Cone (F ⋙ Pi.eval C i)) : Cone F where
  pt i := (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).π.naturality f }

def coconeOfCoconeCompEval (c : ∀ i, Cocone (F ⋙ Pi.eval C i)) : Cocone F where
  pt i := (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).ι.naturality f }

def coneOfConeEvalIsLimit {c : ∀ i, Cone (F ⋙ Pi.eval C i)} (P : ∀ i, IsLimit (c i)) :
    IsLimit (coneOfConeCompEval c) where
  lift s i := (P i).lift (coneCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coneCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (w j) i

def coconeOfCoconeEvalIsColimit {c : ∀ i, Cocone (F ⋙ Pi.eval C i)} (P : ∀ i, IsColimit (c i)) :
    IsColimit (coconeOfCoconeCompEval c) where
  desc s i := (P i).desc (coconeCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coconeCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (w j) i

section

variable [∀ i, HasLimit (F ⋙ Pi.eval C i)]

theorem hasLimit_of_hasLimit_comp_eval : HasLimit F :=
  HasLimit.mk
    { cone := coneOfConeCompEval fun _ => limit.cone _
      isLimit := coneOfConeEvalIsLimit fun _ => limit.isLimit _ }

end

section

variable [∀ i, HasColimit (F ⋙ Pi.eval C i)]

theorem hasColimit_of_hasColimit_comp_eval : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfCoconeCompEval fun _ => colimit.cocone _
      isColimit := coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _ }

end

/-!
As an example, we can use this to construct particular shapes of limits
in a category of indexed families.

With the addition of
`import CategoryTheory.Limits.Shapes.Types`
we can use:
```
attribute [local instance] hasLimit_of_hasLimit_comp_eval
example : hasBinaryProducts (I → Type v₁) := ⟨by infer_instance⟩
```
-/

end CategoryTheory.pi
