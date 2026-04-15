/-
Extracted from CategoryTheory/Monoidal/Action/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Actions from a monoidal category on a category

Given a monoidal category `C`, and a category `D`, we define a left action of
`C` on `D` as the data of an object `c ⊙ₗ d` of `D` for every
`c : C` and `d : D`, as well as the data required to turn `- ⊙ₗ -` into
a bifunctor, along with structure natural isomorphisms
`(- ⊗ -) ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -` and `𝟙_ C ⊙ₗ - ≅ -`, subject to coherence conditions.

We also define right actions, for these, the notation for the action of `c`
on `d` is `d ⊙ᵣ c`, and the structure isomorphisms are of the form
`- ⊙ᵣ (- ⊗ -) ≅ (- ⊙ᵣ -) ⊙ᵣ -` and `- ⊙ₗ 𝟙_ C ≅ -`.


## References
* [Janelidze, G, and Kelly, G.M., *A note on actions of a monoidal category*][JanelidzeKelly2001]

## TODOs/Projects
* Equivalence between actions of `C` on `D` and pseudofunctors from the
  classifying bicategory of `C` to `Cat`.
* Left/Right Modules in `D` over a monoid object in `C`.
  Equivalence with `Mod_` when `D` is `C`. Bimodules objects.
* Given a monad `M` on `C`, equivalence between `Algebra M`, and modules in `C`
  on `M.toMon : Mon (C ⥤ C)`.
* Canonical left action of `Type u` on `u`-small cocomplete categories via the
  copower.

-/

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category* C] [Category* D]

class MonoidalLeftActionStruct [MonoidalCategoryStruct C] where
  /-- The left action on objects. This is denoted `c ⊙ₗ d`. -/
  actionObj : C → D → D
  /-- The left action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.map f).app d`. This is denoted `f ⊵ₗ d`. -/
  actionHomLeft {c c' : C} (f : c ⟶ c') (d : D) :
    actionObj c d ⟶ actionObj c' d
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.obj c).map f`. This is denoted `c ⊴ₗ f`. -/
  actionHomRight (c : C) {d d' : D} (f : d ⟶ d') :
    actionObj c d ⟶ actionObj c d'
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    actionObj c d ⟶ actionObj c' d' := actionHomLeft f d ≫ actionHomRight c' g
  /-- The structural isomorphism `(c ⊗ c') ⊙ₗ d ≅ c ⊙ₗ (c' ⊙ₗ d)`. -/
  actionAssocIso (c c' : C) (d : D) :
    actionObj (c ⊗ c') d ≅ actionObj c (actionObj c' d)
  /-- The structural isomorphism between `𝟙_ C ⊙ₗ d` and `d`. -/
  actionUnitIso (d : D) : actionObj (𝟙_ C) d ≅ d

namespace MonoidalLeftAction

export MonoidalLeftActionStruct

  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso

    actionUnitIso)

scoped infixr:70 " ⊙ₗ " => MonoidalLeftActionStruct.actionObj

scoped infixr:81 " ⊵ₗ " => MonoidalLeftActionStruct.actionHomLeft

scoped infixr:81 " ⊴ₗ " => MonoidalLeftActionStruct.actionHomRight

scoped infixr:70 " ⊙ₗₘ " => MonoidalLeftActionStruct.actionHom

scoped notation "αₗ " => MonoidalLeftActionStruct.actionAssocIso

scoped notation "λₗ " => MonoidalLeftActionStruct.actionUnitIso

scoped notation "λₗ["J"]" => MonoidalLeftActionStruct.actionUnitIso (C := J)

end MonoidalLeftAction

open scoped MonoidalLeftAction in

class MonoidalLeftAction [MonoidalCategory C] extends
    MonoidalLeftActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
      f ⊙ₗₘ g = f ⊵ₗ d ≫ c' ⊴ₗ g := by
    cat_disch
  actionHomRight_id (c : C) (d : D) : c ⊴ₗ 𝟙 d = 𝟙 (c ⊙ₗ d) := by cat_disch
  id_actionHomLeft (c : C) (d : D) : 𝟙 c ⊵ₗ d = 𝟙 (c ⊙ₗ d) := by cat_disch
  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'')
      (g₁ : d ⟶ d') (g₂ : d' ⟶ d'') :
      (f₁ ≫ f₂) ⊙ₗₘ (g₁ ≫ g₂) = (f₁ ⊙ₗₘ g₁) ≫ (f₂ ⊙ₗₘ g₂) := by
    cat_disch
  actionAssocIso_hom_naturality
      {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
      ((f ⊗ₘ g) ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).hom =
        (αₗ c₁ c₃ d₁).hom ≫ (f ⊙ₗₘ g ⊙ₗₘ h) := by
    cat_disch
  actionUnitIso_hom_naturality {d d' : D} (f : d ⟶ d') :
      (λₗ d).hom ≫ f = (𝟙_ C) ⊴ₗ f ≫ (λₗ d').hom := by
    cat_disch
  whiskerLeft_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
      (c ◁ f) ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ f ⊵ₗ d ≫ (αₗ _ _ _).inv := by
    cat_disch
  whiskerRight_actionHomLeft {c c' : C} (c'' : C) (f : c ⟶ c') (d : D) :
      (f ▷ c'') ⊵ₗ d = (αₗ c c'' d).hom ≫
        f ⊵ₗ (c'' ⊙ₗ d : D) ≫ (αₗ c' c'' d).inv := by
    cat_disch
  associator_actionHom (c₁ c₂ c₃ : C) (d : D) :
      (α_ c₁ c₂ c₃).hom ⊵ₗ d ≫ (αₗ c₁ (c₂ ⊗ c₃) d).hom ≫
        c₁ ⊴ₗ (αₗ c₂ c₃ d).hom =
      (αₗ (c₁ ⊗ c₂ : C) c₃ d).hom ≫ (αₗ c₁ c₂ (c₃ ⊙ₗ d)).hom := by
    cat_disch
  leftUnitor_actionHom (c : C) (d : D) :
      (λ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ (λₗ _).hom := by
    cat_disch
  rightUnitor_actionHom (c : C) (d : D) :
      (ρ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ (λₗ _).hom := by
    cat_disch

attribute [reassoc] MonoidalLeftAction.actionHom_def

attribute [reassoc, simp] MonoidalLeftAction.id_actionHomLeft

attribute [reassoc, simp] MonoidalLeftAction.actionHomRight_id

attribute [reassoc, simp] MonoidalLeftAction.whiskerLeft_actionHomLeft

attribute [simp, reassoc] MonoidalLeftAction.actionHom_comp

attribute [reassoc] MonoidalLeftAction.actionAssocIso_hom_naturality

attribute [reassoc] MonoidalLeftAction.actionUnitIso_hom_naturality

attribute [reassoc (attr := simp)] MonoidalLeftAction.associator_actionHom

attribute [simp, reassoc] MonoidalLeftAction.leftUnitor_actionHom

attribute [simp, reassoc] MonoidalLeftAction.rightUnitor_actionHom
