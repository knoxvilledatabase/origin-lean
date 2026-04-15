/-
Extracted from Algebra/Category/ModuleCat/Presheaf.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Presheaves of modules over a presheaf of rings.

Given a presheaf of rings `R : Cᵒᵖ ⥤ RingCat`, we define the category `PresheafOfModules R`.
An object `M : PresheafOfModules R` consists of a family of modules
`M.obj X : ModuleCat (R.obj X)` for all `X : Cᵒᵖ`, together with the data, for all `f : X ⟶ Y`,
of a functorial linear map `M.map f` from `M.obj X` to the restriction
of scalars of `M.obj Y` via `R.map f`.


## Future work

* Compare this to the definition as a presheaf of pairs `(R, M)` with specified first part.
* Compare this to the definition as a module object of the presheaf of rings
  thought of as a monoid object.
* Presheaves of modules over a presheaf of commutative rings form a monoidal category.
* Pushforward and pullback.
-/

universe v v₁ u₁ u

open CategoryTheory LinearMap Opposite

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (R) in

structure PresheafOfModules where
  /-- a family of modules over `R.obj X` for all `X` -/
  obj (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X)
  /-- the restriction maps of a presheaf of modules -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj Y)
  map_id (X : Cᵒᵖ) :
    map (𝟙 X) = (ModuleCat.restrictScalarsId' (R.map (𝟙 X)).hom
      (congrArg RingCat.Hom.hom (R.map_id X))).inv.app _ := by
        cat_disch
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom <| R.map_comp f g)).inv.app _ := by cat_disch

namespace PresheafOfModules

attribute [simp] map_id map_comp

attribute [reassoc] map_comp

#adaptation_note /-- lean-pr-testing-12564

This is required for `Algebra.Category.ModuleCat.Differentials.Presheaf` -/

-- INSTANCE (free from Core): {R

variable (M M₁ M₂ : PresheafOfModules.{v} R)

set_option backward.isDefEq.respectTransparency false in

lemma congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) :
    M.map f m = M.map g m := by rw [h]

lemma map_comp_apply {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x) :
    M.map (i ≫ j) x = M.map j (M.map i x) := by
  rw [M.map_comp]; rfl
