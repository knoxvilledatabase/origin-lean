/-
Extracted from CategoryTheory/Sites/Point/OfIsCofiltered.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Alternative constructor for points

Let `J` be a Grothendieck topology on a category `C`. We provide a constructor
`Point.ofIsCofiltered` for points for `J` which takes as inputs:
- a functor `p : N ⥤ C` where `N` is cofiltered and initially small
- the assumption that for any covering sieve `R` of `X`,
  any morphism `f : p.obj U ⟶ X`, there exists a morphism `g : Y ⟶ X` in `R`,
  a morphism `q : V ⟶ U` in `N` and a morphism `a : p.obj V ⟶ Y` such
  that `a ≫ g = p.map q ≫ f`.
We show that the fiber of a presheaf for the constructed point identifies
to a colimit indexed by the category `N`.

-/

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]

variable [LocallySmall.{w} C] {N : Type u'} [Category.{v'} N]
  (p : N ⥤ C) [InitiallySmall.{w} N]
  {J : GrothendieckTopology C}

namespace ofIsCofiltered

-- INSTANCE (free from Core): :

noncomputable def fiber : C ⥤ Type w :=
  shrinkYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ (Type w)).obj p.op ⋙ colim

variable {p} in

noncomputable def fiberMk {U : N} {X : C} (f : p.obj U ⟶ X) : (fiber.{w} p).obj X :=
  colimit.ι (p.op ⋙ shrinkYoneda.{w}.obj X) (op U)
    (shrinkYonedaObjObjEquiv.symm f)

variable {p} in

lemma fiberMk_jointly_surjective {X : C} (x : (fiber.{w} p).obj X) :
    ∃ (U : N) (f : p.obj U ⟶ X), fiberMk f = x := by
  obtain ⟨U, f, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) x
  obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
  exact ⟨U.unop, f, rfl⟩

set_option backward.isDefEq.respectTransparency false in

variable {p} in

lemma exists_of_fiberMk_eq_fiberMk [IsCofiltered N]
    {U : N} {X : C} {f₁ f₂ : p.obj U ⟶ X} (hf : fiberMk f₁ = fiberMk f₂) :
    ∃ (V : N) (g : V ⟶ U), p.map g ≫ f₁ = p.map g ≫ f₂ := by
  obtain ⟨V, g, hg⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (colimit.isColimit (p.op ⋙ shrinkYoneda.{w}.obj X)) _ _).1 hf
  refine ⟨V.unop, g.unop, ?_⟩
  simpa [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] using hg

set_option backward.isDefEq.respectTransparency false in
