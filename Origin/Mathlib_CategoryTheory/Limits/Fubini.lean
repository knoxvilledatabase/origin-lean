/-
Extracted from CategoryTheory/Limits/Fubini.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A Fubini theorem for categorical (co)limits

We prove that $lim_{J × K} G = lim_J (lim_K G(j, -))$ for a functor `G : J × K ⥤ C`,
when all the appropriate limits exist.

We begin working with a functor `F : J ⥤ K ⥤ C`. We'll write `G : J × K ⥤ C` for the associated
"uncurried" functor.

In the first part, given a coherent family `D` of limit cones over the functors `F.obj j`,
and a cone `c` over `G`, we construct a cone over the cone points of `D`.
We then show that if `c` is a limit cone, the constructed cone is also a limit cone.

In the second part, we state the Fubini theorem in the setting where limits are
provided by suitable `HasLimit` classes.

We construct
`limitUncurryIsoLimitCompLim F : limit (uncurry.obj F) ≅ limit (F ⋙ lim)`
and give simp lemmas characterising it.
For convenience, we also provide
`limitIsoLimitCurryCompLim G : limit G ≅ limit ((curry.obj G) ⋙ lim)`
in terms of the uncurried functor.

All statements have their counterpart for colimits.
-/

open CategoryTheory Functor

namespace CategoryTheory.Limits

variable {J K : Type*} [Category* J] [Category* K]

variable {C : Type*} [Category* C]

variable (F : J ⥤ K ⥤ C) (G : J × K ⥤ C)

structure DiagramOfCones where
  /-- For each object, a cone. -/
  obj : ∀ j : J, Cone (F.obj j)
  /-- For each map, a map of cones. -/
  map : ∀ {j j' : J} (f : j ⟶ j'), (Cone.postcompose (F.map f)).obj (obj j) ⟶ obj j'
  id : ∀ j : J, (map (𝟙 j)).hom = 𝟙 _ := by cat_disch
  comp : ∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom := by cat_disch

structure DiagramOfCocones where
  /-- For each object, a cocone. -/
  obj : ∀ j : J, Cocone (F.obj j)
  /-- For each map, a map of cocones. -/
  map : ∀ {j j' : J} (f : j ⟶ j'), (obj j) ⟶ (Cocone.precompose (F.map f)).obj (obj j')
  id : ∀ j : J, (map (𝟙 j)).hom = 𝟙 _ := by cat_disch
  comp : ∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom := by cat_disch

variable {F}
