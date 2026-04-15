/-
Extracted from CategoryTheory/SmallRepresentatives.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Representatives of small categories

Given a type `Ω : Type w`, we construct a structure `SmallCategoryOfSet Ω : Type w`
which consists of the data and axioms that allows to define a category
structure such that the type of objects and morphisms identify to subtypes of `Ω`.

This allows to define a small family of small categories
`SmallCategoryOfSet.categoryFamily : SmallCategoryOfSet Ω → Type w`
which, up to equivalence, represents all categories such that
types of objects and morphisms have cardinalities less than or equal to
that of `Ω` (see `SmallCategoryOfSet.exists_equivalence`).

Given a cardinal `κ : Cardinal.{w}`, we also provide a small family of categories
`SmallCategoryCardinalLT.categoryFamily κ` which represents (up to isomorphism)
any category `C` such that `HasCardinalLT C κ` holds.

-/

universe w v u

namespace CategoryTheory

variable (Ω : Type w)

structure SmallCategoryOfSet where
  /-- objects -/
  obj : Set Ω
  /-- morphisms -/
  hom (X Y : obj) : Set Ω
  /-- identity morphisms -/
  id (X : obj) : hom X X
  /-- the composition of morphisms -/
  comp {X Y Z : obj} (f : hom X Y) (g : hom Y Z) : hom X Z
  id_comp {X Y : obj} (f : hom X Y) : comp (id _) f = f := by cat_disch
  comp_id {X Y : obj} (f : hom X Y) : comp f (id _) = f := by cat_disch
  assoc {X Y Z T : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z T) :
      comp (comp f g) h = comp f (comp g h) := by cat_disch

namespace SmallCategoryOfSet

attribute [simp] id_comp comp_id assoc
