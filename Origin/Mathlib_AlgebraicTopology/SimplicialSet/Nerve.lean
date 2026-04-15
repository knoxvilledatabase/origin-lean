/-
Extracted from AlgebraicTopology/SimplicialSet/Nerve.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.ComposableArrows

/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).
By definition, the type of `n`-simplices of `nerve C` is `ComposableArrows C n`,
which is the category `Fin (n + 1) ⥤ C`.

## References
* [Paul G. Goerss, John F. Jardine, *Simplicial Homotopy Theory*][goerss-jardine-2009]

-/

open CategoryTheory.Category Simplicial

universe v u

namespace CategoryTheory

@[simps]
def nerve (C : Type u) [Category.{v} C] : SSet.{max u v} where
  obj Δ := ComposableArrows C (Δ.unop.len)
  map f x := x.whiskerLeft (SimplexCategory.toCat.map f.unop)

instance {C : Type*} [Category C] {Δ : SimplexCategoryᵒᵖ} : Category ((nerve C).obj Δ) :=
  (inferInstance : Category (ComposableArrows C (Δ.unop.len)))

@[simps]
def nerveFunctor : Cat ⥤ SSet where
  obj C := nerve C
  map F := { app := fun _ => (F.mapComposableArrows _).obj }

namespace Nerve

variable {C : Type*} [Category C] {n : ℕ}

lemma δ₀_eq {x : nerve C _[n + 1]} : (nerve C).δ (0 : Fin (n + 2)) x = x.δ₀ := rfl

end Nerve

end CategoryTheory
