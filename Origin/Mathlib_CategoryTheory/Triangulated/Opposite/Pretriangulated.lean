/-
Extracted from CategoryTheory/Triangulated/Opposite/Pretriangulated.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The pretriangulated structure on the opposite category

In this file, we construct the pretriangulated structure
on the opposite category `Cᵒᵖ` of a pretriangulated category `C`.

The shift on `Cᵒᵖ` was constructed in `Mathlib.CategoryTheory.Triangulated.Opposite.Basic`,
and is such that shifting by `n : ℤ` on `Cᵒᵖ` corresponds to the shift by
`-n` on `C`. In `Mathlib.CategoryTheory.Triangulated.Opposite.Triangle`, we constructed
an equivalence `(Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ`, called
`Mathlib.CategoryTheory.Pretriangulated.triangleOpEquivalence`.

Here, we defined the notion of distinguished triangles in `Cᵒᵖ`, such that
`triangleOpEquivalence` sends distinguished triangles in `C` to distinguished triangles
in `Cᵒᵖ`. In other words, if `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` is a distinguished triangle in `C`,
then the triangle `op Z ⟶ op Y ⟶ op X ⟶ (op Z)⟦1⟧` that is deduced *without introducing signs*
shall be a distinguished triangle in `Cᵒᵖ`. This is equivalent to the definition
in [Verdier's thesis, p. 96][verdier1996] which would require that the triangle
`(op X)⟦-1⟧ ⟶ op Z ⟶ op Y ⟶ op X` (without signs) is *antidistinguished*.

In the file `Mathlib.Triangulated.Opposite.Triangulated`, we show that `Cᵒᵖ` is
triangulated if `C` is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category* C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Pretriangulated

open Opposite

namespace Opposite

def distinguishedTriangles : Set (Triangle Cᵒᵖ) :=
  {T | ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C}

variable {C}

lemma mem_distinguishedTriangles_iff' (T : Triangle Cᵒᵖ) :
    T ∈ distinguishedTriangles C ↔
      ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
        Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) := by
  rw [mem_distinguishedTriangles_iff]
  constructor
  · intro hT
    exact ⟨_, hT, ⟨(triangleOpEquivalence C).counitIso.symm.app T⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    refine isomorphic_distinguished _ hT' _ ?_
    exact Iso.unop ((triangleOpEquivalence C).unitIso.app (Opposite.op T') ≪≫
      (triangleOpEquivalence C).inverse.mapIso e.symm)

lemma isomorphic_distinguished (T₁ : Triangle Cᵒᵖ)
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle Cᵒᵖ) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles C := by
  simp only [mem_distinguishedTriangles_iff] at hT₁ ⊢
  exact Pretriangulated.isomorphic_distinguished _ hT₁ _
    ((triangleOpEquivalence C).inverse.mapIso e).unop.symm

set_option backward.isDefEq.respectTransparency false in
