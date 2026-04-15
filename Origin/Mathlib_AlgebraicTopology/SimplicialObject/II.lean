/-
Extracted from AlgebraicTopology/SimplicialObject/II.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A construction by Gabriel and Zisman

In this file, we construct a cosimplicial object `SimplexCategory.II`
in `SimplexCategoryᵒᵖ`, i.e. a functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ`.
If we identify `SimplexCategory` with the category of finite nonempty
linearly ordered types, this functor could be interpreted as the
contravariant functor which sends a finite nonempty linearly ordered type `T`
to `T →o Fin 2` (with `f ≤ g ↔ ∀ i, g i ≤ f i`, which turns out to
be a linear order); in particular, it sends `Fin (n + 1)` to a linearly
ordered type which is isomorphic to `Fin (n + 2)`. As a result, we define
`SimplexCategory.II` as a functor which sends `⦋n⦌` to `⦋n + 1⦌`: on morphisms,
it sends faces to degeneracies and vice versa. This construction appeared
in *Calculus of fractions and homotopy theory*, chapter III, paragraph 1.1,
by Gabriel and Zisman.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

open CategoryTheory Simplicial Opposite

namespace SimplexCategory

namespace II

variable {n m : ℕ}

def finset (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i ↦ i = Fin.last _ ∨
    ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc)

lemma mem_finset_iff (f : Fin (n + 1) →o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 2)) :
    i ∈ finset f x ↔ i = Fin.last _ ∨
      ∃ (h : i ≠ Fin.last _), x ≤ (f (i.castPred h)).castSucc := by
  simp [finset]
