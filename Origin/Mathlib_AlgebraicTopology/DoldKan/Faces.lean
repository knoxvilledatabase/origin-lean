/-
Extracted from AlgebraicTopology/DoldKan/Faces.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Study of face maps for the Dold-Kan correspondence

In this file, we obtain the technical lemmas that are used in the file
`Projections.lean` in order to get basic properties of the endomorphisms
`P q : K[X] ⟶ K[X]` with respect to face maps (see `Homotopies.lean` for the
role of these endomorphisms in the overall strategy of proof).

The main lemma in this file is `HigherFacesVanish.induction`. It is based
on two technical lemmas `HigherFacesVanish.comp_Hσ_eq` and
`HigherFacesVanish.comp_Hσ_eq_zero`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

  CategoryTheory.Preadditive CategoryTheory.SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

variable {X : SimplicialObject C}

def HigherFacesVanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _⦋n + 1⦌) : Prop :=
  ∀ j : Fin (n + 1), n + 1 ≤ (j : ℕ) + q → φ ≫ X.δ j.succ = 0

namespace HigherFacesVanish
