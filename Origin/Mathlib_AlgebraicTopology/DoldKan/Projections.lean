/-
Extracted from AlgebraicTopology/DoldKan/Projections.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Construction of projections for the Dold-Kan correspondence

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`HigherFacesVanish.of_P`, `HigherFacesVanish.comp_P_eq_self` and
`comp_P_eq_self_iff`.

Then, we show that they are projections (see `P_f_idem`
and `P_idem`). They are natural transformations (see `natTransP`
and `P_f_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `PInfty.lean`
in order to define `PInfty : K[X] ⟶ K[X]`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive

  CategoryTheory.SimplicialObject Opposite CategoryTheory.Idempotents

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

noncomputable def P : ℕ → (K[X] ⟶ K[X])
  | 0 => 𝟙 _
  | q + 1 => P q ≫ (𝟙 _ + Hσ q)
