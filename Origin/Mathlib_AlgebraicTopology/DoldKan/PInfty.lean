/-
Extracted from AlgebraicTopology/DoldKan/PInfty.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Construction of the projection `PInfty` for the Dold-Kan correspondence

In this file, we construct the projection `PInfty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `Projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `PInfty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive

  CategoryTheory.SimplicialObject CategoryTheory.Idempotents Opposite Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

theorem P_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((P (q + 1)).f n : X _⦋n⦌ ⟶ _) = (P q).f n := by
  cases n with
  | zero => simp only [P_f_0_eq]
  | succ n =>
    simp only [P_succ, comp_add, comp_id, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      add_eq_left]
    exact (HigherFacesVanish.of_P q n).comp_Hσ_eq_zero (Nat.succ_le_iff.mp hqn)

theorem Q_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((Q (q + 1)).f n : X _⦋n⦌ ⟶ _) = (Q q).f n := by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]

noncomputable def PInfty : K[X] ⟶ K[X] :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => ((P n).f n : X _⦋n⦌ ⟶ _)) fun n => by
    simpa only [← P_is_eventually_constant (show n ≤ n by rfl),
      AlternatingFaceMapComplex.obj_d_eq] using (P (n + 1) : K[X] ⟶ _).comm (n + 1) n

noncomputable def QInfty : K[X] ⟶ K[X] :=
  𝟙 _ - PInfty
