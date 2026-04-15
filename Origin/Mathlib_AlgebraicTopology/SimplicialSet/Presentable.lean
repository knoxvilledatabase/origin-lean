/-
Extracted from AlgebraicTopology/SimplicialSet/Presentable.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finite simplicial sets are presentable

In this file, we show that finite simplicial sets are finitely presentable,
which will allow the use of the small object argument in `SSet`.

-/

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

namespace Finite

-- INSTANCE (free from Core): (n

set_option backward.isDefEq.respectTransparency false in

lemma exists_epi_from_isCardinalPresentable (X : SSet.{u}) [X.Finite] :
    ∃ (Y : SSet.{u}) (_ : Y.Finite) (_ : IsFinitelyPresentable.{u} Y)
      (p : Y ⟶ X), Epi p := by
  refine ⟨∐ (fun (s : X.N) ↦ Δ[s.dim]), inferInstance, ?_,
    Sigma.desc (fun s ↦ yonedaEquiv.symm s.simplex), ?_⟩
  · apply +allowSynthFailures isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _)
    · exact hasCardinalLT_of_finite _ _ (by rfl)
    · rintro s
      dsimp
      infer_instance
  · simp only [← Subcomplex.range_eq_top_iff, range_eq_iSup_sigma_ι,
        colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, ← N.iSup_subcomplex_eq_top,
        Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]

-- INSTANCE (free from Core): (X

end Finite

end SSet
