/-
Extracted from AlgebraicTopology/DoldKan/NReflectsIso.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# N₁ and N₂ reflect isomorphisms

In this file, it is shown that the functors
`N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` and
`N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)`
reflect isomorphisms for any preadditive category `C`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents Opposite Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

open MorphComponents

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

theorem compatibility_N₂_N₁_karoubi :
    N₂ ⋙ (karoubiChainComplexEquivalence C ℕ).functor =
      karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C ⋙
        N₁ ⋙ (karoubiChainComplexEquivalence (Karoubi C) ℕ).functor ⋙
            Functor.mapHomologicalComplex (KaroubiKaroubi.equivalence C).inverse _ := by
  refine CategoryTheory.Functor.ext (fun P => ?_) fun P Q f => ?_
  · refine HomologicalComplex.ext ?_ ?_
    · ext n
      · rfl
      · dsimp
        simp only [karoubi_PInfty_f, comp_id, PInfty_f_naturality, id_comp]
    · rintro _ n (rfl : n + 1 = _)
      ext
      have h := (AlternatingFaceMapComplex.map P.p).comm (n + 1) n
      dsimp [N₂, karoubiChainComplexEquivalence,
        KaroubiHomologicalComplexEquivalence.Functor.obj] at h ⊢
      simp only [assoc, Karoubi.eqToHom_f, eqToHom_refl, comp_id,
        karoubi_alternatingFaceMapComplex_d, karoubi_PInfty_f,
        ← HomologicalComplex.Hom.comm_assoc, ← h, app_idem_assoc]
  · ext n
    dsimp [KaroubiKaroubi.inverse, Functor.mapHomologicalComplex]
    simp only [karoubi_PInfty_f, HomologicalComplex.eqToHom_f, Karoubi.eqToHom_f,
      assoc, comp_id, PInfty_f_naturality, app_p_comp,
      karoubiChainComplexEquivalence_functor_obj_X_p, N₂_obj_p_f, eqToHom_refl,
      PInfty_f_naturality_assoc, app_comp_p, PInfty_f_idem_assoc]

-- INSTANCE (free from Core): :

end DoldKan

end AlgebraicTopology
