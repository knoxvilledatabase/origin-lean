/-
Extracted from AlgebraicTopology/SimplicialSet/HornColimits.lean
Genuine: 17 of 17 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Horns as colimits

In this file, we express horns as colimits:
* horns in `Δ[2]` are pushouts of two copies of `Δ[1]`;
* horns in `Δ[n]` are multicoequalizers of copies of the standard
  simplex of dimension `n-1` (a dedicated API is provided for inner
  horns in `Δ[3]`).

-/

universe u

namespace SSet

open CategoryTheory Simplicial Opposite Limits

namespace horn₂₀

lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdSimplex.face {0, 1})
    (stdSimplex.face {0, 2}) Λ[2, 0] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 0 (by simp)
      · exact face_le_horn (1 : Fin 3) 0 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 2 (by simp)

abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 1 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (1 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₀

namespace horn₂₁

lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdSimplex.face {0, 1})
    (stdSimplex.face {1, 2}) Λ[2, 1] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 1 (by simp)
      · exact face_le_horn (0 : Fin 3) 1 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 2 (by simp)

abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₁₂ := by
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₁

namespace horn₂₂

lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdSimplex.face {0, 2})
    (stdSimplex.face {1, 2}) Λ[2, 2] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (1 : Fin 3) 2 (by simp)
      · exact face_le_horn (0 : Fin 3) 2 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 1 (by simp)

abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (0 : Fin 2)) ι₀₂ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₂

namespace horn

variable {n : ℕ} (i : Fin (n + 1))

lemma multicoequalizerDiagram :
    Subcomplex.MulticoequalizerDiagram Λ[n, i]
      (ι := ({i}ᶜ : Set (Fin (n + 1)))) (fun j ↦ stdSimplex.face {j.1}ᶜ)
      (fun j k ↦ stdSimplex.face {j.1, k.1}ᶜ) where
  iSup_eq := by rw [horn_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

noncomputable def isColimit :
    IsColimit ((multicoequalizerDiagram i).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram i).isColimit'

end horn

namespace horn₃₁

abbrev ι₀ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 0 (by simp)

abbrev ι₂ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 2 (by simp)

abbrev ι₃ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 3 (by simp)

variable {X : SSet.{u}} (f₀ f₂ f₃ : Δ[2] ⟶ X)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂)
  (h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃)

set_option backward.isDefEq.respectTransparency false in
