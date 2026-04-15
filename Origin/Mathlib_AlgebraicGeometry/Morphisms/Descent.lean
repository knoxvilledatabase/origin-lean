/-
Extracted from AlgebraicGeometry/Morphisms/Descent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Descent of morphism properties

Let `P` and `P'` be morphism properties. In this file we show some results to deduce
that `P` descends along `P'` from a codescent property of ring homomorphisms.

## Main results

- `HasRingHomProperty.descendsAlong`: if `P` is a local property induced by `Q`, `P'` implies
  `Q'` on global sections of affines and `Q` codescends along `Q'`, then `P` descends along `P'`.
- `HasAffineProperty.descendsAlong_of_affineAnd`: if `P` is given by `affineAnd Q`, `P'` implies
  `Q'` on global sections of affines and `Q` codescends along `Q'`, then `P` descends along `P'`
  (see TODOs).

## TODO

- Show that affine morphisms descend along faithfully-flat morphisms. This will make
  `HasAffineProperty.descendsAlong_of_affineAnd` useful.

-/

universe u v

open TensorProduct CategoryTheory Limits

namespace AlgebraicGeometry

variable (P P' : MorphismProperty Scheme.{u})

set_option backward.isDefEq.respectTransparency false in

lemma Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource (X : Scheme.{u}) [CompactSpace X]
    [IsZariskiLocalAtSource P] [P.ContainsIdentities] :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X), Surjective p ∧ P p ∧ IsAffine Y := by
  let 𝒰 := X.affineCover.finiteSubcover
  let p : ∐ (fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.f i)
  refine ⟨_, p, ⟨fun x ↦ ?_⟩, ?_, inferInstance⟩
  · obtain ⟨i, x, rfl⟩ := X.affineCover.finiteSubcover.exists_eq x
    use Sigma.ι X.affineCover.finiteSubcover.X i x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (sigmaOpenCover _)]
    exact fun i ↦ by simpa [p] using IsZariskiLocalAtSource.of_isOpenImmersion _
