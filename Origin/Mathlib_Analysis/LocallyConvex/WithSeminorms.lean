/-
Extracted from Analysis/LocallyConvex/WithSeminorms.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology induced by a family of seminorms

## Main definitions

* `SeminormFamily.basisSets`: The set of open seminorm balls for a family of seminorms.
* `SeminormFamily.moduleFilterBasis`: A module filter basis formed by the open balls.
* `Seminorm.IsBounded`: A linear map `f : E →ₗ[𝕜] F` is bounded iff every seminorm in `F` can be
  bounded by a finite number of seminorms in `E`.
* `WithSeminorms p`, when `p` is a family of seminorms on `E`, is a proposition expressing that the
  (existing) topology on `E` is induced by the seminorms `p`.
* `PolynormableSpace 𝕜 E` is a class asserting that the (existing) topology on `E` is induced
  by *some* family of `𝕜`-seminorms. If `𝕜` is `RCLike`, this is equivalent to
  `LocallyConvexSpace 𝕜 E`.
  The terminology is inspired by N. Bourbaki, *Variétés différentielles et analytiques*. However,
  unlike Bourbaki, we do not ask seminorms to be ultrametric when `𝕜` is ultrametric.

## Main statements

* `WithSeminorms.toLocallyConvexSpace`: A space equipped with a family of seminorms is locally
  convex.
* `WithSeminorms.firstCountable`: A space is first countable if its topology is induced by a
  countable family of seminorms.

## Continuity of semilinear maps

If `E` and `F` are topological vector space with the topology induced by a family of seminorms, then
we have a direct method to prove that a linear map is continuous:
* `Seminorm.continuous_from_bounded`: A bounded linear map `f : E →ₗ[𝕜] F` is continuous.

If the topology of a space `E` is induced by a family of seminorms, then we can characterize von
Neumann boundedness in terms of that seminorm family. Together with
`LinearMap.continuous_of_locally_bounded` this gives general criterion for continuity.

* `WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.isVonNBounded_iff_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_finset_seminorm_bounded`
* `WithSeminorms.image_isVonNBounded_iff_seminorm_bounded`

## Tags

seminorm, locally convex
-/

open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {R 𝕜 𝕜₂ 𝕝 𝕝₂ E F G ι ι' : Type*}

section FilterBasis

variable [SeminormedRing R] [AddCommGroup E] [Module R E]

variable (R E ι)

abbrev SeminormFamily :=
  ι → Seminorm R E

variable {R E ι}

namespace SeminormFamily

def basisSets (p : SeminormFamily R E ι) : Set (Set E) :=
  ⋃ (s : Finset ι) (r) (_ : 0 < r), singleton (ball (s.sup p) (0 : E) r)

variable (p : SeminormFamily R E ι)

theorem basisSets_iff {U : Set E} :
    U ∈ p.basisSets ↔ ∃ (i : Finset ι) (r : ℝ), 0 < r ∧ U = ball (i.sup p) 0 r := by
  simp only [basisSets, mem_iUnion, exists_prop, mem_singleton_iff]

theorem basisSets_mem (i : Finset ι) {r : ℝ} (hr : 0 < r) : (i.sup p).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨i, _, hr, rfl⟩

theorem basisSets_singleton_mem (i : ι) {r : ℝ} (hr : 0 < r) : (p i).ball 0 r ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨{i}, _, hr, by rw [Finset.sup_singleton]⟩

theorem basisSets_univ_mem : univ ∈ p.basisSets :=
  (basisSets_iff _).mpr ⟨∅, _, one_pos, by
    rw [Finset.sup_empty, Seminorm.bot_eq_zero, ball_zero' _ one_pos]⟩

theorem basisSets_nonempty : p.basisSets.Nonempty := by
  refine nonempty_def.mpr ⟨univ, basisSets_univ_mem _⟩

theorem basisSets_intersect (U V : Set E) (hU : U ∈ p.basisSets) (hV : V ∈ p.basisSets) :
    ∃ z ∈ p.basisSets, z ⊆ U ∩ V := by
  classical
    rcases p.basisSets_iff.mp hU with ⟨s, r₁, hr₁, hU⟩
    rcases p.basisSets_iff.mp hV with ⟨t, r₂, hr₂, hV⟩
    use ((s ∪ t).sup p).ball 0 (min r₁ r₂)
    refine ⟨p.basisSets_mem (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), ?_⟩
    rw [hU, hV, ball_finset_sup_eq_iInter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩),
      ball_finset_sup_eq_iInter _ _ _ hr₁, ball_finset_sup_eq_iInter _ _ _ hr₂]
    exact
      Set.subset_inter
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_left hi, ball_mono <| min_le_left _ _⟩)
        (Set.iInter₂_mono' fun i hi =>
          ⟨i, Finset.subset_union_right hi, ball_mono <| min_le_right _ _⟩)

theorem basisSets_zero (U) (hU : U ∈ p.basisSets) : (0 : E) ∈ U := by
  rcases p.basisSets_iff.mp hU with ⟨ι', r, hr, hU⟩
  rw [hU, mem_ball_zero, map_zero]
  exact hr

theorem basisSets_add (U) (hU : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V + V ⊆ U := by
  rcases p.basisSets_iff.mp hU with ⟨s, r, hr, hU⟩
  use (s.sup p).ball 0 (r / 2)
  refine ⟨p.basisSets_mem s (div_pos hr zero_lt_two), ?_⟩
  refine Set.Subset.trans (ball_add_ball_subset (s.sup p) (r / 2) (r / 2) 0 0) ?_
  rw [hU, add_zero, add_halves]

theorem basisSets_neg (U) (hU' : U ∈ p.basisSets) :
    ∃ V ∈ p.basisSets, V ⊆ (fun x : E => -x) ⁻¹' U := by
  rcases p.basisSets_iff.mp hU' with ⟨s, r, _, hU⟩
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero]
  exact ⟨U, hU', Eq.subset hU⟩
