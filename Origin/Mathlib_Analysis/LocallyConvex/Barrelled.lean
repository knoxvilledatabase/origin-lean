/-
Extracted from Analysis/LocallyConvex/Barrelled.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Barrelled spaces and the Banach-Steinhaus theorem / Uniform Boundedness Principle

This file defines barrelled spaces over a `NontriviallyNormedField`, and proves the
Banach-Steinhaus theorem for maps from a barrelled space to a space equipped with a family
of seminorms generating the topology (i.e. `WithSeminorms q` for some family of seminorms `q`).

The more standard Banach-Steinhaus theorem for normed spaces is then deduced from that in
`Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`.

## Main definitions

* `BarrelledSpace`: a topological vector space `E` is said to be **barrelled** if all lower
  semicontinuous seminorms on `E` are actually continuous. See the implementation details below for
  more comments on this definition.
* `continuousLinearMapOfTendsto`: fix `E` a barrelled space and `F` a `PolynormableSpace`.
  Given a sequence of continuous linear maps from `E` to `F` that converges pointwise to a
  function `f : E → F`, this bundles `f` as a continuous linear map using the
  Banach-Steinhaus theorem.

## Main theorems

* `BaireSpace.instBarrelledSpace`: any TVS that is also a `BaireSpace` is barrelled. In
  particular, this applies to Banach spaces and Fréchet spaces.
* `WithSeminorms.banach_steinhaus`: the **Banach-Steinhaus** theorem, also called
  **Uniform Boundedness Principle**. Fix `E` a barrelled space and `F` a TVS satisfying
  `WithSeminorms q` for some `q`. Any family `𝓕 : ι → E →L[𝕜] F` of continuous linear maps
  that is pointwise bounded is (uniformly) equicontinuous. Here, pointwise bounded means that
  for all `k` and `x`, the family of real numbers `i ↦ q k (𝓕 i x)` is bounded above.
* `PolynormableSpace.banach_steinhaus`: a version of the above which does not make reference
  to a fixed seminorm family. Fix `E` a barrelled space and `F` a `PolynormableSpace`.
  Any family `𝓕 : ι → E →L[𝕜] F` of continuous linear maps that is pointwise von Neumann bounded
  is (uniformly) equicontinuous.

## Implementation details

Barrelled spaces are defined in Bourbaki as locally convex spaces where barrels (aka closed
balanced absorbing convex sets) are neighborhoods of zero. One can then show that barrels in a
locally convex space are exactly closed unit balls of lower semicontinuous seminorms, hence that a
locally convex space is barrelled iff any lower semicontinuous seminorm is continuous.

The problem with this definition is the local convexity, which is essential to prove that the
barrel definition is equivalent to the seminorm definition, because we can essentially only
use `LocallyConvexSpace` over `ℝ` or `ℂ` (which is indeed the setup in which Bourbaki does most
of the theory). Since we can easily prove the normed space version over any
`NontriviallyNormedField`, this wouldn't make for a very satisfying "generalization".

Fortunately, it turns out that using the seminorm definition directly solves all problems,
since it is exactly what we need for the proof. One could then expect to need the barrel
characterization to prove that Baire TVS are barrelled, but the proof is actually easier to do
with the seminorm characterization!

## TODO

* define barrels and prove that a locally convex space is barrelled iff all barrels are
  neighborhoods of zero.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

banach-steinhaus, uniform boundedness, equicontinuity
-/

open Filter Topology Set ContinuousLinearMap

section defs

class BarrelledSpace (𝕜 E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  /-- In a barrelled space, all lower semicontinuous seminorms on `E` are actually continuous. -/
  continuous_of_lowerSemicontinuous : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p → Continuous p

theorem Seminorm.continuous_of_lowerSemicontinuous {𝕜 E : Type*} [AddGroup E] [SMul 𝕜 E]
    [SeminormedRing 𝕜] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : Seminorm 𝕜 E)
    (hp : LowerSemicontinuous p) : Continuous p :=
  BarrelledSpace.continuous_of_lowerSemicontinuous p hp

theorem Seminorm.continuous_iSup
    {ι : Sort*} {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : ι → Seminorm 𝕜 E)
    (hp : ∀ i, Continuous (p i)) (bdd : BddAbove (range p)) :
    Continuous (⨆ i, p i) := by
  rw [← Seminorm.coe_iSup_eq bdd]
  refine Seminorm.continuous_of_lowerSemicontinuous _ ?_
  rw [Seminorm.coe_iSup_eq bdd]
  rw [Seminorm.bddAbove_range_iff] at bdd
  convert lowerSemicontinuous_ciSup (f := fun i x ↦ p i x) bdd (fun i ↦ (hp i).lowerSemicontinuous)
  exact iSup_apply

end defs

section TVS_anyField

variable {α ι κ 𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁]
    [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F]

-- INSTANCE (free from Core): BaireSpace.instBarrelledSpace

namespace WithSeminorms

variable [UniformSpace E] [UniformSpace F] [IsUniformAddGroup E] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E] {𝓕 : ι → E →SL[σ₁₂] F}
    {q : SeminormFamily 𝕜₂ F κ} (hq : WithSeminorms q)

include hq

protected theorem banach_steinhaus (H : ∀ k x, BddAbove (range fun i ↦ q k (𝓕 i x))) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  -- We just have to prove that `⊔ i, (q k) ∘ (𝓕 i)` is a (well-defined) continuous seminorm
  -- for all `k`.
  refine (hq.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup (toLinearMap ∘ 𝓕)).mpr ?_
  intro k
  -- By assumption the supremum `⊔ i, q k (𝓕 i x)` is well-defined for all `x`, hence the
  -- supremum `⊔ i, (q k) ∘ (𝓕 i)` is well defined in the lattice of seminorms.
  have : BddAbove (range fun i ↦ (q k).comp (𝓕 i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    exact H k
  -- By definition of the lattice structure on seminorms, `⊔ i, (q k) ∘ (𝓕 i)` is the *pointwise*
  -- supremum of the continuous seminorms `(q k) ∘ (𝓕 i)`. Since `E` is barrelled, this supremum
  -- is continuous.
  exact ⟨this, Seminorm.continuous_iSup _
    (fun i ↦ (hq.continuous_seminorm k).comp (𝓕 i).continuous) this⟩

end WithSeminorms

section PolynormableSpace

open Bornology

variable [UniformSpace E] [UniformSpace F] [IsUniformAddGroup E] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E] {𝓕 : ι → E →SL[σ₁₂] F} [PolynormableSpace 𝕜₂ F]

protected theorem PolynormableSpace.banach_steinhaus
    (H : ∀ x, IsVonNBounded 𝕜₂ (range fun i ↦ 𝓕 i x)) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  have hp := PolynormableSpace.withSeminorms 𝕜₂ F
  refine hp.banach_steinhaus ?_
  simp_rw [hp.isVonNBounded_iff_seminorm_bddAbove, ← range_comp] at H
  exact fun q x ↦ H x q

variable [ContinuousSMul 𝕜₂ F]

def continuousLinearMapOfTendsto
    [T2Space F] {l : Filter α} [l.IsCountablyGenerated]
    [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F} (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) :
    E →SL[σ₁₂] F where
  toLinearMap := linearMapOfTendsto _ _ h
  cont := by
    -- Since the filter `l` is countably generated and nontrivial, we can find a sequence
    -- `u : ℕ → α` that tends to `l`. By considering `g ∘ u` instead of `g`, we can thus assume
    -- that `α = ℕ` and `l = atTop`
    rcases l.exists_seq_tendsto with ⟨u, hu⟩
    -- We claim that the limit is continuous because it's a limit of an equicontinuous family.
    -- By the Banach-Steinhaus theorem, this equicontinuity will follow from pointwise boundedness.
    refine (h.comp hu).continuous_of_equicontinuous
      (PolynormableSpace.banach_steinhaus ?_).equicontinuous
    -- For `x` fixed, we need to show that the range of `(i : ℕ) ↦ g i x` is bounded.
    intro x
    -- This follows from the fact that this sequence converges (to `f x`) by hypothesis.
    rw [tendsto_pi_nhds] at h
    exact ((h x).comp hu).isVonNBounded_range 𝕜₂

end PolynormableSpace

section Deprecated

variable [UniformSpace E] [UniformSpace F] [IsUniformAddGroup E] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E] [ContinuousSMul 𝕜₂ F] {𝓕 : ι → E →SL[σ₁₂] F}
    {q : SeminormFamily 𝕜₂ F κ} (hq : WithSeminorms q)

include hq
