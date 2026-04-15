/-
Extracted from Topology/Algebra/ProperAction/Basic.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-!
# Proper group action

In this file we define proper action of a group on a topological space, and we prove that in this
case the quotient space is T2. We also give equivalent definitions of proper action using
ultrafilters and show the transfer of proper action to a closed subgroup.

## Main definitions

* `ProperSMul` : a group `G` acts properly on a topological space `X`
  if the map `(g, x) ↦ (g • x, x)` is proper, in the sense of `IsProperMap`.

## Main statements

* `t2Space_quotient_mulAction_of_properSMul`: If a group `G` acts properly
  on a topological space `X`, then the quotient space is Hausdorff (T2).
* `t2Space_of_properSMul_of_t2Group`: If a T2 group acts properly on a topological space,
  then this topological space is T2.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]

## Tags

Hausdorff, group action, proper action
-/

open Filter Topology Set Prod

class ProperVAdd (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [AddGroup G]
    [AddAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_vadd_pair : IsProperMap (fun gx ↦ (gx.1 +ᵥ gx.2, gx.2) : G × X → X × X)

@[to_additive existing (attr := mk_iff)]
class ProperSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [Group G]
    [MulAction G X] : Prop where
  /-- Proper group action in the sense of Bourbaki:
  the map `G × X → X × X` is a proper map (see `IsProperMap`). -/
  isProperMap_smul_pair : IsProperMap (fun gx ↦ (gx.1 • gx.2, gx.2) : G × X → X × X)

attribute [to_additive existing] properSMul_iff

variable {G X : Type*} [Group G] [MulAction G X]

variable [TopologicalSpace G] [TopologicalSpace X]

@[to_additive "If a group acts properly then in particular it acts continuously."]
instance (priority := 100) ProperSMul.toContinuousSMul [ProperSMul G X] : ContinuousSMul G X where
  continuous_smul := isProperMap_smul_pair.continuous.fst

@[to_additive "A group `G` acts properly on a topological space `X` if and only if
for all ultrafilters `𝒰` on `X`, if `𝒰` converges to `(x₁, x₂)`
along the map `(g, x) ↦ (g • x, x)`, then there exists `g : G` such that `g • x₂ = x₁`
and `𝒰.fst` converges to `g`."]
theorem properSMul_iff_continuousSMul_ultrafilter_tendsto :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) →
      ∃ g : G, g • x₂ = x₁ ∧ Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  refine ⟨fun h ↦ ⟨inferInstance, fun 𝒰 x₁ x₂ h' ↦ ?_⟩, fun ⟨cont, h⟩ ↦ ?_⟩
  · rw [properSMul_iff, isProperMap_iff_ultrafilter] at h
    rcases h.2 h' with ⟨gx, hgx1, hgx2⟩
    refine ⟨gx.1, ?_, (continuous_fst.tendsto gx).mono_left hgx2⟩
    simp only [Prod.mk.injEq] at hgx1
    rw [← hgx1.2, hgx1.1]
  · rw [properSMul_iff, isProperMap_iff_ultrafilter]
    refine ⟨by fun_prop, fun 𝒰 (x₁, x₂) hxx ↦ ?_⟩
    rcases h 𝒰 x₁ x₂ hxx with ⟨g, hg1, hg2⟩
    refine ⟨(g, x₂), by simp_rw [hg1], ?_⟩
    rw [nhds_prod_eq, 𝒰.le_prod]
    exact ⟨hg2, (continuous_snd.tendsto _).comp hxx⟩

theorem properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 [T2Space X] :
    ProperSMul G X ↔ ContinuousSMul G X ∧
      (∀ 𝒰 : Ultrafilter (G × X), ∀ x₁ x₂ : X,
        Tendsto (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) 𝒰 (𝓝 (x₁, x₂)) →
     ∃ g : G, Tendsto (Prod.fst : G × X → G) 𝒰 (𝓝 g)) := by
  rw [properSMul_iff_continuousSMul_ultrafilter_tendsto]
  refine and_congr_right fun hc ↦ ?_
  congrm ∀ 𝒰 x₁ x₂ hxx, ∃ g, ?_
  exact and_iff_right_of_imp fun hg ↦ tendsto_nhds_unique
    (hg.smul ((continuous_snd.tendsto _).comp hxx)) ((continuous_fst.tendsto _).comp hxx)

@[to_additive "If `G` acts properly on `X`, then the quotient space is Hausdorff (T2)."]
theorem t2Space_quotient_mulAction_of_properSMul [ProperSMul G X] :
    T2Space (Quotient (MulAction.orbitRel G X)) := by
  rw [t2_iff_isClosed_diagonal]
  set R := MulAction.orbitRel G X
  let π : X → Quotient R := Quotient.mk'
  have : IsOpenQuotientMap (Prod.map π π) :=
    MulAction.isOpenQuotientMap_quotientMk.prodMap MulAction.isOpenQuotientMap_quotientMk
  rw [← this.isQuotientMap.isClosed_preimage]
  convert ProperSMul.isProperMap_smul_pair.isClosedMap.isClosed_range
  · ext ⟨x₁, x₂⟩
    simp only [mem_preimage, map_apply, mem_diagonal_iff, mem_range, Prod.mk.injEq, Prod.exists,
      exists_eq_right]
    rw [Quotient.eq', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  all_goals infer_instance

@[to_additive "If a T2 group acts properly on a topological space,
then this topological space is T2."]
theorem t2Space_of_properSMul_of_t2Group [h_proper : ProperSMul G X] [T2Space G] : T2Space X := by
  let f := fun x : X ↦ ((1 : G), x)
  have proper_f : IsProperMap f := by
    refine IsClosedEmbedding.isProperMap ⟨?_, ?_⟩
    · let g := fun gx : G × X ↦ gx.2
      have : Function.LeftInverse g f := fun x ↦ by simp
      exact this.isEmbedding (by fun_prop) (by fun_prop)
    · have : range f = ({1} ×ˢ univ) := by simp
      rw [this]
      exact isClosed_singleton.prod isClosed_univ
  rw [t2_iff_isClosed_diagonal]
  let g := fun gx : G × X ↦ (gx.1 • gx.2, gx.2)
  have proper_g : IsProperMap g := (properSMul_iff G X).1 h_proper
  have : g ∘ f = fun x ↦ (x, x) := by ext x <;> simp
  have range_gf : range (g ∘ f) = diagonal X := by simp [this]
  rw [← range_gf]
  exact (proper_f.comp proper_g).isClosed_range

@[to_additive "If two groups `H` and `G` act on a topological space `X` such that `G` acts properly
and there exists a group homomorphims `H → G` which is a closed embedding compatible with the
actions, then `H` also acts properly on `X`."]
theorem properSMul_of_isClosedEmbedding {H : Type*} [Group H] [MulAction H X] [TopologicalSpace H]
    [ProperSMul G X] (f : H →* G) (f_clemb : IsClosedEmbedding f)
    (f_compat : ∀ (h : H) (x : X), f h • x = h • x) : ProperSMul H X where
  isProperMap_smul_pair := by
    have h : IsProperMap (Prod.map f (fun x : X ↦ x)) := f_clemb.isProperMap.prodMap isProperMap_id
    have : (fun hx : H × X ↦ (hx.1 • hx.2, hx.2)) = (fun hx ↦ (f hx.1 • hx.2, hx.2)) := by
      simp [f_compat]
    rw [this]
    exact h.comp <| ProperSMul.isProperMap_smul_pair

alias properSMul_of_closedEmbedding := properSMul_of_isClosedEmbedding

@[to_additive "If `H` is a closed subgroup of `G` and `G` acts properly on X then so does `H`."]
instance {H : Subgroup G} [ProperSMul G X] [H_closed : IsClosed (H : Set G)] : ProperSMul H X :=
  properSMul_of_isClosedEmbedding H.subtype H_closed.isClosedEmbedding_subtypeVal fun _ _ ↦ rfl
