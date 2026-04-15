/-
Extracted from Topology/Algebra/InfiniteSum/Nonarchimedean.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Infinite sums and products in nonarchimedean abelian groups

Let `G` be a complete nonarchimedean abelian group and let `f : α → G` be a function. We prove that
`f` is unconditionally summable if and only if `f a` tends to zero on the cofinite filter on `α`.
We also prove the analogous result in the multiplicative setting.

-/

open Filter Topology

namespace NonarchimedeanGroup

variable {α G : Type*}

variable [CommGroup G] [UniformSpace G] [UniformGroup G] [NonarchimedeanGroup G]

@[to_additive "Let `G` be a nonarchimedean additive abelian group, and let `f : α → G` be a function
that tends to zero on the filter of cofinite sets. For each finite subset of `α`, consider the
partial sum of `f` on that subset. These partial sums form a Cauchy filter."]
theorem cauchySeq_prod_of_tendsto_cofinite_one {f : α → G} (hf : Tendsto f cofinite (𝓝 1)) :
    CauchySeq (fun s ↦ ∏ i ∈ s, f i) := by
  /- Let `U` be a neighborhood of `1`. It suffices to show that there exists `s : Finset α` such
  that for any `t : Finset α` disjoint from `s`, we have `∏ i ∈ t, f i ∈ U`. -/
  apply cauchySeq_finset_iff_prod_vanishing.mpr
  intro U hU
  -- Since `G` is nonarchimedean, `U` contains an open subgroup `V`.
  rcases is_nonarchimedean U hU with ⟨V, hV⟩
  /- Let `s` be the set of all indices `i : α` such that `f i ∉ V`. By our assumption `hf`, this is
  finite. -/
  use (tendsto_def.mp hf V V.mem_nhds_one).toFinset
  /- For any `t : Finset α` disjoint from `s`, the product `∏ i ∈ t, f i` is a product of elements
  of `V`, so it is an element of `V` too. Thus, `∏ i ∈ t, f i ∈ U`, as desired. -/
  intro t ht
  apply hV
  apply Subgroup.prod_mem
  intro i hi
  simpa using Finset.disjoint_left.mp ht hi

@[to_additive "Let `G` be a complete nonarchimedean additive abelian group, and let `f : α → G` be a
function that tends to zero on the filter of cofinite sets. Then `f` is unconditionally summable."]
theorem multipliable_of_tendsto_cofinite_one [CompleteSpace G] {f : α → G}
    (hf : Tendsto f cofinite (𝓝 1)) : Multipliable f :=
  CompleteSpace.complete (cauchySeq_prod_of_tendsto_cofinite_one hf)

@[to_additive "Let `G` be a complete nonarchimedean additive abelian group. Then a function
`f : α → G` is unconditionally summable if and only if it tends to zero on the filter of cofinite
sets."]
theorem multipliable_iff_tendsto_cofinite_one [CompleteSpace G] (f : α → G) :
    Multipliable f ↔ Tendsto f cofinite (𝓝 1) :=
  ⟨Multipliable.tendsto_cofinite_one, multipliable_of_tendsto_cofinite_one⟩

end NonarchimedeanGroup
