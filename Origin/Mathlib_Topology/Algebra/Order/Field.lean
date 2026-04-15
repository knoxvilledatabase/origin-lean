/-
Extracted from Topology/Algebra/Order/Field.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topologies on linear ordered fields

In this file we prove that a linear ordered field with order topology has continuous multiplication
and division (apart from zero in the denominator). We also prove theorems like
`Filter.Tendsto.mul_atTop`: if `f` tends to a positive number and `g` tends to positive infinity,
then `f * g` tends to positive infinity.
-/

open Set Filter TopologicalSpace Function

open scoped Pointwise Topology

open OrderDual (toDual ofDual)

section Semifield

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

theorem Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0] with x hg
    hf using mul_le_mul_of_nonneg_left hg.le hf

theorem Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atTop_mul_pos hC hf
