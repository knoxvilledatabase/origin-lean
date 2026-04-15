/-
Extracted from Order/SuccPred/LinearLocallyFinite.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Linear locally finite orders

We prove that a `LinearOrder` which is a `LocallyFiniteOrder` also verifies
* `SuccOrder`
* `PredOrder`
* `IsSuccArchimedean`
* `IsPredArchimedean`
* `Countable`

Furthermore, we show that there is an `OrderIso` between such an order and a subset of `ℤ`.

## Main definitions

* `toZ i0 i`: in a linear order on which we can define predecessors and successors and which is
  succ-archimedean, we can assign a unique integer `toZ i0 i` to each element `i : ι` while
  respecting the order, starting from `toZ i0 i0 = 0`.

## Main results

Results about linear locally finite orders:
* `LinearLocallyFiniteOrder.SuccOrder`: a linear locally finite order has a successor function.
* `LinearLocallyFiniteOrder.PredOrder`: a linear locally finite order has a predecessor
  function.
* `LinearLocallyFiniteOrder.isSuccArchimedean`: a linear locally finite order is
  succ-archimedean.
* `LinearOrder.pred_archimedean_of_succ_archimedean`: a succ-archimedean linear order is also
  pred-archimedean.
* `countable_of_linear_succ_pred_arch` : a succ-archimedean linear order is countable.

About `toZ`:
* `orderIsoRangeToZOfLinearSuccPredArch`: `toZ` defines an `OrderIso` between `ι` and its
  range.
* `orderIsoNatOfLinearSuccPredArch`: if the order has a bot but no top, `toZ` defines an
  `OrderIso` between `ι` and `ℕ`.
* `orderIsoIntOfLinearSuccPredArch`: if the order has neither bot nor top, `toZ` defines an
  `OrderIso` between `ι` and `ℤ`.
* `orderIsoRangeOfLinearSuccPredArch`: if the order has both a bot and a top, `toZ` gives an
  `OrderIso` between `ι` and `Finset.range ((toZ ⊥ ⊤).toNat + 1)`.

-/

open Order

variable {ι : Type*} [LinearOrder ι]

namespace LinearOrder

variable [SuccOrder ι] [PredOrder ι]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): isSuccArchimedean_of_isPredArchimedean

theorem isSuccArchimedean_iff_isPredArchimedean : IsSuccArchimedean ι ↔ IsPredArchimedean ι where
  mp _ := isPredArchimedean_of_isSuccArchimedean
  mpr _ := isSuccArchimedean_of_isPredArchimedean

end LinearOrder

namespace LinearLocallyFiniteOrder

noncomputable def succFn (i : ι) : ι :=
  (exists_glb_Ioi i).choose

theorem succFn_spec (i : ι) : IsGLB (Set.Ioi i) (succFn i) :=
  (exists_glb_Ioi i).choose_spec

theorem le_succFn (i : ι) : i ≤ succFn i := by
  rw [le_isGLB_iff (succFn_spec i), mem_lowerBounds]
  exact fun x hx ↦ le_of_lt hx

theorem isGLB_Ioc_of_isGLB_Ioi {i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i) k) :
    IsGLB (Set.Ioc i j) k := by
  simp_rw [IsGLB, IsGreatest, mem_upperBounds, mem_lowerBounds] at h ⊢
  refine ⟨fun x hx ↦ h.1 x hx.1, fun x hx ↦ h.2 x ?_⟩
  intro y hy
  rcases le_or_gt y j with h_le | h_lt
  · exact hx y ⟨hy, h_le⟩
  · exact le_trans (hx j ⟨hij_lt, le_rfl⟩) h_lt.le

theorem isMax_of_succFn_le [LocallyFiniteOrder ι] (i : ι) (hi : succFn i ≤ i) : IsMax i := by
  refine fun j _ ↦ not_lt.mp fun hij_lt ↦ ?_
  have h_succFn_eq : succFn i = i := le_antisymm hi (le_succFn i)
  have h_glb : IsGLB (Finset.Ioc i j : Set ι) i := by
    rw [Finset.coe_Ioc]
    have h := succFn_spec i
    rw [h_succFn_eq] at h
    exact isGLB_Ioc_of_isGLB_Ioi hij_lt h
  have hi_mem : i ∈ Finset.Ioc i j := by
    refine Finset.isGLB_mem _ h_glb ?_
    exact ⟨_, Finset.mem_Ioc.mpr ⟨hij_lt, le_rfl⟩⟩
  rw [Finset.mem_Ioc] at hi_mem
  exact lt_irrefl i hi_mem.1

theorem succFn_le_of_lt (i j : ι) (hij : i < j) : succFn i ≤ j := by
  have h := succFn_spec i
  rw [IsGLB, IsGreatest, mem_lowerBounds] at h
  exact h.1 j hij

theorem le_of_lt_succFn (j i : ι) (hij : j < succFn i) : j ≤ i := by
  rw [lt_isGLB_iff (succFn_spec i)] at hij
  obtain ⟨k, hk_lb, hk⟩ := hij
  rw [mem_lowerBounds] at hk_lb
  exact not_lt.mp fun hi_lt_j ↦ not_le.mpr hk (hk_lb j hi_lt_j)

variable (ι) in
