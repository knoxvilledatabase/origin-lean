/-
Extracted from Topology/Order/MonotoneConvergence.lean
Genuine: 15 of 25 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Bounded monotone sequences converge

In this file we prove a few theorems of the form “if the range of a monotone function `f : ι → α`
admits a least upper bound `a`, then `f x` tends to `a` as `x → ∞`”, as well as version of this
statement for (conditionally) complete lattices that use `⨆ x, f x` instead of `IsLUB`.

These theorems work for linear orders with order topologies as well as their products (both in terms
of `Prod` and in terms of function types). In order to reduce code duplication, we introduce two
typeclasses (one for the property formulated above and one for the dual property), prove theorems
assuming one of these typeclasses, and provide instances for linear orders and their products.

We also prove some "inverse" results: if `f n` is a monotone sequence and `a` is its limit,
then `f n ≤ a` for all `n`.

## Tags

monotone convergence
-/

open Filter Set Function

open scoped Topology

variable {α β : Type*}

class SupConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → ∞` -/
  tendsto_coe_atTop_isLUB :
    ∀ (a : α) (s : Set α), IsLUB s a → Tendsto ((↑) : s → α) atTop (𝓝 a)

class InfConvergenceClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  /-- proof that a monotone function tends to `𝓝 a` as `x → -∞` -/
  tendsto_coe_atBot_isGLB :
    ∀ (a : α) (s : Set α), IsGLB s a → Tendsto ((↑) : s → α) atBot (𝓝 a)

-- INSTANCE (free from Core): OrderDual.supConvergenceClass

-- INSTANCE (free from Core): OrderDual.infConvergenceClass

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

variable {ι : Type*} [Preorder ι] [TopologicalSpace α]

section IsLUB

variable [Preorder α] [SupConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atTop_isLUB (h_mono : Monotone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by
  suffices Tendsto (rangeFactorization f) atTop atTop from
    (SupConvergenceClass.tendsto_coe_atTop_isLUB _ _ ha).comp this
  exact h_mono.rangeFactorization.tendsto_atTop_atTop fun b => b.2.imp fun a ha => ha.ge

theorem tendsto_atBot_isLUB (h_anti : Antitone f) (ha : IsLUB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_anti.dual_left ha using 1

end IsLUB

section IsGLB

variable [Preorder α] [InfConvergenceClass α] {f : ι → α} {a : α}

theorem tendsto_atBot_isGLB (h_mono : Monotone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atBot (𝓝 a) := by convert tendsto_atTop_isLUB h_mono.dual ha.dual using 1

theorem tendsto_atTop_isGLB (h_anti : Antitone f) (ha : IsGLB (Set.range f) a) :
    Tendsto f atTop (𝓝 a) := by convert tendsto_atBot_isLUB h_anti.dual ha.dual using 1

end IsGLB

section CiSup

variable [ConditionallyCompletePartialOrderSup α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_ciSup (h_mono : Monotone f) (hbdd : BddAbove <| range f) :
    Tendsto f atTop (𝓝 (⨆ i, f i)) := by
  obtain (h | h) := eq_or_ne atTop (⊥ : Filter ι)
  · simp [h]
  · obtain ⟨h₁, h₂⟩ := Filter.atTop_neBot_iff.mp ⟨h⟩
    exact tendsto_atTop_isLUB h_mono <|
      h_mono.directed_le.directedOn_range.isLUB_csSup (Set.range_nonempty f) hbdd

theorem tendsto_atBot_ciSup (h_anti : Antitone f) (hbdd : BddAbove <| range f) :
    Tendsto f atBot (𝓝 (⨆ i, f i)) := by convert tendsto_atTop_ciSup h_anti.dual hbdd.dual using 1

end CiSup

section CiInf

variable [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_ciInf (h_mono : Monotone f) (hbdd : BddBelow <| range f) :
    Tendsto f atBot (𝓝 (⨅ i, f i)) := by convert tendsto_atTop_ciSup h_mono.dual hbdd.dual using 1

theorem tendsto_atTop_ciInf (h_anti : Antitone f) (hbdd : BddBelow <| range f) :
    Tendsto f atTop (𝓝 (⨅ i, f i)) := by convert tendsto_atBot_ciSup h_anti.dual hbdd.dual using 1

end CiInf

section iSup

variable [CompleteLattice α] [SupConvergenceClass α] {f : ι → α}

theorem tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f atTop (𝓝 (⨆ i, f i)) :=
  tendsto_atTop_ciSup h_mono (OrderTop.bddAbove _)

theorem tendsto_atBot_iSup (h_anti : Antitone f) : Tendsto f atBot (𝓝 (⨆ i, f i)) :=
  tendsto_atBot_ciSup h_anti (OrderTop.bddAbove _)

end iSup

section iInf

variable [CompleteLattice α] [InfConvergenceClass α] {f : ι → α}

theorem tendsto_atBot_iInf (h_mono : Monotone f) : Tendsto f atBot (𝓝 (⨅ i, f i)) :=
  tendsto_atBot_ciInf h_mono (OrderBot.bddBelow _)

theorem tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f atTop (𝓝 (⨅ i, f i)) :=
  tendsto_atTop_ciInf h_anti (OrderBot.bddBelow _)

end iInf

end

-- INSTANCE (free from Core): Prod.supConvergenceClass

-- INSTANCE (free from Core): [Preorder

-- INSTANCE (free from Core): Pi.supConvergenceClass

-- INSTANCE (free from Core): Pi.infConvergenceClass

-- INSTANCE (free from Core): Pi.supConvergenceClass'

-- INSTANCE (free from Core): Pi.infConvergenceClass'

theorem tendsto_atTop_of_monotone {ι α : Type*} [Preorder ι] [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [OrderTopology α] {f : ι → α} (h_mono : Monotone f) :
    Tendsto f atTop atTop ∨ ∃ l, Tendsto f atTop (𝓝 l) := by
  classical
  exact if H : BddAbove (range f) then Or.inr ⟨_, tendsto_atTop_ciSup h_mono H⟩
  else Or.inl <| tendsto_atTop_atTop_of_monotone' h_mono H
