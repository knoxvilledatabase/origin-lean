/-
Extracted from Dynamics/Ergodic/Function.lean
Genuine: 3 of 8 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# Functions invariant under (quasi)ergodic map

In this file we prove that an a.e. strongly measurable function `g : α → X`
that is a.e. invariant under a (quasi)ergodic map is a.e. equal to a constant.
We prove several versions of this statement with slightly different measurability assumptions.
We also formulate a version for `MeasureTheory.AEEqFun` functions
with all a.e. equalities replaced with equalities in the quotient space.
-/

open Function Set Filter MeasureTheory Topology TopologicalSpace

variable {α X : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀ [Nonempty X] [MeasurableSpace X]
    {s : Set X} [MeasurableSpace.CountablySeparated s] {f : α → α} {g : α → X}
    (h : QuasiErgodic f μ) (hs : ∀ᵐ x ∂μ, g x ∈ s) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) :
    ∃ c, g =ᵐ[μ] const α c := by
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_separating MeasurableSet hs ?_
  refine fun U hU ↦ h.ae_mem_or_ae_nmem₀ (s := g ⁻¹' U) (hgm hU) ?_b
  refine (hg_eq.mono fun x hx ↦ ?_).set_eq
  rw [← preimage_comp, mem_preimage, mem_preimage, hx]

section CountableSeparatingOnUniv

variable [Nonempty X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
  {f : α → α} {g : α → X}

theorem PreErgodic.ae_eq_const_of_ae_eq_comp (h : PreErgodic f μ) (hgm : Measurable g)
    (hg_eq : g ∘ f = g) : ∃ c, g =ᵐ[μ] const α c :=
  exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU ↦
    h.ae_mem_or_ae_nmem (s := g ⁻¹' U) (hgm hU) <| by rw [← preimage_comp, hg_eq]

end CountableSeparatingOnUniv

variable [TopologicalSpace X] [MetrizableSpace X] [Nonempty X] {f : α → α}

namespace QuasiErgodic

theorem ae_eq_const_of_ae_eq_comp_ae {g : α → X} (h : QuasiErgodic f μ)
    (hgm : AEStronglyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c := by
  borelize X
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  haveI := ht.secondCountableTopology
  exact h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ hgt hgm.aemeasurable.nullMeasurable hg_eq

end QuasiErgodic

namespace Ergodic

end Ergodic
