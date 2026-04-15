/-
Extracted from Topology/EMetricSpace/Pi.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Indexed product of extended metric spaces
-/

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

open EMetric

section Pi

open Finset

variable {X : β → Type*} [Fintype β]

-- INSTANCE (free from Core): [∀

theorem edist_le_pi_edist [∀ b, EDist (X b)] (f g : ∀ b, X b) (b : β) :
    edist (f b) (g b) ≤ edist f g :=
  le_sup (f := fun b => edist (f b) (g b)) (Finset.mem_univ b)

theorem edist_pi_le_iff [∀ b, EDist (X b)] {f g : ∀ b, X b} {d : ℝ≥0∞} :
    edist f g ≤ d ↔ ∀ b, edist (f b) (g b) ≤ d :=
  Finset.sup_le_iff.trans <| by simp only [Finset.mem_univ, forall_const]

theorem edist_pi_const_le (a b : α) : (edist (fun _ : β => a) fun _ => b) ≤ edist a b :=
  edist_pi_le_iff.2 fun _ => le_rfl
