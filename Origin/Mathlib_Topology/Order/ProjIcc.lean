/-
Extracted from Topology/Order/ProjIcc.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projection onto a closed interval

In this file we prove that the projection `Set.projIcc f a b h` is a quotient map, and use it
to show that `Set.IccExtend h f` is continuous if and only if `f` is continuous.
-/

open Set Filter Topology

variable {α β γ : Type*} [LinearOrder α] {a b c : α} {h : a ≤ b}

protected theorem Filter.Tendsto.IccExtend (f : γ → Icc a b → β) {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (hf : Tendsto ↿f (lc ×ˢ la.map (projIcc a b h)) lb) :
    Tendsto (↿(IccExtend h ∘ f)) (lc ×ˢ la) lb :=
  hf.comp <| tendsto_id.prodMap tendsto_map

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]
