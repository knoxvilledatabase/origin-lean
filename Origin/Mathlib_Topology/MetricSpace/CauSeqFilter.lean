/-
Extracted from Topology/MetricSpace/CauSeqFilter.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Completeness in terms of `Cauchy` filters vs `isCauSeq` sequences

In this file we apply `Metric.complete_of_cauchySeq_tendsto` to prove that a `NormedRing`
is complete in terms of `Cauchy` filter if and only if it is complete in terms
of `CauSeq` Cauchy sequences.
-/

universe u v

open Set Filter Topology

variable {β : Type v}

theorem CauSeq.tendsto_limit [NormedRing β] [hn : IsAbsoluteValue (norm : β → ℝ)]
    (f : CauSeq β norm) [CauSeq.IsComplete β norm] : Tendsto f atTop (𝓝 f.lim) :=
  tendsto_nhds.mpr
    (by
      intro s os lfs
      suffices ∃ a : ℕ, ∀ b : ℕ, b ≥ a → f b ∈ s by simpa using this
      rcases Metric.isOpen_iff.1 os _ lfs with ⟨ε, ⟨hε, hεs⟩⟩
      obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ hε
      exists N
      intro b hb
      apply hεs
      dsimp [Metric.ball]
      rw [dist_comm, dist_eq_norm]
      solve_by_elim)

variable [NormedField β]

open Metric

theorem CauchySeq.isCauSeq {f : ℕ → β} (hf : CauchySeq f) : IsCauSeq norm f := by
  obtain ⟨hf1, hf2⟩ := cauchy_iff.1 hf
  intro ε hε
  rcases hf2 { x | dist x.1 x.2 < ε } (dist_mem_uniformity hε) with ⟨t, ⟨ht, htsub⟩⟩
  simp only [mem_map, mem_atTop_sets, mem_preimage] at ht; obtain ⟨N, hN⟩ := ht
  exists N
  intro j hj
  rw [← dist_eq_norm]
  apply @htsub (f j, f N)
  apply Set.mk_mem_prod <;> solve_by_elim [le_refl]

theorem CauSeq.cauchySeq (f : CauSeq β norm) : CauchySeq f := by
  refine cauchy_iff.2 ⟨by infer_instance, fun s hs => ?_⟩
  rcases mem_uniformity_dist.1 hs with ⟨ε, ⟨hε, hεs⟩⟩
  obtain ⟨N, hN⟩ := CauSeq.cauchy₂ f hε
  exists { n | n ≥ N }.image f
  simp only [mem_atTop_sets, mem_map]
  constructor
  · exists N
    intro b hb
    exists b
  · rintro ⟨a, b⟩ ⟨⟨a', ⟨ha'1, ha'2⟩⟩, ⟨b', ⟨hb'1, hb'2⟩⟩⟩
    dsimp at ha'1 ha'2 hb'1 hb'2
    rw [← ha'2, ← hb'2]
    apply hεs
    rw [dist_eq_norm]
    apply hN <;> assumption

theorem isCauSeq_iff_cauchySeq {α : Type u} [NormedField α] {u : ℕ → α} :
    IsCauSeq norm u ↔ CauchySeq u :=
  ⟨fun h => CauSeq.cauchySeq ⟨u, h⟩, fun h => h.isCauSeq⟩

-- INSTANCE (free from Core): (priority
