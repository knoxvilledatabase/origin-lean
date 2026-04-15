/-
Extracted from CategoryTheory/Sites/Coherent/CoherentTopology.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Description of the covering sieves of the coherent topology

This file characterises the covering sieves of the coherent topology.

## Main result

* `coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`: a sieve is a covering sieve for the
  coherent topology if and only if it contains a finite effective epimorphic family.

-/

namespace CategoryTheory

variable {C : Type*} [Category* C] [Precoherent C] {X : C}

theorem coherentTopology.mem_sieves_of_hasEffectiveEpiFamily (S : Sieve X) :
    (∃ (α : Type) (_ : Finite α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a))) →
        (S ∈ (coherentTopology C) X) := by
  intro ⟨α, _, Y, π, hπ⟩
  apply (coherentCoverage C).mem_toGrothendieck_sieves_of_superset (R := Presieve.ofArrows Y π)
  · exact fun _ _ h ↦ by cases h; exact hπ.2 _
  · exact ⟨_, inferInstance, Y, π, rfl, hπ.1⟩

theorem EffectiveEpiFamily.transitive_of_finite {α : Type} [Finite α] {Y : α → C}
    (π : (a : α) → (Y a ⟶ X)) (h : EffectiveEpiFamily Y π) {β : α → Type} [∀ (a : α), Finite (β a)]
    {Y_n : (a : α) → β a → C} (π_n : (a : α) → (b : β a) → (Y_n a b ⟶ Y a))
    (H : ∀ a, EffectiveEpiFamily (Y_n a) (π_n a)) :
    EffectiveEpiFamily
      (fun (c : Σ a, β a) => Y_n c.fst c.snd) (fun c => π_n c.fst c.snd ≫ π c.fst) := by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) ∈ (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentTopology.isSheaf_yoneda_obj W _ h₂
  -- Show that a covering sieve is a colimit, which implies the original set of arrows is regular
  -- epimorphic. We use the transitivity property of saturation
  apply Coverage.Saturate.transitive X (Sieve.generate (Presieve.ofArrows Y π))
  · apply Coverage.Saturate.of
    use α, inferInstance, Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (coherentTopology C).pullback_stable'
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    -- Need to show that the pullback of the family `π_n` to a given `Y i` is effective epimorphic
    obtain ⟨i⟩ := hY
    exact ⟨β i, inferInstance, Y_n i, π_n i, H i, fun b ↦
      ⟨Y_n i b, (𝟙 _), π_n i b ≫ π i, ⟨(⟨i, b⟩ : Σ (i : α), β i)⟩, by simp⟩⟩

-- INSTANCE (free from Core): precoherentEffectiveEpiFamilyCompEffectiveEpis

end CategoryTheory
