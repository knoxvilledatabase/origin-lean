/-
Extracted from MeasureTheory/MeasurableSpace/Embedding.lean
Genuine: 18 of 18 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Measurable embeddings and equivalences

A measurable equivalence between measurable spaces is an equivalence
which respects the σ-algebras, that is, for which both directions of
the equivalence are measurable functions.

## Main definitions

* `MeasurableEmbedding`: a map `f : α → β` is called a *measurable embedding* if it is injective,
  measurable, and sends measurable sets to measurable sets.
* `MeasurableEquiv`: an equivalence `α ≃ β` is a *measurable equivalence* if its forward and inverse
  functions are measurable.

We prove a multitude of elementary lemmas about these, and one more substantial theorem:

* `MeasurableEmbedding.schroederBernstein`: the **measurable Schröder-Bernstein Theorem**: given
  measurable embeddings `α → β` and `β → α`, we can find a measurable equivalence `α ≃ᵐ β`.

## Notation

* We write `α ≃ᵐ β` for measurable equivalences between the measurable spaces `α` and `β`.
  This should not be confused with `≃ₘ` which is used for diffeomorphisms between manifolds.

## Tags

measurable equivalence, measurable embedding
-/

open Set Function Equiv MeasureTheory

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s t u : Set α}

structure MeasurableEmbedding [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop where
  /-- A measurable embedding is injective. -/
  protected injective : Injective f
  /-- A measurable embedding is a measurable function. -/
  protected measurable : Measurable f
  /-- The image of a measurable set under a measurable embedding is a measurable set. -/
  protected measurableSet_image' : ∀ ⦃s⦄, MeasurableSet s → MeasurableSet (f '' s)

attribute [fun_prop] MeasurableEmbedding.measurable

namespace MeasurableEmbedding

variable {mα : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {g : β → γ}

theorem measurableSet_image (hf : MeasurableEmbedding f) :
    MeasurableSet (f '' s) ↔ MeasurableSet s :=
  ⟨fun h => by simpa only [hf.injective.preimage_image] using hf.measurable h, fun h =>
    hf.measurableSet_image' h⟩

theorem id : MeasurableEmbedding (id : α → α) :=
  ⟨injective_id, measurable_id, fun s hs => by rwa [image_id]⟩

theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (g ∘ f) :=
  ⟨hg.injective.comp hf.injective, hg.measurable.comp hf.measurable, fun s hs => by
    rwa [image_comp, hg.measurableSet_image, hf.measurableSet_image]⟩

theorem subtype_coe (hs : MeasurableSet s) : MeasurableEmbedding ((↑) : s → α) where
  injective := Subtype.coe_injective
  measurable := measurable_subtype_coe
  measurableSet_image' := fun _ => MeasurableSet.subtype_image hs

theorem measurableSet_range (hf : MeasurableEmbedding f) : MeasurableSet (range f) := by
  rw [← image_univ]
  exact hf.measurableSet_image' MeasurableSet.univ

theorem measurableSet_preimage (hf : MeasurableEmbedding f) {s : Set β} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [← image_preimage_eq_inter_range, hf.measurableSet_image]

theorem measurable_rangeSplitting (hf : MeasurableEmbedding f) :
    Measurable (rangeSplitting f) := fun s hs => by
  rwa [preimage_rangeSplitting hf.injective,
    ← (subtype_coe hf.measurableSet_range).measurableSet_image, ← image_comp,
    coe_comp_rangeFactorization, hf.measurableSet_image]

theorem measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} {g' : β → γ} (hg : Measurable g)
    (hg' : Measurable g') : Measurable (extend f g g') := by
  refine measurable_of_restrict_of_restrict_compl hf.measurableSet_range ?_ ?_
  · rw [restrict_extend_range]
    simpa only [rangeSplitting] using hg.comp hf.measurable_rangeSplitting
  · rw [restrict_extend_compl_range]
    exact hg'.comp measurable_subtype_coe

theorem exists_measurable_extend (hf : MeasurableEmbedding f) {g : α → γ} (hg : Measurable g)
    (hne : β → Nonempty γ) : ∃ g' : β → γ, Measurable g' ∧ g' ∘ f = g :=
  ⟨extend f g fun x => Classical.choice (hne x),
    hf.measurable_extend hg (measurable_const' fun _ _ => rfl),
    funext fun _ => hf.injective.extend_apply _ _ _⟩

theorem measurable_comp_iff (hg : MeasurableEmbedding g) : Measurable (g ∘ f) ↔ Measurable f := by
  refine ⟨fun H => ?_, hg.measurable.comp⟩
  suffices Measurable ((rangeSplitting g ∘ rangeFactorization g) ∘ f) by
    rwa [(rightInverse_rangeSplitting hg.injective).comp_eq_id] at this
  exact hg.measurable_rangeSplitting.comp H.subtype_mk

lemma natCast {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddMonoidWithOne α] [CharZero α] :
    MeasurableEmbedding (Nat.cast : ℕ → α) where
  injective := Nat.cast_injective
  measurable := measurable_from_nat
  measurableSet_image' := fun _ _ =>
    ((Set.countable_range (Nat.cast : ℕ → α)).mono
      (Set.image_subset_range _ _)).measurableSet

end MeasurableEmbedding

section gluing

variable {α₁ α₂ α₃ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mα₁ : MeasurableSpace α₁} {mα₂ : MeasurableSpace α₂} {mα₃ : MeasurableSpace α₃}
  {i₁ : α₁ → α} {i₂ : α₂ → α} {i₃ : α₃ → α} {s : Set α} {f : α → β}

lemma MeasurableSet.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ ⊆ range i₁ ∪ range i₂)
    (hs₁ : MeasurableSet (i₁ ⁻¹' s)) (hs₂ : MeasurableSet (i₂ ⁻¹' s)) : MeasurableSet s := by
  convert (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

lemma MeasurableSet.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ ⊆ range i₁ ∪ range i₂ ∪ range i₃) (hs₁ : MeasurableSet (i₁ ⁻¹' s))
    (hs₂ : MeasurableSet (i₂ ⁻¹' s)) (hs₃ : MeasurableSet (i₃ ⁻¹' s)) : MeasurableSet s := by
  convert (hi₁.measurableSet_image' hs₁).union (hi₂.measurableSet_image' hs₂) |>.union
    (hi₃.measurableSet_image' hs₃)
  simp [image_preimage_eq_range_inter, ← union_inter_distrib_right, univ_subset_iff.1 h]

lemma Measurable.of_union_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (h : univ ⊆ range i₁ ∪ range i₂)
    (hf₁ : Measurable (f ∘ i₁)) (hf₂ : Measurable (f ∘ i₂)) : Measurable f :=
  fun _s hs ↦ .of_union_range_cover hi₁ hi₂ h (hf₁ hs) (hf₂ hs)

lemma Measurable.of_union₃_range_cover (hi₁ : MeasurableEmbedding i₁)
    (hi₂ : MeasurableEmbedding i₂) (hi₃ : MeasurableEmbedding i₃)
    (h : univ ⊆ range i₁ ∪ range i₂ ∪ range i₃) (hf₁ : Measurable (f ∘ i₁))
    (hf₂ : Measurable (f ∘ i₂)) (hf₃ : Measurable (f ∘ i₃)) : Measurable f :=
  fun _s hs ↦ .of_union₃_range_cover hi₁ hi₂ hi₃ h (hf₁ hs) (hf₂ hs) (hf₃ hs)

end gluing

theorem MeasurableSet.exists_measurable_proj {_ : MeasurableSpace α}
    (hs : MeasurableSet s) (hne : s.Nonempty) : ∃ f : α → s, Measurable f ∧ ∀ x : s, f x = x :=
  let ⟨f, hfm, hf⟩ :=
    (MeasurableEmbedding.subtype_coe hs).exists_measurable_extend measurable_id fun _ =>
      hne.to_subtype
  ⟨f, hfm, congr_fun hf⟩

structure MeasurableEquiv (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends α ≃ β where
  /-- The forward function of a measurable equivalence is measurable. -/
  measurable_toFun : Measurable toEquiv := by measurability
  /-- The inverse function of a measurable equivalence is measurable. -/
  measurable_invFun : Measurable toEquiv.symm := by measurability
