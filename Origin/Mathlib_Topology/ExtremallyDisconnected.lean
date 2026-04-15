/-
Extracted from Topology/ExtremallyDisconnected.lean
Genuine: 11 of 14 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.StoneCech

/-!
# Extremally disconnected spaces

An extremally disconnected topological space is a space in which the closure of every open set is
open. Such spaces are also called Stonean spaces. They are the projective objects in the category of
compact Hausdorff spaces.

## Main declarations

* `ExtremallyDisconnected`: Predicate for a space to be extremally disconnected.
* `CompactT2.Projective`: Predicate for a topological space to be a projective object in the
  category of compact Hausdorff spaces.
* `CompactT2.Projective.extremallyDisconnected`: Compact Hausdorff spaces that are projective are
  extremally disconnected.
* `CompactT2.ExtremallyDisconnected.projective`: Extremally disconnected spaces are projective
  objects in the category of compact Hausdorff spaces.

## References

[Gleason, *Projective topological spaces*][gleason1958]
-/

noncomputable section

open Function Set

universe u

variable (X : Type u) [TopologicalSpace X]

class ExtremallyDisconnected : Prop where
  /-- The closure of every open set is open. -/
  open_closure : ∀ U : Set X, IsOpen U → IsOpen (closure U)

theorem extremallyDisconnected_of_homeo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ExtremallyDisconnected X] (e : X ≃ₜ Y) : ExtremallyDisconnected Y where
  open_closure U hU := by
    rw [e.symm.isInducing.closure_eq_preimage_closure_image, Homeomorph.isOpen_preimage]
    exact ExtremallyDisconnected.open_closure _ (e.symm.isOpen_image.mpr hU)

section TotallySeparated

instance [ExtremallyDisconnected X] [T2Space X] : TotallySeparatedSpace X :=

{ isTotallySeparated_univ := by

    intro x _ y _ hxy

    obtain ⟨U, V, hUV⟩ := T2Space.t2 hxy

    refine ⟨closure U, (closure U)ᶜ, ExtremallyDisconnected.open_closure U hUV.1,

      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,

      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩

    rw [Set.mem_compl_iff, mem_closure_iff]

    push_neg

    refine ⟨V, ⟨hUV.2.1, hUV.2.2.2.1, ?_⟩⟩

    rw [← Set.disjoint_iff_inter_eq_empty, disjoint_comm]

    exact hUV.2.2.2.2 }

end TotallySeparated

section

def CompactT2.Projective : Prop :=
  ∀ {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z],
    ∀ [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z],
      ∀ {f : X → Z} {g : Y → Z} (_ : Continuous f) (_ : Continuous g) (_ : Surjective g),
        ∃ h : X → Y, Continuous h ∧ g ∘ h = f

variable {X}

theorem StoneCech.projective [DiscreteTopology X] : CompactT2.Projective (StoneCech X) := by
  intro Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur
  let s : Z → Y := fun z => Classical.choose <| g_sur z
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_sur z)
  let t := s ∘ f ∘ stoneCechUnit
  have ht : Continuous t := continuous_of_discreteTopology
  let h : StoneCech X → Y := stoneCechExtend ht
  have hh : Continuous h := continuous_stoneCechExtend ht
  refine ⟨h, hh, denseRange_stoneCechUnit.equalizer (hg.comp hh) hf ?_⟩
  rw [comp_assoc, stoneCechExtend_extends ht, ← comp_assoc, hs, id_comp]

protected theorem CompactT2.Projective.extremallyDisconnected [CompactSpace X] [T2Space X]
    (h : CompactT2.Projective X) : ExtremallyDisconnected X := by
  refine { open_closure := fun U hU => ?_ }
  let Z₁ : Set (X × Bool) := Uᶜ ×ˢ {true}
  let Z₂ : Set (X × Bool) := closure U ×ˢ {false}
  let Z : Set (X × Bool) := Z₁ ∪ Z₂
  have hZ₁₂ : Disjoint Z₁ Z₂ := disjoint_left.2 fun x hx₁ hx₂ => by cases hx₁.2.symm.trans hx₂.2
  have hZ₁ : IsClosed Z₁ := hU.isClosed_compl.prod (T1Space.t1 _)
  have hZ₂ : IsClosed Z₂ := isClosed_closure.prod (T1Space.t1 false)
  have hZ : IsClosed Z := hZ₁.union hZ₂
  let f : Z → X := Prod.fst ∘ Subtype.val
  have f_cont : Continuous f := continuous_fst.comp continuous_subtype_val
  have f_sur : Surjective f := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨⟨(x, false), Or.inr ⟨subset_closure hx, mem_singleton _⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inl ⟨hx, mem_singleton _⟩⟩, rfl⟩
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur
  let φ := Subtype.val ∘ g
  have hφ : Continuous φ := continuous_subtype_val.comp hg
  have hφ₁ : ∀ x, (φ x).1 = x := congr_fun g_sec
  suffices closure U = φ ⁻¹' Z₂ by
    rw [this, preimage_comp, ← isClosed_compl_iff, ← preimage_compl,
      ← preimage_subtype_coe_eq_compl Subset.rfl]
    · exact hZ₁.preimage hφ
    · rw [hZ₁₂.inter_eq, inter_empty]
  refine (closure_minimal ?_ <| hZ₂.preimage hφ).antisymm fun x hx => ?_
  · intro x hx
    have : φ x ∈ Z₁ ∪ Z₂ := (g x).2
    -- Porting note: Originally `simpa [hx, hφ₁] using this`
    cases' this with hφ hφ
    · exact ((hφ₁ x ▸ hφ.1) hx).elim
    · exact hφ
  · rw [← hφ₁ x]
    exact hx.1

end

section

variable {A D E : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace E]

lemma exists_compact_surjective_zorn_subset [T1Space A] [CompactSpace D] {π : D → A}
    (π_cont : Continuous π) (π_surj : π.Surjective) : ∃ E : Set D, CompactSpace E ∧ π '' E = univ ∧
    ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → E.restrict π '' E₀ ≠ univ := by
  -- suffices to apply Zorn's lemma on the subsets of $D$ that are closed and mapped onto $A$
  let S : Set <| Set D := {E : Set D | IsClosed E ∧ π '' E = univ}
  suffices ∀ (C : Set <| Set D) (_ : C ⊆ S) (_ : IsChain (· ⊆ ·) C), ∃ s ∈ S, ∀ c ∈ C, s ⊆ c by
    rcases zorn_superset S this with ⟨E, E_min⟩
    obtain ⟨E_closed, E_surj⟩ := E_min.prop
    refine ⟨E, isCompact_iff_compactSpace.mp E_closed.isCompact, E_surj, ?_⟩
    intro E₀ E₀_min E₀_closed
    contrapose! E₀_min
    exact eq_univ_of_image_val_eq <|
      E_min.eq_of_subset ⟨E₀_closed.trans E_closed, image_image_val_eq_restrict_image ▸ E₀_min⟩
        image_val_subset
  -- suffices to prove intersection of chain is minimal
  intro C C_sub C_chain
  -- prove intersection of chain is closed
  refine ⟨iInter (fun c : C => c), ⟨isClosed_iInter fun ⟨_, h⟩ => (C_sub h).left, ?_⟩,
    fun c hc _ h => mem_iInter.mp h ⟨c, hc⟩⟩
  -- prove intersection of chain is mapped onto $A$
  by_cases hC : Nonempty C
  · refine eq_univ_of_forall fun a => inter_nonempty_iff_exists_left.mp ?_
    -- apply Cantor's intersection theorem
    refine iInter_inter (ι := C) (π ⁻¹' {a}) _ ▸
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
      ?_ (fun c => ?_) (fun c => IsClosed.isCompact ?_) (fun c => ?_)
    · replace C_chain : IsChain (· ⊇ ·) C := C_chain.symm
      have : ∀ s t : Set D, s ⊇ t → _ ⊇ _ := fun _ _ => inter_subset_inter_left <| π ⁻¹' {a}
      exact (directedOn_iff_directed.mp C_chain.directedOn).mono_comp (· ⊇ ·) this
    · rw [← image_inter_nonempty_iff, (C_sub c.mem).right, univ_inter]
      exact singleton_nonempty a
    all_goals exact (C_sub c.mem).left.inter <| (T1Space.t1 a).preimage π_cont
  · rw [@iInter_of_empty _ _ <| not_nonempty_iff.mp hC, image_univ_of_surjective π_surj]

lemma image_subset_closure_compl_image_compl_of_isOpen {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ)
    {G : Set E} (hG : IsOpen G) : ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ) := by
  -- suffices to prove for nonempty $G$
  by_cases G_empty : G = ∅
  · simpa only [G_empty, image_empty] using empty_subset _
  · -- let $a \in \rho(G)$
    intro a ha
    rw [mem_closure_iff]
    -- let $N$ be a neighbourhood of $a$
    intro N N_open hN
    -- get $x \in A$ from nonempty open $G \cap \rho^{-1}(N)$
    rcases (G.mem_image ρ a).mp ha with ⟨e, he, rfl⟩
    have nonempty : (G ∩ ρ⁻¹' N).Nonempty := ⟨e, mem_inter he <| mem_preimage.mpr hN⟩
    have is_open : IsOpen <| G ∩ ρ⁻¹' N := hG.inter <| N_open.preimage ρ_cont
    have ne_univ : ρ '' (G ∩ ρ⁻¹' N)ᶜ ≠ univ :=
      zorn_subset _ (compl_ne_univ.mpr nonempty) is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_univ with ⟨x, hx⟩
    -- prove $x \in N \cap (A \setminus \rho(E \setminus G))$
    have hx' : x ∈ (ρ '' Gᶜ)ᶜ := fun h => hx <| image_subset ρ (by simp) h
    rcases ρ_surj x with ⟨y, rfl⟩
    have hy : y ∈ G ∩ ρ⁻¹' N := by simpa using mt (mem_image_of_mem ρ) <| mem_compl hx
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩

lemma ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen [ExtremallyDisconnected A]
    {U₁ U₂ : Set A} (h : Disjoint U₁ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) :
    Disjoint (closure U₁) (closure U₂) :=
  (h.closure_right hU₁).closure_left <| open_closure U₂ hU₂

private lemma ExtremallyDisconnected.homeoCompactToT2_injective [ExtremallyDisconnected A]
    [T2Space A] [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) :
    ρ.Injective := by
  -- let $x_1, x_2 \in E$ be distinct points such that $\rho(x_1) = \rho(x_2)$
  intro x₁ x₂ hρx
  by_contra hx
  -- let $G_1$ and $G_2$ be disjoint open neighbourhoods of $x_1$ and $x_2$ respectively
  rcases t2_separation hx with ⟨G₁, G₂, G₁_open, G₂_open, hx₁, hx₂, disj⟩
  -- prove $A \setminus \rho(E - G_1)$ and $A \setminus \rho(E - G_2)$ are disjoint
  have G₁_comp : IsCompact G₁ᶜ := IsClosed.isCompact G₁_open.isClosed_compl
  have G₂_comp : IsCompact G₂ᶜ := IsClosed.isCompact G₂_open.isClosed_compl
  have G₁_open' : IsOpen (ρ '' G₁ᶜ)ᶜ := (G₁_comp.image ρ_cont).isClosed.isOpen_compl
  have G₂_open' : IsOpen (ρ '' G₂ᶜ)ᶜ := (G₂_comp.image ρ_cont).isClosed.isOpen_compl
  have disj' : Disjoint (ρ '' G₁ᶜ)ᶜ (ρ '' G₂ᶜ)ᶜ := by
    rw [disjoint_iff_inter_eq_empty, ← compl_union, ← image_union, ← compl_inter,
      disjoint_iff_inter_eq_empty.mp disj, compl_empty, compl_empty_iff,
      image_univ_of_surjective ρ_surj]
  -- apply Lemma 2.2 to prove their closures are disjoint
  have disj'' : Disjoint (closure (ρ '' G₁ᶜ)ᶜ) (closure (ρ '' G₂ᶜ)ᶜ) :=
    disjoint_closure_of_disjoint_isOpen disj' G₁_open' G₂_open'
  -- apply Lemma 2.1 to prove $\rho(x_1) = \rho(x_2)$ lies in their intersection
  have hx₁' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₁_open <|
    mem_image_of_mem ρ hx₁
  have hx₂' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₂_open <|
    mem_image_of_mem ρ hx₂
  exact disj''.ne_of_mem hx₁' hx₂' hρx

noncomputable def ExtremallyDisconnected.homeoCompactToT2 [ExtremallyDisconnected A] [T2Space A]
    [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ) (ρ_surj : ρ.Surjective)
    (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) : E ≃ₜ A :=
  ρ_cont.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨homeoCompactToT2_injective ρ_cont ρ_surj zorn_subset, ρ_surj⟩)

protected theorem CompactT2.ExtremallyDisconnected.projective [ExtremallyDisconnected A]
    [CompactSpace A] [T2Space A] : CompactT2.Projective A := by
  -- let $B$ and $C$ be compact; let $f : B \twoheadrightarrow C$ and $\phi : A \to C$ be continuous
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  -- let $D := \{(a, b) : \phi(a) = f(b)\}$ with projections $\pi_1 : D \to A$ and $\pi_2 : D \to B$
  let D : Set <| A × B := {x | φ x.fst = f x.snd}
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  -- apply Lemma 2.4 to get closed $E$ satisfying "Zorn subset condition"
  let π₁ : D → A := Prod.fst ∘ Subtype.val
  have π₁_cont : Continuous π₁ := continuous_fst.comp continuous_subtype_val
  have π₁_surj : π₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  rcases exists_compact_surjective_zorn_subset π₁_cont π₁_surj with ⟨E, _, E_onto, E_min⟩
  -- apply Lemma 2.3 to get homeomorphism $\pi_1|_E : E \to A$
  let ρ : E → A := E.restrict π₁
  have ρ_cont : Continuous ρ := π₁_cont.continuousOn.restrict
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_onto ▸ mem_univ a : a ∈ π₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := ExtremallyDisconnected.homeoCompactToT2 ρ_cont ρ_surj E_min
  -- prove $\rho := \pi_2|_E \circ \pi_1|_E^{-1}$ satisfies $\phi = f \circ \rho$
  let π₂ : D → B := Prod.snd ∘ Subtype.val
  have π₂_cont : Continuous π₂ := continuous_snd.comp continuous_subtype_val
  refine ⟨E.restrict π₂ ∘ ρ'.symm, ⟨π₂_cont.continuousOn.restrict.comp ρ'.symm.continuous, ?_⟩⟩
  suffices f ∘ E.restrict π₂ = φ ∘ ρ' by
    rw [← comp_assoc, this, comp_assoc, Homeomorph.self_comp_symm, comp_id]
  ext x
  exact x.val.mem.symm

protected theorem CompactT2.projective_iff_extremallyDisconnected [CompactSpace A] [T2Space A] :
    Projective A ↔ ExtremallyDisconnected A :=
  ⟨Projective.extremallyDisconnected, fun _ => ExtremallyDisconnected.projective⟩

alias CompactT2.projective_iff_extremallyDisconnnected :=
  CompactT2.projective_iff_extremallyDisconnected

end

instance instExtremallyDisconnected {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [h₀ : ∀ i, ExtremallyDisconnected (π i)] : ExtremallyDisconnected (Σ i, π i) := by
  constructor
  intro s hs
  rw [isOpen_sigma_iff] at hs ⊢
  intro i
  rcases h₀ i with ⟨h₀⟩
  suffices h : Sigma.mk i ⁻¹' closure s = closure (Sigma.mk i ⁻¹' s) by
    rw [h]
    exact h₀ _ (hs i)
  apply IsOpenMap.preimage_closure_eq_closure_preimage
  · intro U _
    rw [isOpen_sigma_iff]
    intro j
    by_cases ij : i = j
    · rwa [← ij, sigma_mk_preimage_image_eq_self]
    · rw [sigma_mk_preimage_image' ij]
      exact isOpen_empty
  · continuity

end
