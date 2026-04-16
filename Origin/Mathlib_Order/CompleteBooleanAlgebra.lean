/-
Extracted from Order/CompleteBooleanAlgebra.lean
Genuine: 83 | Conflates: 0 | Dissolved: 0 | Infrastructure: 31
-/
import Origin.Core
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Directed
import Mathlib.Logic.Equiv.Set

noncomputable section

/-!
# Frames, completely distributive lattices and complete Boolean algebras

In this file we define and provide API for (co)frames, completely distributive lattices and
complete Boolean algebras.

We distinguish two different distributivity properties:
 1. `inf_iSup_eq : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i` (finite `⊓` distributes over infinite `⨆`).
  This is required by `Frame`, `CompleteDistribLattice`, and `CompleteBooleanAlgebra`
  (`Coframe`, etc., require the dual property).
 2. `iInf_iSup_eq : (⨅ i, ⨆ j, f i j) = ⨆ s, ⨅ i, f i (s i)`
  (infinite `⨅` distributes over infinite `⨆`).
  This stronger property is called "completely distributive",
  and is required by `CompletelyDistribLattice` and `CompleteAtomicBooleanAlgebra`.

## Typeclasses

* `Order.Frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `Order.Coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `CompleteDistribLattice`: Complete distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompletelyDistribLattice`: Completely distributive lattices: A complete lattice whose
  `⨅` and `⨆` satisfy `iInf_iSup_eq`.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompleteAtomicBooleanAlgebra`: Complete atomic Boolean algebra:
  A complete Boolean algebra which is additionally completely distributive.
  (This implies that it's (co)atom(ist)ic.)

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `Filter` is a coframe but not a completely
distributive lattice.

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

open Function Set

universe u v w w'

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

class Order.Frame.MinimalAxioms (α : Type u) extends CompleteLattice α where
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b

class Order.Coframe.MinimalAxioms (α : Type u) extends CompleteLattice α where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

class Order.Frame (α : Type*) extends CompleteLattice α, HeytingAlgebra α where
  /-- `⊓` distributes over `⨆`. -/
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b

class Order.Coframe (α : Type*) extends CompleteLattice α, CoheytingAlgebra α where
  /-- `⊔` distributes over `⨅`. -/
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

open Order

structure CompleteDistribLattice.MinimalAxioms (α : Type u)
    extends CompleteLattice α, Frame.MinimalAxioms α, Coframe.MinimalAxioms α where

attribute [nolint docBlame] CompleteDistribLattice.MinimalAxioms.toMinimalAxioms
  CompleteDistribLattice.MinimalAxioms.toMinimalAxioms_1

class CompleteDistribLattice (α : Type*) extends Frame α, Coframe α, BiheytingAlgebra α

structure CompletelyDistribLattice.MinimalAxioms (α : Type u) extends CompleteLattice α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

class CompletelyDistribLattice (α : Type u) extends CompleteLattice α, BiheytingAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

theorem le_iInf_iSup [CompleteLattice α] {f : ∀ a, κ a → α} :
    (⨆ g : ∀ a, κ a, ⨅ a, f a (g a)) ≤ ⨅ a, ⨆ b, f a b :=
  iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)

lemma iSup_iInf_le [CompleteLattice α] {f : ∀ a, κ a → α} :
    ⨆ a, ⨅ b, f a b ≤ ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  le_iInf_iSup (α := αᵒᵈ)

namespace Order.Frame.MinimalAxioms

variable (minAx : MinimalAxioms α) {s : Set α} {a b : α}

lemma inf_sSup_eq : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  (minAx.inf_sSup_le_iSup_inf _ _).antisymm iSup_inf_le_inf_sSup

lemma sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

lemma iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]

lemma inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using minAx.iSup_inf_eq f a

lemma inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ i, ⨆ j, f i j) = ⨆ i, ⨆ j, a ⊓ f i j := by
  simp only [inf_iSup_eq]

def of [Frame α] : MinimalAxioms α := { ‹Frame α› with }

end MinimalAxioms

abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : Frame α where
  __ := minAx
  himp a b := sSup {c | c ⊓ a ≤ b}
  le_himp_iff _ b c :=
    ⟨fun h ↦ (inf_le_inf_right _ h).trans (by simp [minAx.sSup_inf_eq]), fun h ↦ le_sSup h⟩
  himp_bot _ := rfl

end Order.Frame

namespace Order.Coframe.MinimalAxioms

variable (minAx : MinimalAxioms α) {s : Set α} {a b : α}

lemma sup_sInf_eq : a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  sup_sInf_le_iInf_sup.antisymm (minAx.iInf_sup_le_sup_sInf _ _)

lemma sInf_sup_eq : sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b := by
  simpa only [sup_comm] using @sup_sInf_eq α _ s b

lemma iInf_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a := by
  rw [iInf, sInf_sup_eq, iInf_range]

lemma sup_iInf_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i := by
  simpa only [sup_comm] using minAx.iInf_sup_eq f a

lemma sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ i, ⨅ j, f i j) = ⨅ i, ⨅ j, a ⊔ f i j := by
  simp only [sup_iInf_eq]

def of [Coframe α] : MinimalAxioms α := { ‹Coframe α› with }

end MinimalAxioms

abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : Coframe α where
  __ := minAx
  sdiff a b := sInf {c | a ≤ b ⊔ c}
  sdiff_le_iff a b _ :=
    ⟨fun h ↦ (sup_le_sup_left h _).trans' (by simp [minAx.sup_sInf_eq]), fun h ↦ sInf_le h⟩
  top_sdiff _ := rfl

end Order.Coframe

namespace CompleteDistribLattice.MinimalAxioms

variable (minAx : MinimalAxioms α)

def of [CompleteDistribLattice α] : MinimalAxioms α := { ‹CompleteDistribLattice α› with }

abbrev toFrame : Frame.MinimalAxioms α := minAx.toMinimalAxioms

abbrev toCoframe : Coframe.MinimalAxioms α where __ := minAx

end MinimalAxioms

abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : CompleteDistribLattice α where
  __ := Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

end CompleteDistribLattice

namespace CompletelyDistribLattice.MinimalAxioms

variable (minAx : MinimalAxioms α)

lemma iInf_iSup_eq' (f : ∀ a, κ a → α) :
    let _ := minAx.toCompleteLattice
    ⨅ i, ⨆ j, f i j = ⨆ g : ∀ i, κ i, ⨅ i, f i (g i) := by
  let _ := minAx.toCompleteLattice
  refine le_antisymm ?_ le_iInf_iSup
  calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
    _ = _ := minAx.iInf_iSup_eq _
    _ ≤ _ := iSup_le fun g => by
      refine le_trans ?_ <| le_iSup _ fun a => Classical.choose (g ⟨_, a, rfl⟩).2
      refine le_iInf fun a => le_trans (iInf_le _ ⟨range (f a), a, rfl⟩) ?_
      rw [← Classical.choose_spec (g ⟨_, a, rfl⟩).2]

lemma iSup_iInf_eq (f : ∀ i, κ i → α) :
    let _ := minAx.toCompleteLattice
    ⨆ i, ⨅ j, f i j = ⨅ g : ∀ i, κ i, ⨆ i, f i (g i) := by
  let _ := minAx.toCompleteLattice
  refine le_antisymm iSup_iInf_le ?_
  rw [minAx.iInf_iSup_eq']
  refine iSup_le fun g => ?_
  have ⟨a, ha⟩ : ∃ a, ∀ b, ∃ f, ∃ h : a = g f, h ▸ b = f (g f) := of_not_not fun h => by
    push_neg at h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a)
  refine le_iInf fun b => ?_
  obtain ⟨h, rfl, rfl⟩ := ha b
  exact iInf_le _ _

abbrev toCompleteDistribLattice : CompleteDistribLattice.MinimalAxioms α where
  __ := minAx
  inf_sSup_le_iSup_inf a s := by
    let _ := minAx.toCompleteLattice
    calc
      _ = ⨅ i : ULift.{u} Bool, ⨆ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by simp [le_antisymm_iff, sSup_eq_iSup', iSup_unique, iInf_bool_eq]
      _ ≤ _ := by
        simp only [minAx.iInf_iSup_eq, iInf_ulift, iInf_bool_eq, iSup_le_iff]
        exact fun x ↦ le_biSup _ (x (.up false)).2
  iInf_sup_le_sup_sInf a s := by
    let _ := minAx.toCompleteLattice
    calc
      _ ≤ ⨆ i : ULift.{u} Bool, ⨅ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by
        simp only [minAx.iSup_iInf_eq, iSup_ulift, iSup_bool_eq, le_iInf_iff]
        exact fun x ↦ biInf_le _ (x (.up false)).2
      _ = _ := by simp [le_antisymm_iff, sInf_eq_iInf', iInf_unique, iSup_bool_eq]

def of [CompletelyDistribLattice α] : MinimalAxioms α := { ‹CompletelyDistribLattice α› with }

end MinimalAxioms

abbrev ofMinimalAxioms (minAx : MinimalAxioms α) : CompletelyDistribLattice α where
  __ := minAx
  __ := CompleteDistribLattice.ofMinimalAxioms minAx.toCompleteDistribLattice

end CompletelyDistribLattice

theorem iInf_iSup_eq [CompletelyDistribLattice α] {f : ∀ a, κ a → α} :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a) :=
  CompletelyDistribLattice.MinimalAxioms.of.iInf_iSup_eq' _

theorem iSup_iInf_eq [CompletelyDistribLattice α] {f : ∀ a, κ a → α} :
    (⨆ a, ⨅ b, f a b) = ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  CompletelyDistribLattice.MinimalAxioms.of.iSup_iInf_eq _

instance (priority := 100) CompletelyDistribLattice.toCompleteDistribLattice
    [CompletelyDistribLattice α] : CompleteDistribLattice α where
  __ := ‹CompletelyDistribLattice α›
  __ := CompleteDistribLattice.ofMinimalAxioms MinimalAxioms.of.toCompleteDistribLattice

instance (priority := 100) CompleteLinearOrder.toCompletelyDistribLattice [CompleteLinearOrder α] :
    CompletelyDistribLattice α where
  __ := ‹CompleteLinearOrder α›
  iInf_iSup_eq {α β} g := by
    let lhs := ⨅ a, ⨆ b, g a b
    let rhs := ⨆ h : ∀ a, β a, ⨅ a, g a (h a)
    suffices lhs ≤ rhs from le_antisymm this le_iInf_iSup
    if h : ∃ x, rhs < x ∧ x < lhs then
      rcases h with ⟨x, hr, hl⟩
      suffices rhs ≥ x from nomatch not_lt.2 this hr
      have : ∀ a, ∃ b, x < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_not_le fun h =>
            lt_irrefl x (lt_of_lt_of_le hl (le_trans (iInf_le _ a) h))
      choose f hf using this
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => le_of_lt (hf a)
    else
      refine le_of_not_lt fun hrl : rhs < lhs => not_le_of_lt hrl ?_
      replace h : ∀ x, x ≤ rhs ∨ lhs ≤ x := by
        simpa only [not_exists, not_and_or, not_or, not_lt] using h
      have : ∀ a, ∃ b, rhs < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_lt_of_le hrl (iInf_le _ a)
      choose f hf using this
      have : ∀ a, lhs ≤ g a (f a) := fun a =>
        (h (g a (f a))).resolve_left (by simpa using hf a)
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => this _

section Frame

variable [Frame α] {s t : Set α} {a b : α}

instance OrderDual.instCoframe : Coframe αᵒᵈ where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra
  iInf_sup_le_sup_sInf := @Frame.inf_sSup_le_iSup_inf α _

theorem inf_sSup_eq : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  (Frame.inf_sSup_le_iSup_inf _ _).antisymm iSup_inf_le_inf_sSup

theorem sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

theorem iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]

theorem inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a

theorem iSup₂_inf_eq {f : ∀ i, κ i → α} (a : α) :
    (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a := by
  simp only [iSup_inf_eq]

theorem inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) :
    (a ⊓ ⨆ (i) (j), f i j) = ⨆ (i) (j), a ⊓ f i j := by
  simp only [inf_iSup_eq]

theorem iSup_inf_iSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]

theorem biSup_inf_biSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl

theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]

theorem iSup_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]

theorem disjoint_iSup_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @iSup_disjoint_iff

theorem iSup₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [iSup_disjoint_iff]

theorem disjoint_iSup₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_iSup_iff]

theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]

theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using @sSup_disjoint_iff

theorem iSup_inf_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine (le_iSup_inf_iSup f g).antisymm ?_
  rw [iSup_inf_iSup]
  refine iSup_mono' fun i => ?_
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

theorem iSup_inf_of_antitone {ι : Type*} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i :=
  @iSup_inf_of_monotone α _ ιᵒᵈ _ _ f g hf.dual_left hg.dual_left

instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair, ← sSup_pair, inf_sSup_eq, ← sSup_image, image_pair]

instance Prod.instFrame [Frame α] [Frame β] : Frame (α × β) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra
  inf_sSup_le_iSup_inf a s := by
    simp [Prod.le_def, sSup_eq_iSup, fst_iSup, snd_iSup, fst_iInf, snd_iInf, inf_iSup_eq]

instance Pi.instFrame {ι : Type*} {π : ι → Type*} [∀ i, Frame (π i)] : Frame (∀ i, π i) where
  __ := instCompleteLattice
  __ := instHeytingAlgebra
  inf_sSup_le_iSup_inf a s i := by
    simp only [sSup_apply, iSup_apply, inf_apply, inf_iSup_eq, ← iSup_subtype'']; rfl

end Frame

section Coframe

variable [Coframe α] {s t : Set α} {a b : α}

instance OrderDual.instFrame : Frame αᵒᵈ where
  __ := instCompleteLattice
  __ := instHeytingAlgebra
  inf_sSup_le_iSup_inf := @Coframe.iInf_sup_le_sup_sInf α _

theorem sup_sInf_eq : a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  @inf_sSup_eq αᵒᵈ _ _ _

theorem sInf_sup_eq : sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b :=
  @sSup_inf_eq αᵒᵈ _ _ _

theorem iInf_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
  @iSup_inf_eq αᵒᵈ _ _ _ _

theorem sup_iInf_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i :=
  @inf_iSup_eq αᵒᵈ _ _ _ _

theorem iInf₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @iSup₂_inf_eq αᵒᵈ _ _ _ _ _

theorem sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ (i) (j), f i j) = ⨅ (i) (j), a ⊔ f i j :=
  @inf_iSup₂_eq αᵒᵈ _ _ _ _ _

theorem iInf_sup_iInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @iSup_inf_iSup αᵒᵈ _ _ _ _ _

theorem biInf_sup_biInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @biSup_inf_biSup αᵒᵈ _ _ _ _ _ _ _

theorem sInf_sup_sInf : sInf s ⊔ sInf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @sSup_inf_sSup αᵒᵈ _ _ _

theorem iInf_sup_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_antitone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right

theorem iInf_sup_of_antitone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_monotone αᵒᵈ _ _ _ _ _ _ hf.dual_right hg.dual_right

instance (priority := 100) Coframe.toDistribLattice : DistribLattice α where
  __ := ‹Coframe α›
  le_sup_inf a b c := by
    rw [← sInf_pair, ← sInf_pair, sup_sInf_eq, ← sInf_image, image_pair]

instance Prod.instCoframe [Coframe β] : Coframe (α × β) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra
  iInf_sup_le_sup_sInf a s := by
    simp [Prod.le_def, sInf_eq_iInf, fst_iSup, snd_iSup, fst_iInf, snd_iInf, sup_iInf_eq]

instance Pi.instCoframe {ι : Type*} {π : ι → Type*} [∀ i, Coframe (π i)] : Coframe (∀ i, π i) where
  __ := instCompleteLattice
  __ := instCoheytingAlgebra
  iInf_sup_le_sup_sInf a s i := by
    simp only [sInf_apply, iInf_apply, sup_apply, sup_iInf_eq, ← iInf_subtype'']; rfl

end Coframe

section CompleteDistribLattice

variable [CompleteDistribLattice α]

instance OrderDual.instCompleteDistribLattice [CompleteDistribLattice α] :
    CompleteDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe

instance Prod.instCompleteDistribLattice [CompleteDistribLattice β] :
    CompleteDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe

instance Pi.instCompleteDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteDistribLattice (π i)] : CompleteDistribLattice (∀ i, π i) where
  __ := instFrame
  __ := instCoframe

end CompleteDistribLattice

section CompletelyDistribLattice

instance OrderDual.instCompletelyDistribLattice [CompletelyDistribLattice α] :
    CompletelyDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq _ := iSup_iInf_eq (α := α)

instance Prod.instCompletelyDistribLattice [CompletelyDistribLattice α]
    [CompletelyDistribLattice β] : CompletelyDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]

instance Pi.instCompletelyDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, CompletelyDistribLattice (π i)] : CompletelyDistribLattice (∀ i, π i) where
  __ := instFrame
  __ := instCoframe
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]

end CompletelyDistribLattice

class CompleteBooleanAlgebra (α) extends CompleteLattice α, BooleanAlgebra α where
  /-- `⊓` distributes over `⨆`. -/
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b
  /-- `⊔` distributes over `⨅`. -/
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

instance (priority := 100) CompleteBooleanAlgebra.toCompleteDistribLattice
    [CompleteBooleanAlgebra α] : CompleteDistribLattice α where
  __ := ‹CompleteBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra

instance Prod.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] [CompleteBooleanAlgebra β] :
    CompleteBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

instance Pi.instCompleteBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteBooleanAlgebra (π i)] : CompleteBooleanAlgebra (∀ i, π i) where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

instance OrderDual.instCompleteBooleanAlgebra [CompleteBooleanAlgebra α] :
    CompleteBooleanAlgebra αᵒᵈ where
  __ := instBooleanAlgebra
  __ := instCompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] {s : Set α} {f : ι → α}

theorem compl_iInf : (iInf f)ᶜ = ⨆ i, (f i)ᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (HasCompl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)

theorem compl_iSup : (iSup f)ᶜ = ⨅ i, (f i)ᶜ :=
  compl_injective (by simp [compl_iInf])

theorem compl_sInf : (sInf s)ᶜ = ⨆ i ∈ s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]

theorem compl_sSup : (sSup s)ᶜ = ⨅ i ∈ s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]

theorem compl_sInf' : (sInf s)ᶜ = sSup (HasCompl.compl '' s) :=
  compl_sInf.trans sSup_image.symm

theorem compl_sSup' : (sSup s)ᶜ = sInf (HasCompl.compl '' s) :=
  compl_sSup.trans sInf_image.symm

open scoped symmDiff in

theorem iSup_symmDiff_iSup_le {g : ι → α} : (⨆ i, f i) ∆ (⨆ i, g i) ≤ ⨆ i, ((f i) ∆ (g i)) := by
  simp_rw [symmDiff_le_iff, ← iSup_sup_eq]
  exact ⟨iSup_mono fun i ↦ sup_comm (g i) _ ▸ le_symmDiff_sup_right ..,
    iSup_mono fun i ↦ sup_comm (f i) _ ▸ symmDiff_comm (f i) _ ▸ le_symmDiff_sup_right ..⟩

open scoped symmDiff in

theorem biSup_symmDiff_biSup_le {p : ι → Prop} {f g : (i : ι) → p i → α} :
    (⨆ i, ⨆ (h : p i), f i h) ∆ (⨆ i, ⨆ (h : p i), g i h) ≤
    ⨆ i, ⨆ (h : p i), ((f i h) ∆ (g i h)) :=
  le_trans iSup_symmDiff_iSup_le <|iSup_mono fun _ ↦ iSup_symmDiff_iSup_le

end CompleteBooleanAlgebra

class CompleteAtomicBooleanAlgebra (α : Type u) extends CompleteLattice α, BooleanAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

instance (priority := 100) CompleteAtomicBooleanAlgebra.toCompletelyDistribLattice
    [CompleteAtomicBooleanAlgebra α] : CompletelyDistribLattice α where
  __ := ‹CompleteAtomicBooleanAlgebra α›
  __ := BooleanAlgebra.toBiheytingAlgebra

instance (priority := 100) CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra
    [CompleteAtomicBooleanAlgebra α] : CompleteBooleanAlgebra α where
  __ := ‹CompleteAtomicBooleanAlgebra α›
  __ := CompletelyDistribLattice.toCompleteDistribLattice

instance Prod.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α]
    [CompleteAtomicBooleanAlgebra β] : CompleteAtomicBooleanAlgebra (α × β) where
  __ := instBooleanAlgebra
  __ := instCompletelyDistribLattice

instance Pi.instCompleteAtomicBooleanAlgebra {ι : Type*} {π : ι → Type*}
    [∀ i, CompleteAtomicBooleanAlgebra (π i)] : CompleteAtomicBooleanAlgebra (∀ i, π i) where
  __ := Pi.instCompleteBooleanAlgebra
  iInf_iSup_eq f := by ext; rw [iInf_iSup_eq]

instance OrderDual.instCompleteAtomicBooleanAlgebra [CompleteAtomicBooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra αᵒᵈ where
  __ := instCompleteBooleanAlgebra
  __ := instCompletelyDistribLattice

instance Prop.instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.instBooleanAlgebra
  iInf_iSup_eq f := by simp [Classical.skolem]

instance Prop.instCompleteBooleanAlgebra : CompleteBooleanAlgebra Prop := inferInstance

section lift

protected abbrev Function.Injective.frameMinimalAxioms [Max α] [Min α] [SupSet α] [InfSet α] [Top α]
    [Bot α] (minAx : Frame.MinimalAxioms β) (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : Frame.MinimalAxioms α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  inf_sSup_le_iSup_inf a s := by
    change f (a ⊓ sSup s) ≤ f _
    rw [← sSup_image, map_inf, map_sSup s, minAx.inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge

protected abbrev Function.Injective.coframeMinimalAxioms [Max α] [Min α] [SupSet α] [InfSet α]
    [Top α] [Bot α] (minAx : Coframe.MinimalAxioms β) (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : Coframe.MinimalAxioms α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  iInf_sup_le_sup_sInf a s := by
    change f _ ≤ f (a ⊔ sInf s)
    rw [← sInf_image, map_sup, map_sInf s, minAx.sup_iInf₂_eq]
    simp_rw [← map_sup]
    exact ((map_sInf _).trans iInf_image).le

protected abbrev Function.Injective.frame [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [HasCompl α] [HImp α] [Frame β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f aᶜ = (f a)ᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : Frame α where
  __ := hf.frameMinimalAxioms .of f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.heytingAlgebra f map_sup map_inf map_top map_bot map_compl map_himp

protected abbrev Function.Injective.coframe [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α]
    [HNot α] [SDiff α] [Coframe β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : Coframe α where
  __ := hf.coframeMinimalAxioms .of f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coheytingAlgebra f map_sup map_inf map_top map_bot map_hnot map_sdiff

protected abbrev Function.Injective.completeDistribLatticeMinimalAxioms [Max α] [Min α] [SupSet α]
    [InfSet α] [Top α] [Bot α] (minAx : CompleteDistribLattice.MinimalAxioms β) (f : α → β)
    (hf : Injective f) (map_sup : let _ := minAx.toCompleteLattice
      ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : let _ := minAx.toCompleteLattice
      ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : let _ := minAx.toCompleteLattice
      ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : let _ := minAx.toCompleteLattice
      ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : let _ := minAx.toCompleteLattice
      f ⊤ = ⊤) (map_bot : let _ := minAx.toCompleteLattice
      f ⊥ = ⊥) :
    CompleteDistribLattice.MinimalAxioms α where
  __ := hf.frameMinimalAxioms minAx.toFrame f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.coframeMinimalAxioms minAx.toCoframe f map_sup map_inf map_sSup map_sInf map_top map_bot

protected abbrev Function.Injective.completeDistribLattice [Max α] [Min α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [HImp α] [HNot α] [SDiff α] [CompleteDistribLattice β] (f : α → β)
    (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteDistribLattice α where
  __ := hf.frame f map_sup map_inf map_sSup map_sInf map_top map_bot map_compl map_himp
  __ := hf.coframe f map_sup map_inf map_sSup map_sInf map_top map_bot map_hnot map_sdiff

protected abbrev Function.Injective.completelyDistribLatticeMinimalAxioms [Max α] [Min α] [SupSet α]
    [InfSet α] [Top α] [Bot α] (minAx : CompletelyDistribLattice.MinimalAxioms β) (f : α → β)
    (hf : Injective f) (map_sup : let _ := minAx.toCompleteLattice
      ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : let _ := minAx.toCompleteLattice
      ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : let _ := minAx.toCompleteLattice
      ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : let _ := minAx.toCompleteLattice
      ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : let _ := minAx.toCompleteLattice
      f ⊤ = ⊤) (map_bot : let _ := minAx.toCompleteLattice
      f ⊥ = ⊥) :
    CompletelyDistribLattice.MinimalAxioms α where
  __ := hf.completeDistribLatticeMinimalAxioms minAx.toCompleteDistribLattice f map_sup map_inf
    map_sSup map_sInf map_top map_bot
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      minAx.iInf_iSup_eq']

protected abbrev Function.Injective.completelyDistribLattice [Max α] [Min α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [HImp α] [HNot α] [SDiff α] [CompletelyDistribLattice β]
    (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompletelyDistribLattice α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.biheytingAlgebra f map_sup map_inf map_top map_bot map_compl map_hnot map_himp map_sdiff
  iInf_iSup_eq g := hf <| by
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      iInf_iSup_eq]

protected abbrev Function.Injective.completeBooleanAlgebra [Max α] [Min α] [SupSet α] [InfSet α]
    [Top α] [Bot α] [HasCompl α] [HImp α] [SDiff α] [CompleteBooleanAlgebra β] (f : α → β)
    (hf : Injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
    (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteBooleanAlgebra α where
  __ := hf.completeLattice f map_sup map_inf map_sSup map_sInf map_top map_bot
  __ := hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff map_himp
  inf_sSup_le_iSup_inf a s := by
    change f (a ⊓ sSup s) ≤ f _
    rw [← sSup_image, map_inf, map_sSup s, inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge
  iInf_sup_le_sup_sInf a s := by
    change f _ ≤ f (a ⊔ sInf s)
    rw [← sInf_image, map_sup, map_sInf s, sup_iInf₂_eq]
    simp_rw [← map_sup]
    exact ((map_sInf _).trans iInf_image).le

protected abbrev Function.Injective.completeAtomicBooleanAlgebra [Max α] [Min α] [SupSet α]
    [InfSet α] [Top α] [Bot α] [HasCompl α] [HImp α] [HNot α] [SDiff α]
    [CompleteAtomicBooleanAlgebra β] (f : α → β) (hf : Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥)
    (map_compl : ∀ a, f aᶜ = (f a)ᶜ) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    CompleteAtomicBooleanAlgebra α where
  __ := hf.completelyDistribLattice f map_sup map_inf map_sSup map_sInf map_top map_bot map_compl
    map_himp map_hnot map_sdiff
  __ := hf.booleanAlgebra f map_sup map_inf map_top map_bot map_compl map_sdiff map_himp

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1})

instance instCompleteAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra PUnit where
  __ := PUnit.instBooleanAlgebra
  sSup _ := unit
  sInf _ := unit
  le_sSup _ _ _ := trivial
  sSup_le _ _ _ := trivial
  sInf_le _ _ _ := trivial
  le_sInf _ _ _ := trivial
  iInf_iSup_eq _ := rfl

instance instCompleteBooleanAlgebra : CompleteBooleanAlgebra PUnit := inferInstance

end PUnit
