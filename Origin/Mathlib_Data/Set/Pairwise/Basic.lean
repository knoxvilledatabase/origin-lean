/-
Extracted from Data/Set/Pairwise/Basic.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relations holding pairwise

This file develops pairwise relations and defines pairwise disjoint indexed sets.

We also prove many basic facts about `Pairwise`. It is possible that an intermediate file,
with more imports than `Logic.Pairwise` but not importing `Data.Set.Function` would be appropriate
to hold many of these basic facts.

## Main declarations

* `Set.PairwiseDisjoint`: `s.PairwiseDisjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `Disjoint`.

## Notes

The spelling `s.PairwiseDisjoint id` is preferred over `s.Pairwise Disjoint` to permit dot notation
on `Set.PairwiseDisjoint`, even though the latter unfolds to something nicer.
-/

open Function Order Set

variable {α β γ ι ι' : Type*} {r p : α → α → Prop}

section Pairwise

variable {f g : ι → α} {s t : Set α} {a b : α}

theorem pairwise_on_bool (hr : Symmetric r) {a b : α} :
    Pairwise (r on fun c => cond c a b) ↔ r a b := by simpa [Pairwise, Function.onFun] using @hr a b

theorem pairwise_disjoint_on_bool [PartialOrder α] [OrderBot α] {a b : α} :
    Pairwise (Disjoint on fun c => cond c a b) ↔ Disjoint a b :=
  pairwise_on_bool Disjoint.symm

theorem Symmetric.pairwise_on [LinearOrder ι] (hr : Symmetric r) (f : ι → α) :
    Pairwise (r on f) ↔ ∀ ⦃m n⦄, m < n → r (f m) (f n) :=
  ⟨fun h _m _n hmn => h hmn.ne, fun h _m _n hmn => hmn.lt_or_gt.elim (@h _ _) fun h' => hr (h h')⟩

theorem pairwise_disjoint_on [PartialOrder α] [OrderBot α] [LinearOrder ι] (f : ι → α) :
    Pairwise (Disjoint on f) ↔ ∀ ⦃m n⦄, m < n → Disjoint (f m) (f n) :=
  Symmetric.pairwise_on Disjoint.symm f

theorem pairwise_disjoint_mono [PartialOrder α] [OrderBot α] (hs : Pairwise (Disjoint on f))
    (h : g ≤ f) : Pairwise (Disjoint on g) :=
  hs.mono fun i j hij => Disjoint.mono (h i) (h j) hij

theorem Pairwise.disjoint_extend_bot [PartialOrder γ] [OrderBot γ]
    {e : α → β} {f : α → γ} (hf : Pairwise (Disjoint on f)) (he : FactorsThrough f e) :
    Pairwise (Disjoint on extend e f ⊥) := by
  intro b₁ b₂ hne
  rcases em (∃ a₁, e a₁ = b₁) with ⟨a₁, rfl⟩ | hb₁
  · rcases em (∃ a₂, e a₂ = b₂) with ⟨a₂, rfl⟩ | hb₂
    · simpa only [onFun, he.extend_apply] using hf (ne_of_apply_ne e hne)
    · simpa only [onFun, extend_apply' _ _ _ hb₂] using disjoint_bot_right
  · simpa only [onFun, extend_apply' _ _ _ hb₁] using disjoint_bot_left

namespace Set

theorem Pairwise.mono (h : t ⊆ s) (hs : s.Pairwise r) : t.Pairwise r :=
  fun _x xt _y yt => hs (h xt) (h yt)

theorem Pairwise.mono' (H : r ≤ p) (hr : s.Pairwise r) : s.Pairwise p :=
  hr.imp H

theorem pairwise_top (s : Set α) : s.Pairwise ⊤ :=
  pairwise_of_forall s _ fun _ _ => trivial

protected theorem Subsingleton.pairwise (h : s.Subsingleton) (r : α → α → Prop) : s.Pairwise r :=
  fun _x hx _y hy hne => (hne (h hx hy)).elim
