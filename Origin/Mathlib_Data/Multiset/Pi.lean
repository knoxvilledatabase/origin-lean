/-
Extracted from Data/Multiset/Pi.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Cartesian product of multisets

## Main definitions

* `Multiset.pi`: Cartesian product of multisets indexed by a multiset.
-/

namespace Multiset

section Pi

open Function

namespace Pi

variable {α : Type*} [DecidableEq α] {δ : α → Sort*}

def empty (δ : α → Sort*) : ∀ a ∈ (0 : Multiset α), δ a :=
  nofun

variable (m : Multiset α) (a : α)

def cons (b : δ a) (f : ∀ a ∈ m, δ a) : ∀ a' ∈ a ::ₘ m, δ a' :=
  fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' <| (mem_cons.1 ha').resolve_left h

variable {m a}

theorem cons_same {b : δ a} {f : ∀ a ∈ m, δ a} (h : a ∈ a ::ₘ m) :
    cons m a b f a h = b :=
  dif_pos rfl

theorem cons_ne {a a' : α} {b : δ a} {f : ∀ a ∈ m, δ a} (h' : a' ∈ a ::ₘ m)
    (h : a' ≠ a) : Pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
  dif_neg h

theorem cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : ∀ a ∈ m, δ a}
    (h : a ≠ a') : Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f) ≍
      Pi.cons (a ::ₘ m) a' b' (Pi.cons m a b f) := by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro a'' _ rfl
  refine hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ => ?_
  rcases Decidable.ne_or_eq a'' a with (h₁ | rfl)
  on_goal 1 => rcases Decidable.eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]
