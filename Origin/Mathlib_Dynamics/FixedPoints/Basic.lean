/-
Extracted from Dynamics/FixedPoints/Basic.lean
Genuine: 10 of 15 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Iterate
import Mathlib.GroupTheory.Perm.Basic

/-!
# Fixed points of a self-map

In this file we define

* the predicate `IsFixedPt f x := f x = x`;
* the set `fixedPoints f` of fixed points of a self-map `f`.

We also prove some simple lemmas about `IsFixedPt` and `∘`, `iterate`, and `Semiconj`.

## Tags

fixed point
-/

open Equiv

universe u v

variable {α : Type u} {β : Type v} {f fa g : α → α} {x : α} {fb : β → β} {e : Perm α}

namespace Function

open Function (Commute)

theorem isFixedPt_id (x : α) : IsFixedPt id x :=
  (rfl : _)

namespace IsFixedPt

-- INSTANCE (free from Core): decidable

protected theorem eq (hf : IsFixedPt f x) : f x = x :=
  hf

protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
  calc
    f (g x) = f x := congr_arg f hg
    _ = x := hf

protected theorem iterate (hf : IsFixedPt f x) (n : ℕ) : IsFixedPt f^[n] x :=
  iterate_fixed hf n

theorem left_of_comp (hfg : IsFixedPt (f ∘ g) x) (hg : IsFixedPt g x) : IsFixedPt f x :=
  calc
    f x = f (g x) := congr_arg f hg.symm
    _ = x := hfg

protected theorem map {x : α} (hx : IsFixedPt fa x) {g : α → β} (h : Semiconj g fa fb) :
    IsFixedPt fb (g x) :=
  calc
    fb (g x) = g (fa x) := (h.eq x).symm
    _ = g x := congr_arg g hx

protected theorem apply {x : α} (hx : IsFixedPt f x) : IsFixedPt f (f x) := by convert hx

theorem preimage_iterate {s : Set α} (h : IsFixedPt (Set.preimage f) s) (n : ℕ) :
    IsFixedPt (Set.preimage f^[n]) s := by
  rw [Set.preimage_iterate_eq]
  exact h.iterate n

lemma image_iterate {s : Set α} (h : IsFixedPt (Set.image f) s) (n : ℕ) :
    IsFixedPt (Set.image f^[n]) s :=
  Set.image_iterate_eq ▸ h.iterate n

protected theorem perm_zpow (h : IsFixedPt e x) : ∀ n : ℤ, IsFixedPt (⇑(e ^ n)) x
  | Int.ofNat _ => h.perm_pow _
  | Int.negSucc n => (h.perm_pow <| n + 1).perm_inv

end IsFixedPt
