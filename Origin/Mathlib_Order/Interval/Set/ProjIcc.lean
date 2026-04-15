/-
Extracted from Order/Interval/Set/ProjIcc.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `Set.projIci (a : α)` to be the map `α → [a, ∞)` sending `(-∞, a]` to `a`, and each point
  `x ∈ [a, ∞)` to itself;
* `Set.projIic (b : α)` to be the map `α → (-∞, b[` sending `[b, ∞)` to `b`, and each point
  `x ∈ (-∞, b]` to itself;
* `Set.projIcc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `Set.IccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIcc a b h`.
* `Set.IciExtend {a : α} (f : Ici a → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIci a`.
* `Set.IicExtend {b : α} (f : Iic b → β)` to be the extension of `f` to `α` defined
  as `f ∘ projIic b`.

We also prove some trivial properties of these maps.
-/

variable {α β : Type*} [LinearOrder α]

open Function

namespace Set

def projIci (a x : α) : Ici a := ⟨max a x, le_max_left _ _⟩

def projIic (b x : α) : Iic b := ⟨min b x, min_le_left _ _⟩

def projIcc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_left _ _, max_le h (min_le_left _ _)⟩

variable {a b : α} (h : a ≤ b) {x : α}
