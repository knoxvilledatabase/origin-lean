/-
Extracted from Order/Monotone/Monovary.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monovariance of functions

Two functions *vary together* if a strict change in the first implies a change in the second.

This is in some sense a way to say that two functions `f : ι → α`, `g : ι → β` are "monotone
together", without actually having an order on `ι`.

This condition comes up in the rearrangement inequality. See `Algebra.Order.Rearrangement`.

## Main declarations

* `Monovary f g`: `f` monovaries with `g`. If `g i < g j`, then `f i ≤ f j`.
* `Antivary f g`: `f` antivaries with `g`. If `g i < g j`, then `f j ≤ f i`.
* `MonovaryOn f g s`: `f` monovaries with `g` on `s`.
* `AntivaryOn f g s`: `f` antivaries with `g` on `s`.
-/

open Function Set

variable {ι ι' α β γ : Type*}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β}
  {s t : Set ι}

def Monovary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f i ≤ f j

def Antivary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f j ≤ f i

def MonovaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f i ≤ f j

def AntivaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f j ≤ f i

protected theorem Monovary.monovaryOn (h : Monovary f g) (s : Set ι) : MonovaryOn f g s :=
  fun _ _ _ _ hij => h hij

protected theorem Antivary.antivaryOn (h : Antivary f g) (s : Set ι) : AntivaryOn f g s :=
  fun _ _ _ _ hij => h hij
