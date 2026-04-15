/-
Extracted from Logic/Function/Conjugate.lean
Genuine: 11 of 14 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Semiconjugate and commuting maps

We define the following predicates:

* `Function.Semiconj`: `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`;
* `Function.Semiconj₂`: `f : α → β` semiconjugates a binary operation `ga : α → α → α`
  to `gb : β → β → β` if `f (ga x y) = gb (f x) (f y)`;
* `Function.Commute`: `f : α → α` commutes with `g : α → α` if `f ∘ g = g ∘ f`,
  or equivalently `Semiconj f g g`.
-/

namespace Function

variable {α : Type*} {β : Type*} {γ : Type*}

def Semiconj (f : α → β) (ga : α → α) (gb : β → β) : Prop :=
  ∀ x, f (ga x) = gb (f x)

namespace Semiconj

variable {f fab : α → β} {fbc : β → γ} {ga ga' : α → α} {gb gb' : β → β} {gc : γ → γ}

lemma _root_.Function.semiconj_iff_comp_eq : Semiconj f ga gb ↔ f ∘ ga = gb ∘ f := funext_iff.symm

protected alias ⟨comp_eq, _⟩ := semiconj_iff_comp_eq

theorem comp_right (h : Semiconj f ga gb) (h' : Semiconj f ga' gb') :
    Semiconj f (ga ∘ ga') (gb ∘ gb') := fun x ↦ by
  simp only [comp_apply, h.eq, h'.eq]

protected theorem trans (hab : Semiconj fab ga gb) (hbc : Semiconj fbc gb gc) :
    Semiconj (fbc ∘ fab) ga gc := fun x ↦ by
  simp only [comp_apply, hab.eq, hbc.eq]

theorem comp_left (hbc : Semiconj fbc gb gc) (hab : Semiconj fab ga gb) :
    Semiconj (fbc ∘ fab) ga gc :=
  hab.trans hbc

theorem id_right : Semiconj f id id := fun _ ↦ rfl

theorem id_left : Semiconj id ga ga := fun _ ↦ rfl

theorem inverses_right (h : Semiconj f ga gb) (ha : RightInverse ga' ga) (hb : LeftInverse gb' gb) :
    Semiconj f ga' gb' := fun x ↦ by
  rw [← hb (f (ga' x)), ← h.eq, ha x]

lemma inverse_left {f' : β → α} (h : Semiconj f ga gb)
    (hf₁ : LeftInverse f' f) (hf₂ : RightInverse f' f) : Semiconj f' gb ga := fun x ↦ by
  rw [← hf₁.injective.eq_iff, h, hf₂, hf₂]

theorem option_map {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) :
    Semiconj (Option.map f) (Option.map ga) (Option.map gb)
  | none => rfl
  | some _ => congr_arg some <| h _

end Semiconj

protected def Commute (f g : α → α) : Prop :=
  Semiconj f g g

open Function (Commute)

namespace Commute

variable {f f' g g' : α → α}
