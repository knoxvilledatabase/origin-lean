/-
Extracted from Logic/Relator.lean
Genuine: 29 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Logic.Function.Defs

/-!
# Relator for functions, pairs, sums, and lists.
-/

namespace Relator

universe u₁ u₂ v₁ v₂

section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}

variable (R : α → β → Prop) (S : γ → δ → Prop)

def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀⦃a b⦄, R a b → S (f a) (g b)

infixr:40 " ⇒ " => LiftFun

end

section

variable {α : Type u₁} {β : Type u₂} (R : α → β → Prop)

def RightTotal : Prop := ∀ b, ∃ a, R a b

def LeftTotal : Prop := ∀ a, ∃ b, R a b

def BiTotal : Prop := LeftTotal R ∧ RightTotal R

def LeftUnique : Prop := ∀ ⦃a b c⦄, R a c → R b c → a = b

def RightUnique : Prop := ∀ ⦃a b c⦄, R a b → R a c → b = c

def BiUnique : Prop := LeftUnique R ∧ RightUnique R

variable {R}

lemma RightTotal.rel_forall (h : RightTotal R) :
    ((R ⇒ (· → ·)) ⇒ (· → ·)) (fun p => ∀i, p i) (fun q => ∀i, q i) :=
  fun _ _ Hrel H b => Exists.elim (h b) (fun _ Rab => Hrel Rab (H _))

lemma LeftTotal.rel_exists (h : LeftTotal R) :
    ((R ⇒ (· → ·)) ⇒ (· → ·)) (fun p => ∃i, p i) (fun q => ∃i, q i) :=
  fun _ _ Hrel ⟨a, pa⟩ => (h a).imp fun _ Rab => Hrel Rab pa

lemma BiTotal.rel_forall (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∀i, p i) (fun q => ∀i, q i) :=
  fun _ _ Hrel =>
    ⟨fun H b => Exists.elim (h.right b) (fun _ Rab => (Hrel Rab).mp (H _)),
      fun H a => Exists.elim (h.left a) (fun _ Rab => (Hrel Rab).mpr (H _))⟩

lemma BiTotal.rel_exists (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∃i, p i) (fun q => ∃i, q i) :=
  fun _ _ Hrel =>
    ⟨fun ⟨a, pa⟩ => (h.left a).imp fun _ Rab => (Hrel Rab).1 pa,
      fun ⟨b, qb⟩ => (h.right b).imp fun _ Rab => (Hrel Rab).2 qb⟩

lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ Iff)) Eq eq') : LeftUnique R :=
  fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)

end

lemma rel_imp : (Iff ⇒ (Iff ⇒ Iff)) (· → ·) (· → ·) :=
  fun _ _ h _ _ l => imp_congr h l

lemma rel_not : (Iff ⇒ Iff) Not Not :=
  fun _ _ h => not_congr h

lemma bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }

variable {α : Type*} {β : Type*} {γ : Type*}

variable {r : α → β → Prop}

lemma LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) :=
  fun _ _ _ h₁ h₂ => h h₁ h₂

lemma rel_and : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·∧·) (·∧·) :=
  fun _ _ h₁ _ _ h₂ => and_congr h₁ h₂

lemma rel_or : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·∨·) (·∨·) :=
  fun _ _ h₁ _ _ h₂ => or_congr h₁ h₂

lemma rel_iff : ((·↔·) ⇒ (·↔·) ⇒ (·↔·)) (·↔·) (·↔·) :=
  fun _ _ h₁ _ _ h₂ => iff_congr h₁ h₂

lemma rel_eq {r : α → β → Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (·↔·)) (·=·) (·=·) :=
  fun _ _ h₁ _ _ h₂ => ⟨fun h => hr.right h₁ <| h.symm ▸ h₂, fun h => hr.left h₁ <| h.symm ▸ h₂⟩

open Function

variable {r₁₁ : α → α → Prop} {r₁₂ : α → β → Prop} {r₂₁ : β → α → Prop}
  {r₂₃ : β → γ → Prop} {r₁₃ : α → γ → Prop}

namespace LeftTotal

protected lemma refl (hr : ∀ a : α, r₁₁ a a) :
    LeftTotal r₁₁ :=
  fun a ↦ ⟨a, hr _⟩

protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    LeftTotal r₁₂ → RightTotal r₂₁ :=
  fun h a ↦ (h a).imp (fun _ ↦ hr _ _)

protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    LeftTotal r₁₂ → LeftTotal r₂₃ → LeftTotal r₁₃ :=
  fun h₁ h₂ a ↦ let ⟨b, hab⟩ := h₁ a; let ⟨c, hbc⟩ := h₂ b; ⟨c, hr _ _ _ hab hbc⟩

end LeftTotal

namespace RightTotal

protected lemma refl (hr : ∀ a : α, r₁₁ a a) : RightTotal r₁₁ :=
  LeftTotal.refl hr

protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    RightTotal r₁₂ → LeftTotal r₂₁ :=
  LeftTotal.symm (fun _ _ ↦ hr _ _)

protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    RightTotal r₁₂ → RightTotal r₂₃ → RightTotal r₁₃ :=
  swap <| LeftTotal.trans (fun _ _ _ ↦ swap <| hr _ _ _)

end RightTotal

namespace BiTotal

protected lemma refl (hr : ∀ a : α, r₁₁ a a) :
    BiTotal r₁₁ :=
  ⟨LeftTotal.refl hr, RightTotal.refl hr⟩

protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    BiTotal r₁₂ → BiTotal r₂₁ :=
  fun h ↦ ⟨h.2.symm hr, h.1.symm hr⟩

protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    BiTotal r₁₂ → BiTotal r₂₃ → BiTotal r₁₃ :=
  fun h₁ h₂ ↦ ⟨h₁.1.trans hr h₂.1, h₁.2.trans hr h₂.2⟩

end BiTotal

end Relator
