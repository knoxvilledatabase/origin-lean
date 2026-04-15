/-
Extracted from Data/List/Forall2.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Double universal quantification on a list

This file provides an API for `List.Forall₂` (definition in `Data.List.Defs`).
`Forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length, and whenever `a` is the nth element
of `l₁`, and `b` is the nth element of `l₂`, then `R a b` is satisfied.
-/

open Nat Function

namespace List

variable {α β γ δ : Type*} {R S : α → β → Prop} {P : γ → δ → Prop} {Rₐ : α → α → Prop}

open Relator

mk_iff_of_inductive_prop List.Forall₂ List.forall₂_iff

theorem Forall₂.imp (H : ∀ a b, R a b → S a b) {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> solve_by_elim

theorem Forall₂.mp {Q : α → β → Prop} (h : ∀ a b, Q a b → R a b → S a b) :
    ∀ {l₁ l₂}, Forall₂ Q l₁ l₂ → Forall₂ R l₁ l₂ → Forall₂ S l₁ l₂
  | [], [], Forall₂.nil, Forall₂.nil => Forall₂.nil
  | a :: _, b :: _, Forall₂.cons hr hrs, Forall₂.cons hq hqs =>
    Forall₂.cons (h a b hr hq) (Forall₂.mp h hrs hqs)

theorem Forall₂.flip : ∀ {a b}, Forall₂ (flip R) b a → Forall₂ R a b
  | _, _, Forall₂.nil => Forall₂.nil
  | _ :: _, _ :: _, Forall₂.cons h₁ h₂ => Forall₂.cons h₁ h₂.flip
