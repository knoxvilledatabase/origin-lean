/-
Extracted from Computability/StateTransition.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# State Transition Systems

This file contains simple definitions and lemmas for reasoning about state transition systems
defined by a function `σ → Option σ`, where `σ` is the type of states.
-/

assert_not_exists MonoidWithZero

open Relation

namespace StateTransition

def eval {σ} (f : σ → Option σ) : σ → Part σ :=
  PFun.fix fun s ↦ Part.some <| (f s).elim (Sum.inl s) Sum.inr

def Reaches {σ} (f : σ → Option σ) : σ → σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ f a

def Reaches₁ {σ} (f : σ → Option σ) : σ → σ → Prop :=
  TransGen fun a b ↦ b ∈ f a

theorem reaches₁_eq {σ} {f : σ → Option σ} {a b c} (h : f a = f b) :
    Reaches₁ f a c ↔ Reaches₁ f b c :=
  TransGen.head'_iff.trans (TransGen.head'_iff.trans <| by rw [h]).symm

theorem reaches_total {σ} {f : σ → Option σ} {a b c} (hab : Reaches f a b) (hac : Reaches f a c) :
    Reaches f b c ∨ Reaches f c b :=
  ReflTransGen.total_of_right_unique (fun _ _ _ ↦ Option.mem_unique) hab hac

theorem reaches₁_fwd {σ} {f : σ → Option σ} {a b c} (h₁ : Reaches₁ f a c) (h₂ : b ∈ f a) :
    Reaches f b c := by
  rcases TransGen.head'_iff.1 h₁ with ⟨b', hab, hbc⟩
  cases Option.mem_unique hab h₂; exact hbc

def Reaches₀ {σ} (f : σ → Option σ) (a b : σ) : Prop :=
  ∀ c, Reaches₁ f b c → Reaches₁ f a c

theorem Reaches₀.trans {σ} {f : σ → Option σ} {a b c : σ} (h₁ : Reaches₀ f a b)
    (h₂ : Reaches₀ f b c) : Reaches₀ f a c
  | _, h₃ => h₁ _ (h₂ _ h₃)
