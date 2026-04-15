/-
Extracted from Data/Seq/Computation.lean
Genuine: 12 of 14 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Coinductive formalization of unbounded computations.

This file provides a `Computation` type where `Computation α` is the type of
unbounded computations returning `α`.
-/

open Function

universe u v w

def Computation (α : Type u) : Type u :=
  { f : Stream' (Option α) // ∀ ⦃n a⦄, f n = some a → f (n + 1) = some a }

namespace Computation

variable {α : Type u} {β : Type v} {γ : Type w}

def pure (a : α) : Computation α :=
  ⟨Stream'.const (some a), fun _ _ => id⟩

-- INSTANCE (free from Core): :

def think (c : Computation α) : Computation α :=
  ⟨Stream'.cons none c.1, fun n a h => by
    rcases n with - | n
    · contradiction
    · exact c.2 h⟩

def thinkN (c : Computation α) : ℕ → Computation α
  | 0 => c
  | n + 1 => think (thinkN c n)

def head (c : Computation α) : Option α :=
  c.1.head

def tail (c : Computation α) : Computation α :=
  ⟨c.1.tail, fun _ _ h => c.2 h⟩

def empty (α) : Computation α :=
  ⟨Stream'.const none, fun _ _ => id⟩

-- INSTANCE (free from Core): :

def runFor : Computation α → ℕ → Option α :=
  Subtype.val

def destruct (c : Computation α) : α ⊕ (Computation α) :=
  match c.1 0 with
  | none => Sum.inr (tail c)
  | some a => Sum.inl a

unsafe def run : Computation α → α
  | c =>
    match destruct c with
    | Sum.inl a => a
    | Sum.inr ca => run ca

theorem destruct_eq_pure {s : Computation α} {a : α} : destruct s = Sum.inl a → s = pure a := by
  dsimp [destruct]
  cases f0 : s.1 0 <;> intro h
  · contradiction
  · apply Subtype.ext
    funext n
    induction n with
    | zero => injection h with h'; rwa [h'] at f0
    | succ n IH => exact s.2 IH

theorem destruct_eq_think {s : Computation α} {s'} : destruct s = Sum.inr s' → s = think s' := by
  dsimp [destruct]
  rcases f0 : s.1 0 with - | a' <;> intro h
  · injection h with h'
    rw [← h']
    obtain ⟨f, al⟩ := s
    apply Subtype.ext
    dsimp [think, tail]
    rw [← f0]
    exact (Stream'.eta f).symm
  · contradiction
