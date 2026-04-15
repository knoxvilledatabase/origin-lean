/-
Extracted from Combinatorics/Quiver/Path.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Paths in quivers

Given a quiver `V`, we define the type of paths from `a : V` to `b : V` as an inductive
family. We define composition of paths and the action of prefunctors on paths.
-/

open Function

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace Quiver

inductive Path {V : Type u} [Quiver.{v} V] (a : V) : V → Type max u v
  | nil : Path a a
  | cons : ∀ {b c : V}, Path a b → (b ⟶ c) → Path a c

compile_inductive% Path

def Hom.toPath {V} [Quiver V] {a b : V} (e : a ⟶ b) : Path a b :=
  Path.nil.cons e

namespace Path

variable {V : Type u} [Quiver V] {a b c d : V}

lemma nil_ne_cons (p : Path a b) (e : b ⟶ a) : Path.nil ≠ p.cons e :=
  fun h => by injection h

lemma cons_ne_nil (p : Path a b) (e : b ⟶ a) : p.cons e ≠ Path.nil :=
  fun h => by injection h

lemma obj_eq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : b = c := by injection h

lemma heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : p ≍ p' := by injection h

lemma hom_heq_of_cons_eq_cons {p : Path a b} {p' : Path a c}
    {e : b ⟶ d} {e' : c ⟶ d} (h : p.cons e = p'.cons e') : e ≍ e' := by injection h

def length {a : V} : ∀ {b : V}, Path a b → ℕ
  | _, nil => 0
  | _, cons p _ => p.length + 1

-- INSTANCE (free from Core): {a
