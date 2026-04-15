/-
Extracted from Order/Bounds/Defs.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Set.Defs
import Mathlib.Tactic.TypeStar

/-!
# Definitions about upper/lower bounds

In this file we define:
* `upperBounds`, `lowerBounds` : the set of upper bounds (resp., lower bounds) of a set;
* `BddAbove s`, `BddBelow s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `IsLeast s a`, `IsGreatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `IsLUB s a`, `IsGLB s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.
* `IsCofinal s`: for every `a`, there exists a member of `s` greater or equal to it.
-/

variable {α : Type*} [LE α]

def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

def lowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }

def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

def BddBelow (s : Set α) :=
  (lowerBounds s).Nonempty

def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s

def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)

def IsGLB (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)

def IsCofinal (s : Set α) : Prop :=
  ∀ x, ∃ y ∈ s, x ≤ y
