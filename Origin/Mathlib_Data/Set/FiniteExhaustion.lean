/-
Extracted from Data/Set/FiniteExhaustion.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Finite Exhaustions

This file defines a structure called `FiniteExhaustion` which represents an exhaustion of a
countable set by an increasing sequence of finite sets. Given a countable set `s`,
`FiniteExhaustion.choice s` is a choice of a finite exhaustion.
-/

open Set

structure Set.FiniteExhaustion {α : Type*} (s : Set α) where
  /-- The underlying sequence of a `FiniteExhaustion`. -/
  toFun : ℕ → Set α
  /-- Every set in a `FiniteExhaustion` is finite. -/
  finite' : ∀ n, Finite (toFun n)
  /-- The sequence of sets in a `FiniteExhaustion` are monotonically increasing. -/
  subset_succ' : ∀ n, toFun n ⊆ toFun (n + 1)
  /-- The union of all sets in a `FiniteExhaustion` equals `s` -/
  iUnion_eq' : ⋃ n, toFun n = s

namespace Set.FiniteExhaustion

-- INSTANCE (free from Core): {α

-- INSTANCE (free from Core): {α

-- INSTANCE (free from Core): {α

variable {α : Type*} {s : Set α} (K : FiniteExhaustion s)
