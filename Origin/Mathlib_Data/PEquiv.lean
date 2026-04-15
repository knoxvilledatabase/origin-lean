/-
Extracted from Data/PEquiv.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Partial Equivalences

In this file, we define partial equivalences `PEquiv`, which are a bijection between a subset of `α`
and a subset of `β`. Notationally, a `PEquiv` is denoted by "`≃.`" (note that the full stop is part
of the notation). The way we store these internally is with two functions `f : α → Option β` and
the reverse function `g : β → Option α`, with the condition that if `f a` is `some b`,
then `g b` is `some a`.

## Main results

- `PEquiv.ofSet`: creates a `PEquiv` from a set `s`,
  which sends an element to itself if it is in `s`.
- `PEquiv.single`: given two elements `a : α` and `b : β`, create a `PEquiv` that sends them to
  each other, and ignores all other elements.
- `PEquiv.injective_of_forall_ne_isSome`/`injective_of_forall_isSome`: If the domain of a `PEquiv`
  is all of `α` (except possibly one point), its `toFun` is injective.

## Canonical order

`PEquiv` is canonically ordered by inclusion; that is, if a function `f` defined on a subset `s`
is equal to `g` on that subset, but `g` is also defined on a larger set, then `f ≤ g`. We also have
a definition of `⊥`, which is the empty `PEquiv` (sends all to `none`), which in the end gives us a
`SemilatticeInf` with an `OrderBot` instance.

## Tags

pequiv, partial equivalence

-/

assert_not_exists RelIso

universe u v w x

structure PEquiv (α : Type u) (β : Type v) where
  /-- The underlying partial function of a `PEquiv` -/
  toFun : α → Option β
  /-- The partial inverse of `toFun` -/
  invFun : β → Option α
  /-- `invFun` is the partial inverse of `toFun` -/
  inv : ∀ (a : α) (b : β), invFun b = some a ↔ toFun a = some b

infixr:25 " ≃. " => PEquiv

namespace PEquiv

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Function Option

-- INSTANCE (free from Core): :
