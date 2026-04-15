/-
Extracted from AlgebraicTopology/SimplexCategory/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Basic properties of the simplex category

In `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean`, we define the simplex
category with objects `ℕ` and morphisms `n ⟶ m` the monotone maps from
`Fin (n + 1)` to `Fin (m + 1)`.

In this file, we define the generating maps for the simplex category, show that
this category is equivalent to `NonemptyFinLinOrd`, and establish basic
properties of its epimorphisms and monomorphisms.
-/

universe v

open Simplicial CategoryTheory Limits

namespace SimplexCategory

-- INSTANCE (free from Core): {a

-- INSTANCE (free from Core): {n

section Init

lemma congr_toOrderHom_apply {a b : SimplexCategory} {f g : a ⟶ b} (h : f = g)
    (x : Fin (a.len + 1)) : f.toOrderHom x = g.toOrderHom x := by rw [h]

def const (x y : SimplexCategory) (i : Fin (y.len + 1)) : x ⟶ y :=
  Hom.mk <| ⟨fun _ => i, by tauto⟩
