/-
Extracted from Order/CompleteLattice/MulticoequalizerDiagram.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multicoequalizer diagrams in complete lattices

We introduce the notion of bi-Cartesian square (`Lattice.BicartSq`) in a lattice `T`.
This consists of elements `x₁`, `x₂`, `x₃` and `x₄` such that `x₂ ⊔ x₃ = x₄` and
`x₂ ⊓ x₃ = x₁`.

It shall be shown (TODO) that if `T := Set X`, then the image of the
associated commutative square in the category `Type _` is a bi-Cartesian square
in a categorical sense (both pushout and pullback).

More generally, if `T` is a complete lattice, `x : T`, `u : ι → T`, `v : ι → ι → T`,
we introduce a property `MulticoequalizerDiagram x u v` which says that `x` is
the supremum of `u`, and that for all `i` and `j`, `v i j` is the minimum of `u i` and `u j`.
Again, when `T := Set X`, we shall show (TODO) that we obtain a multicoequalizer diagram
in the category of types.

-/

universe u

open CategoryTheory Limits

local grind_pattern inf_le_left => a ⊓ b

local grind_pattern inf_le_right => a ⊓ b

local grind_pattern le_sup_left => a ⊔ b

local grind_pattern le_sup_right => a ⊔ b

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

structure BicartSq : Prop where
  sup_eq : x₂ ⊔ x₃ = x₄
  inf_eq : x₂ ⊓ x₃ = x₁

attribute [grind cases] BicartSq

namespace BicartSq
