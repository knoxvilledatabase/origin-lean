/-
Extracted from Data/List/Zip.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# zip & unzip

This file provides results about `List.zipWith`, `List.zip` and `List.unzip` (definitions are in
core Lean).
`zipWith f l₁ l₂` applies `f : α → β → γ` pointwise to a list `l₁ : List α` and `l₂ : List β`. It
applies, until one of the lists is exhausted. For example,
`zipWith f [0, 1, 2] [6.28, 31] = [f 0 6.28, f 1 31]`.
`zip` is `zipWith` applied to `Prod.mk`. For example,
`zip [a₁, a₂] [b₁, b₂, b₃] = [(a₁, b₁), (a₂, b₂)]`.
`unzip` undoes `zip`. For example, `unzip [(a₁, b₁), (a₂, b₂)] = ([a₁, a₂], [b₁, b₂])`.
-/

assert_not_exists Monoid

universe u

open Nat

namespace List

variable {α : Type u} {β γ δ ε : Type*}

open Function in

theorem rightInverse_unzip_zip :
    RightInverse (unzip : List (α × β) → List α × List β) (uncurry zip) := by
  grind [zip_unzip]
