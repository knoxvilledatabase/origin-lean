/-
Extracted from AlgebraicTopology/SimplicialSet/Subcomplex.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Subcomplexes of a simplicial set

Given a simplicial set `X`, this file defines the type `X.Subcomplex`
of subcomplexes of `X` as an abbreviation for `Subfunctor X`.
It also introduces a coercion from `X.Subcomplex` to `SSet`.

-/

universe u

open CategoryTheory Simplicial Limits

namespace SSet

-- INSTANCE (free from Core): :

variable (X Y : SSet.{u})

abbrev Subcomplex := Subfunctor X

variable {X Y}

namespace Subcomplex

abbrev toSSet (A : X.Subcomplex) : SSet.{u} := A.toFunctor

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

abbrev ι (A : Subcomplex X) : Quiver.Hom (V := SSet) A X := Subfunctor.ι A

-- INSTANCE (free from Core): (A

variable {S₁ S₂ : X.Subcomplex} (h : S₁ ≤ S₂)

abbrev homOfLE : (S₁ : SSet.{u}) ⟶ (S₂ : SSet.{u}) := Subfunctor.homOfLe h
