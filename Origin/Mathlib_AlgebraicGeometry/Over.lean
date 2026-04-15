/-
Extracted from AlgebraicGeometry/Over.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Typeclasses for `S`-schemes and `S`-morphisms

We define these as thin wrappers around `CategoryTheory/Comma/OverClass`.

## Main definition
- `AlgebraicGeometry.Scheme.Over`: `X.Over S` equips `X` with an `S`-scheme structure.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `AlgebraicGeometry.Scheme.Hom.IsOver`: `f.IsOver S` asserts that `f` is an `S`-morphism.

-/

namespace AlgebraicGeometry.Scheme

universe u

open CategoryTheory

variable {X Y : Scheme.{u}} (f : X.Hom Y) (S S' : Scheme.{u})

protected abbrev Over (X S : Scheme.{u}) := OverClass X S

abbrev CanonicallyOver (X S : Scheme.{u}) := CanonicallyOverClass X S

abbrev Hom.IsOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] := HomIsOver f S
