/-
Extracted from Tactic/ToLevel.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Tactic.PPWithUniv

/-! # `ToLevel` class

This module defines `Lean.ToLevel`, which is the `Lean.Level` analogue to `Lean.ToExpr`.

**Warning:** Import `Mathlib.Tactic.ToExpr` instead of this one if you are writing `ToExpr`
instances. This ensures that you are using the universe polymorphic `ToExpr` instances that
override the ones from Lean 4 core.

-/

namespace Lean

@[pp_with_univ]
class ToLevel.{u} where
  /-- A `Level` that represents the universe level `u`. -/
  toLevel : Level
  /-- The universe itself. This is only here to avoid the "unused universe parameter" error. -/
  univ : Type u := Sort u

export ToLevel (toLevel)

attribute [pp_with_univ] toLevel

instance : ToLevel.{0} where
  toLevel := .zero

universe u v

instance [ToLevel.{u}] : ToLevel.{u+1} where
  toLevel := .succ toLevel.{u}

def ToLevel.max [ToLevel.{u}] [ToLevel.{v}] : ToLevel.{max u v} where
  toLevel := .max toLevel.{u} toLevel.{v}

def ToLevel.imax [ToLevel.{u}] [ToLevel.{v}] : ToLevel.{imax u v} where
  toLevel := .imax toLevel.{u} toLevel.{v}

end Lean
