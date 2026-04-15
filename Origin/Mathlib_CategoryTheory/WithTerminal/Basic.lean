/-
Extracted from CategoryTheory/WithTerminal/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# `WithInitial` and `WithTerminal`

Given a category `C`, this file constructs two objects:
1. `WithTerminal C`, the category built from `C` by formally adjoining a terminal object.
2. `WithInitial C`, the category built from `C` by formally adjoining an initial object.

The terminal resp. initial object is `WithTerminal.star` resp. `WithInitial.star`, and
the proofs that these are terminal resp. initial are in `WithTerminal.star_terminal`
and `WithInitial.star_initial`.

The inclusion from `C` into `WithTerminal C` resp. `WithInitial C` is denoted
`WithTerminal.incl` resp. `WithInitial.incl`.

The relevant constructions needed for the universal properties of these constructions are:
1. `lift`, which lifts `F : C ⥤ D` to a functor from `WithTerminal C` resp. `WithInitial C` in
  the case where an object `Z : D` is provided satisfying some additional conditions.
2. `inclLift` shows that the composition of `lift` with `incl` is isomorphic to the
  functor which was lifted.
3. `liftUnique` provides the uniqueness property of `lift`.

In addition to this, we provide `WithTerminal.map` and `WithInitial.map` providing the
functoriality of these constructions with respect to functors on the base categories.

We define corresponding pseudofunctors `WithTerminal.pseudofunctor` and `WithInitial.pseudofunctor`
from `Cat` to `Cat`.

-/

namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

inductive WithTerminal : Type u
  | of : C → WithTerminal
  | star : WithTerminal
  deriving Inhabited

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithTerminal

inductive WithInitial : Type u
  | of : C → WithInitial
  | star : WithInitial
  deriving Inhabited

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WithInitial

namespace WithTerminal

variable {C}
