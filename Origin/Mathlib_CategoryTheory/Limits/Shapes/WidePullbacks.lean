/-
Extracted from CategoryTheory/Limits/Shapes/WidePullbacks.lean
Genuine: 4 of 10 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Wide pullbacks

We define the category `WidePullbackShape`, (resp. `WidePushoutShape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wideCospan` (`wideSpan`) constructs a functor from this category, hitting
the given morphisms.

We use `WidePullbackShape` to define ordinary pullbacks (pushouts) by using `J := WalkingPair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `HasWidePullbacks` and `HasFiniteWidePullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/

universe w w' v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

variable (J : Type w)

def WidePullbackShape := Option J

-- INSTANCE (free from Core): :

def WidePushoutShape := Option J

-- INSTANCE (free from Core): :

namespace WidePullbackShape

variable {J}

set_option genSizeOfSpec false in

inductive Hom : WidePullbackShape J → WidePullbackShape J → Type w
  | id : ∀ X, Hom X X
  | term : ∀ j : J, Hom (some j) none
  deriving DecidableEq

attribute [nolint unusedArguments] instDecidableEqHom.decEq

-- INSTANCE (free from Core): struct

-- INSTANCE (free from Core): Hom.inhabited

open Lean Elab Tactic

meta def evalCasesBash : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePullbackShape _,
      (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash

-- INSTANCE (free from Core): subsingleton_hom

-- INSTANCE (free from Core): category
