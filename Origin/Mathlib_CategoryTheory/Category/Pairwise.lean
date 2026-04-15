/-
Extracted from CategoryTheory/Category/Pairwise.lean
Genuine: 5 of 11 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `Pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(Opens X)ᵒᵖ`),
we produce a functor `Pairwise ι ⥤ α` in the obvious way,
and show that `iSup U` provides a colimit cocone over this functor.
-/

noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

inductive Pairwise (ι : Type v)
  | single : ι → Pairwise ι
  | pair : ι → ι → Pairwise ι
  deriving Fintype, DecidableEq

variable {ι : Type v}

namespace Pairwise

-- INSTANCE (free from Core): pairwiseInhabited

inductive Hom : Pairwise ι → Pairwise ι → Type v
  | id_single : ∀ i, Hom (single i) (single i)
  | id_pair : ∀ i j, Hom (pair i j) (pair i j)
  | left : ∀ i j, Hom (pair i j) (single i)
  | right : ∀ i j, Hom (pair i j) (single j)
  deriving DecidableEq

attribute [nolint unusedArguments] instDecidableEqHom.decEq

open Hom

-- INSTANCE (free from Core): homInhabited

def id : ∀ o : Pairwise ι, Hom o o
  | single i => id_single i
  | pair i j => id_pair i j

def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃
  | _, _, _, id_single _, g => g
  | _, _, _, id_pair _ _, g => g
  | _, _, _, left i j, id_single _ => left i j
  | _, _, _, right i j, id_single _ => right i j

-- INSTANCE (free from Core): :

open Lean Elab Tactic in

meta def pairwiseCases : TacticM Unit := do
  evalTactic (← `(tactic| casesm* (_ : Pairwise _) ⟶ (_ : Pairwise _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] pairwiseCases in

-- INSTANCE (free from Core): :

end

-- INSTANCE (free from Core): {i

-- INSTANCE (free from Core): [Fintype

variable {α : Type u} (U : ι → α)

variable [SemilatticeInf α]
