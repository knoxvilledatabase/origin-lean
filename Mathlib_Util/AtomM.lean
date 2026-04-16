/-
Extracted from Util/AtomM.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Init
import Lean.Meta.Tactic.Simp.Types
import Qq

noncomputable section

/-!
# A monad for tracking and deduplicating atoms

This monad is used by tactics like `ring` and `abel` to keep uninterpreted atoms in a consistent
order, and also to allow unifying atoms up to a specified transparency mode.

Note: this can become very expensive because it is using `isDefEq`.
For performance reasons, consider whether `Lean.Meta.Canonicalizer.canon` can be used instead.
After canonicalizing, a `HashMap Expr Nat` suffices to keep track of previously seen atoms,
and is much faster as it uses `Expr` equality rather than `isDefEq`.
-/

namespace Mathlib.Tactic

open Lean Meta

structure AtomM.Context where
  /-- The reducibility setting for definitional equality of atoms -/
  red : TransparencyMode
  /-- A simplification to apply to atomic expressions when they are encountered,
  before interning them in the atom list. -/
  evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }
  deriving Inhabited

structure AtomM.State where
  /-- The list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
  atoms : Array Expr := #[]

abbrev AtomM := ReaderT AtomM.Context <| StateRefT AtomM.State MetaM

def AtomM.run {α : Type} (red : TransparencyMode) (m : AtomM α)
    (evalAtom : Expr → MetaM Simp.Result := fun e ↦ pure { expr := e }) :
    MetaM α :=
  (m { red, evalAtom }).run' {}

def AtomM.addAtom (e : Expr) : AtomM (Nat × Expr) := do
  let c ← get
  for h : i in [:c.atoms.size] do
    if ← withTransparency (← read).red <| isDefEq e c.atoms[i] then
      return (i, c.atoms[i])
  modifyGet fun c ↦ ((c.atoms.size, e), { c with atoms := c.atoms.push e })

open Qq in

def AtomM.addAtomQ {u : Level} {α : Q(Type u)} (e : Q($α)) :
    AtomM (Nat × {e' : Q($α) // $e =Q $e'}) := do
  let (n, e') ← AtomM.addAtom e
  return (n, ⟨e', ⟨⟩⟩)

end Mathlib.Tactic
