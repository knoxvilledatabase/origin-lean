/-
Extracted from Data/MLList/DepthFirst.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Batteries.Data.MLList.Basic
import Mathlib.Control.Combinators
import Std.Data.HashSet.Basic

noncomputable section

/-!
# Depth first search

We perform depth first search of a tree or graph,
where the neighbours of a vertex are provided either by list `α → List α`
or a lazy list `α → MLList MetaM α`.

This is useful in meta code for searching for solutions in the presence of alternatives.
It can be nice to represent the choices via a lazy list,
so the later choices don't need to be evaluated while we do depth first search on earlier choices.

## Deprecation

This material has been moved out of Mathlib to https://github.com/semorrison/lean-monadic-list.
-/

set_option linter.deprecated false

universe u

variable {α : Type u} {m : Type u → Type u}

section

variable [Monad m] [Alternative m]

partial def depthFirst' (f : Nat → α → m α) (n : Nat) (a : α) : m α :=

pure a <|> joinM ((f n a) <&> (depthFirst' f (n+1)))

def depthFirst (f : α → m α) (a : α) (maxDepth : Option Nat := none) : m α :=
  match maxDepth with
  | some d => depthFirst' (fun n a => if n ≤ d then f a else failure) 0 a
  | none => depthFirst' (fun _ a => f a) 0 a

end

variable [Monad m]

open Lean in

def depthFirstRemovingDuplicates {α : Type u} [BEq α] [Hashable α]
    (f : α → MLList m α) (a : α) (maxDepth : Option Nat := none) : MLList m α :=

let f' : α → MLList (StateT.{u} (Std.HashSet α) m) α := fun a =>

  (f a).liftM >>= fun b => do

    let s ← get

    if s.contains b then failure

    set <| s.insert b

    pure b

(depthFirst f' a maxDepth).runState' (Std.HashSet.empty.insert a)

def depthFirstRemovingDuplicates' [BEq α] [Hashable α]
    (f : α → List α) (a : α) (maxDepth : Option Nat := none) : List α :=

depthFirstRemovingDuplicates

  (fun a => (.ofList (f a) : MLList Option α)) a maxDepth |>.force |>.get!
