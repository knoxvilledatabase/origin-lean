/-
Extracted from SetTheory/Game/State.lean
Genuine: 13 | Conflates: 0 | Dissolved: 4 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.SetTheory.Game.Short

/-!
# Games described via "the state of the board".

We provide a simple mechanism for constructing combinatorial (pre-)games, by describing
"the state of the board", and providing an upper bound on the number of turns remaining.


## Implementation notes

We're very careful to produce a computable definition, so small games can be evaluated
using `decide`. To achieve this, I've had to rely solely on induction on natural numbers:
relying on general well-foundedness seems to be poisonous to computation?

See `SetTheory/Game/Domineering` for an example using this construction.
-/

universe u

namespace SetTheory

namespace PGame

class State (S : Type u) where
  turnBound : S → ℕ
  l : S → Finset S
  r : S → Finset S
  left_bound : ∀ {s t : S}, t ∈ l s → turnBound t < turnBound s
  right_bound : ∀ {s t : S}, t ∈ r s → turnBound t < turnBound s

open State

variable {S : Type u} [State S]

-- DISSOLVED: turnBound_ne_zero_of_left_move

-- DISSOLVED: turnBound_ne_zero_of_right_move

theorem turnBound_of_left {s t : S} (m : t ∈ l s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (left_bound m) h)

theorem turnBound_of_right {s t : S} (m : t ∈ r s) (n : ℕ) (h : turnBound s ≤ n + 1) :
    turnBound t ≤ n :=
  Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (right_bound m) h)

-- DISSOLVED: ofStateAux

-- DISSOLVED: ofStateAuxRelabelling

def ofState (s : S) : PGame :=
  ofStateAux (turnBound s) s (refl _)

def leftMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    LeftMoves (ofStateAux n s h) ≃ { t // t ∈ l s } := by induction n <;> rfl

def leftMovesOfState (s : S) : LeftMoves (ofState s) ≃ { t // t ∈ l s } :=
  leftMovesOfStateAux _ _

def rightMovesOfStateAux (n : ℕ) {s : S} (h : turnBound s ≤ n) :
    RightMoves (ofStateAux n s h) ≃ { t // t ∈ r s } := by induction n <;> rfl

def rightMovesOfState (s : S) : RightMoves (ofState s) ≃ { t // t ∈ r s } :=
  rightMovesOfStateAux _ _

def relabellingMoveLeftAux (n : ℕ) {s : S} (h : turnBound s ≤ n)
    (t : LeftMoves (ofStateAux n s h)) :
    Relabelling (moveLeft (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((leftMovesOfStateAux n h) t : S)
        (turnBound_of_left ((leftMovesOfStateAux n h) t).2 (n - 1)
          (Nat.le_trans h le_tsub_add))) := by
  induction n
  · have t' := (leftMovesOfStateAux 0 h) t
    exfalso; exact turnBound_ne_zero_of_left_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl

def relabellingMoveLeft (s : S) (t : LeftMoves (ofState s)) :
    Relabelling (moveLeft (ofState s) t) (ofState ((leftMovesOfState s).toFun t : S)) := by
  trans
  · apply relabellingMoveLeftAux
  · apply ofStateAuxRelabelling

def relabellingMoveRightAux (n : ℕ) {s : S} (h : turnBound s ≤ n)
    (t : RightMoves (ofStateAux n s h)) :
    Relabelling (moveRight (ofStateAux n s h) t)
      (ofStateAux (n - 1) ((rightMovesOfStateAux n h) t : S)
        (turnBound_of_right ((rightMovesOfStateAux n h) t).2 (n - 1)
          (Nat.le_trans h le_tsub_add))) := by
  induction n
  · have t' := (rightMovesOfStateAux 0 h) t
    exfalso; exact turnBound_ne_zero_of_right_move t'.2 (nonpos_iff_eq_zero.mp h)
  · rfl

def relabellingMoveRight (s : S) (t : RightMoves (ofState s)) :
    Relabelling (moveRight (ofState s) t) (ofState ((rightMovesOfState s).toFun t : S)) := by
  trans
  · apply relabellingMoveRightAux
  · apply ofStateAuxRelabelling

instance fintypeLeftMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (LeftMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (leftMovesOfStateAux _ _).symm

instance fintypeRightMovesOfStateAux (n : ℕ) (s : S) (h : turnBound s ≤ n) :
    Fintype (RightMoves (ofStateAux n s h)) := by
  apply Fintype.ofEquiv _ (rightMovesOfStateAux _ _).symm

instance shortOfStateAux : ∀ (n : ℕ) {s : S} (h : turnBound s ≤ n), Short (ofStateAux n s h)
  | 0, s, h =>
    Short.mk'
      (fun i => by
        have i := (leftMovesOfStateAux _ _).toFun i
        exfalso
        exact turnBound_ne_zero_of_left_move i.2 (nonpos_iff_eq_zero.mp h))
      fun j => by
      have j := (rightMovesOfStateAux _ _).toFun j
      exfalso
      exact turnBound_ne_zero_of_right_move j.2 (nonpos_iff_eq_zero.mp h)
  | n + 1, _, h =>
    Short.mk'
      (fun i =>
        shortOfRelabelling (relabellingMoveLeftAux (n + 1) h i).symm (shortOfStateAux n _))
      fun j =>
      shortOfRelabelling (relabellingMoveRightAux (n + 1) h j).symm (shortOfStateAux n _)

instance shortOfState (s : S) : Short (ofState s) := by
  dsimp [PGame.ofState]
  infer_instance

end PGame

namespace Game

def ofState {S : Type u} [PGame.State S] (s : S) : Game :=
  ⟦PGame.ofState s⟧

end Game

end SetTheory
