/-
Extracted from Algebra/Expr.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Group.ZeroOne
import Qq

/-! # Helpers to invoke functions involving algebra at tactic time

This file provides instances on `x y : Q($α)` such that `x + y = q($x + $y)`.
-/

open Qq

def Expr.instOne {u : Lean.Level} (α : Q(Type u)) (_ : Q(One $α)) : One Q($α) where
  one := q(1 : $α)

def Expr.instZero {u : Lean.Level} (α : Q(Type u)) (_ : Q(Zero $α)) : Zero Q($α) where
  zero := q(0 : $α)

def Expr.instMul {u : Lean.Level} (α : Q(Type u)) (_ : Q(Mul $α)) : Mul Q($α) where
  mul x y := q($x * $y)

def Expr.instAdd {u : Lean.Level} (α : Q(Type u)) (_ : Q(Add $α)) : Add Q($α) where
  add x y := q($x + $y)
