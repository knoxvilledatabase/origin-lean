/-
Extracted from Data/Num/Basic.lean
Genuine: 15 of 30 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!
# Binary representation of integers using inductive types

Note: Unlike in Coq, where this representation is preferred because of
the reliance on kernel reduction, in Lean this representation is discouraged
in favor of the "Peano" natural numbers `Nat`, and the purpose of this
collection of theorems is to show the equivalence of the different approaches.
-/

inductive PosNum : Type
  | one : PosNum
  | bit1 : PosNum → PosNum
  | bit0 : PosNum → PosNum
  deriving DecidableEq

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

inductive Num : Type
  | zero : Num
  | pos : PosNum → Num
  deriving DecidableEq

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

inductive ZNum : Type
  | zero : ZNum
  | pos : PosNum → ZNum
  | neg : PosNum → ZNum
  deriving DecidableEq

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

namespace PosNum

def bit (b : Bool) : PosNum → PosNum :=
  cond b bit1 bit0

def succ : PosNum → PosNum
  | 1 => bit0 one
  | bit1 n => bit0 (succ n)
  | bit0 n => bit1 n

def isOne : PosNum → Bool
  | 1 => true
  | _ => false

protected def add : PosNum → PosNum → PosNum
  | 1, b => succ b
  | a, 1 => succ a
  | bit0 a, bit0 b => bit0 (PosNum.add a b)
  | bit1 a, bit1 b => bit0 (succ (PosNum.add a b))
  | bit0 a, bit1 b => bit1 (PosNum.add a b)
  | bit1 a, bit0 b => bit1 (PosNum.add a b)

-- INSTANCE (free from Core): :

def pred' : PosNum → Num
  | 1 => 0
  | bit0 n => Num.pos (Num.casesOn (pred' n) 1 bit1)
  | bit1 n => Num.pos (bit0 n)

def pred (a : PosNum) : PosNum :=
  Num.casesOn (pred' a) 1 id

def size : PosNum → PosNum
  | 1 => 1
  | bit0 n => succ (size n)
  | bit1 n => succ (size n)

def natSize : PosNum → Nat
  | 1 => 1
  | bit0 n => Nat.succ (natSize n)
  | bit1 n => Nat.succ (natSize n)

protected def mul (a : PosNum) : PosNum → PosNum
  | 1 => a
  | bit0 b => bit0 (PosNum.mul a b)
  | bit1 b => bit0 (PosNum.mul a b) + a

-- INSTANCE (free from Core): :

def ofNatSucc : ℕ → PosNum
  | 0 => 1
  | Nat.succ n => succ (ofNatSucc n)

def ofNat (n : ℕ) : PosNum :=
  ofNatSucc (Nat.pred n)

-- INSTANCE (free from Core): (priority

open Ordering

def cmp : PosNum → PosNum → Ordering
  | 1, 1 => eq
  | _, 1 => gt
  | 1, _ => lt
  | bit0 a, bit0 b => cmp a b
  | bit0 a, bit1 b => Ordering.casesOn (cmp a b) lt lt gt
  | bit1 a, bit0 b => Ordering.casesOn (cmp a b) lt gt gt
  | bit1 a, bit1 b => cmp a b

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): decidableLT

-- INSTANCE (free from Core): decidableLE

end PosNum

variable {α : Type*} [One α] [Add α]
