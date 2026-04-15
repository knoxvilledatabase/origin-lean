/-
Extracted from Data/PFunctor/Univariate/M.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# M-types

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.
-/

universe u uA uB v w

open Nat Function

open List

variable (F : PFunctor.{uA, uB})

namespace PFunctor

namespace Approx

inductive CofixA : ℕ → Type (max uA uB)
  | continue : CofixA 0
  | intro {n} : ∀ a, (F.B a → CofixA n) → CofixA (succ n)

protected def CofixA.default [Inhabited F.A] : ∀ n, CofixA F n
  | 0 => CofixA.continue
  | succ n => CofixA.intro default fun _ => CofixA.default n

-- INSTANCE (free from Core): [Inhabited

theorem cofixA_eq_zero : ∀ x y : CofixA F 0, x = y
  | CofixA.continue, CofixA.continue => rfl

variable {F}

def head' : ∀ {n}, CofixA F (succ n) → F.A
  | _, CofixA.intro i _ => i

def children' : ∀ {n} (x : CofixA F (succ n)), F.B (head' x) → CofixA F n
  | _, CofixA.intro _ f => f

theorem approx_eta {n : ℕ} (x : CofixA F (n + 1)) : x = CofixA.intro (head' x) (children' x) := by
  cases x; rfl

inductive Agree : ∀ {n : ℕ}, CofixA F n → CofixA F (n + 1) → Prop
  | continu (x : CofixA F 0) (y : CofixA F 1) : Agree x y
  | intro {n} {a} (x : F.B a → CofixA F n) (x' : F.B a → CofixA F (n + 1)) :
    (∀ i : F.B a, Agree (x i) (x' i)) → Agree (CofixA.intro a x) (CofixA.intro a x')

def AllAgree (x : ∀ n, CofixA F n) :=
  ∀ n, Agree (x n) (x (succ n))
