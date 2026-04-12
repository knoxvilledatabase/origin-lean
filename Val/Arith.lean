/-
Released under MIT license.
-/
import Val.Foundation

/-!
# Val α: Level 1 — ValArith (Raw Operations)

The base class. Carries the four operations on α. Defines mul, add, neg, inv
on Val α with sort dispatch. All constructor-combination simp lemmas live here.

No algebraic laws. This level only says "α has these operations."
Domains: SetTheory, Computability, Logic, Data, ModelTheory.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- The Base Class
-- ============================================================================

class ValArith (α : Type u) where
  mulF : α → α → α
  addF : α → α → α
  negF : α → α
  invF : α → α

-- ============================================================================
-- Operations on Val α (sort dispatch + class for α)
-- ============================================================================

def mul [ValArith α] : Val α → Val α → Val α
  | origin, _                  => origin
  | _, origin                  => origin
  | container a, container b   => container (ValArith.mulF a b)
  | container a, contents b    => container (ValArith.mulF a b)
  | contents a, container b    => container (ValArith.mulF a b)
  | contents a, contents b     => contents (ValArith.mulF a b)

def add [ValArith α] : Val α → Val α → Val α
  | origin, _                  => origin
  | _, origin                  => origin
  | container a, container b   => container (ValArith.addF a b)
  | container a, contents b    => container (ValArith.addF a b)
  | contents a, container b    => container (ValArith.addF a b)
  | contents a, contents b     => contents (ValArith.addF a b)

def neg [ValArith α] : Val α → Val α
  | origin       => origin
  | container a  => container (ValArith.negF a)
  | contents a   => contents (ValArith.negF a)

def inv [ValArith α] : Val α → Val α
  | origin       => origin
  | container a  => container (ValArith.invF a)
  | contents a   => contents (ValArith.invF a)

def fdiv [ValArith α] (a b : Val α) : Val α :=
  mul a (inv b)

def project : Val α → Option α
  | origin       => none
  | container a  => some a
  | contents a   => some a

-- ============================================================================
-- Simp Set: mul
-- ============================================================================

@[simp] theorem mul_origin_left [ValArith α] (a : Val α) :
    mul origin a = origin := by cases a <;> rfl

@[simp] theorem mul_origin_right [ValArith α] (a : Val α) :
    mul a origin = origin := by cases a <;> rfl

@[simp] theorem mul_contents_contents [ValArith α] (a b : α) :
    mul (contents a) (contents b) = contents (ValArith.mulF a b) := rfl

@[simp] theorem mul_container_container [ValArith α] (a b : α) :
    mul (container a) (container b) = container (ValArith.mulF a b) := rfl

@[simp] theorem mul_container_contents [ValArith α] (a b : α) :
    mul (container a) (contents b) = container (ValArith.mulF a b) := rfl

@[simp] theorem mul_contents_container [ValArith α] (a b : α) :
    mul (contents a) (container b) = container (ValArith.mulF a b) := rfl

-- ============================================================================
-- Simp Set: add
-- ============================================================================

@[simp] theorem add_origin_left [ValArith α] (a : Val α) :
    add origin a = origin := by cases a <;> rfl

@[simp] theorem add_origin_right [ValArith α] (a : Val α) :
    add a origin = origin := by cases a <;> rfl

@[simp] theorem add_contents_contents [ValArith α] (a b : α) :
    add (contents a) (contents b) = contents (ValArith.addF a b) := rfl

@[simp] theorem add_container_container [ValArith α] (a b : α) :
    add (container a) (container b) = container (ValArith.addF a b) := rfl

@[simp] theorem add_container_contents [ValArith α] (a b : α) :
    add (container a) (contents b) = container (ValArith.addF a b) := rfl

@[simp] theorem add_contents_container [ValArith α] (a b : α) :
    add (contents a) (container b) = container (ValArith.addF a b) := rfl

-- ============================================================================
-- Simp Set: neg, inv
-- ============================================================================

@[simp] theorem neg_origin [ValArith α] : neg (origin : Val α) = origin := rfl
@[simp] theorem neg_container [ValArith α] (a : α) :
    neg (container a : Val α) = container (ValArith.negF a) := rfl
@[simp] theorem neg_contents [ValArith α] (a : α) :
    neg (contents a : Val α) = contents (ValArith.negF a) := rfl

@[simp] theorem inv_origin [ValArith α] : inv (origin : Val α) = origin := rfl
@[simp] theorem inv_container [ValArith α] (a : α) :
    inv (container a : Val α) = container (ValArith.invF a) := rfl
@[simp] theorem inv_contents [ValArith α] (a : α) :
    inv (contents a : Val α) = contents (ValArith.invF a) := rfl

-- ============================================================================
-- Sort-Operation Interaction
-- ============================================================================

@[simp] theorem isContents_mul_contents [ValArith α] (a b : α) :
    isContents (mul (contents a) (contents b)) = True := rfl

@[simp] theorem isContents_add_contents [ValArith α] (a b : α) :
    isContents (add (contents a) (contents b)) = True := rfl

@[simp] theorem isOrigin_mul_origin_left [ValArith α] (x : Val α) :
    isOrigin (mul origin x) = True := by cases x <;> rfl

@[simp] theorem isOrigin_mul_origin_right [ValArith α] (x : Val α) :
    isOrigin (mul x origin) = True := by cases x <;> rfl

-- ============================================================================
-- Contents closure: contents never produce origin
-- ============================================================================

theorem mul_contents_ne_origin [ValArith α] (a b : α) :
    mul (contents a) (contents b) ≠ origin := by simp

theorem add_contents_ne_origin [ValArith α] (a b : α) :
    add (contents a) (contents b) ≠ origin := by simp

end Val
