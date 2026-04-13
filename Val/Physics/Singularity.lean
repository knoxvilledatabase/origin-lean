/-
Released under MIT license.
-/
import Val.Field

/-!
# Val Physics: Singularity — Existence Boundaries

The physics equivalent of Foundation.lean. Core patterns that every
physics domain file imports.

Two demos confirmed the mechanism:
- PointCharge.lean: field doesn't exist at r=0 (classical EM). 14 hypotheses dissolved.
- Vacuum.lean: particles don't exist in vacuum (QFT). 17 hypotheses dissolved.

Both dissolved through the same constructor. This file extracts the common
patterns and provides the tools domain files need.

The key addition: cross-type binary lift. Math operations are
Val α → Val α → Val α (same type). Physics operations cross types:
mass × acceleration = force. Different dimensions in, different out.
The existence boundary (origin absorption) works the same way.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Cross-Type Binary Lift
-- ============================================================================

-- Math's mul and add: Val α → Val α → Val α (same type in and out).
-- Physics needs: Val α → Val β → Val γ (different types).
-- Example: Val (mass) × Val (accel) → Val (force).
-- Origin absorption works identically across types.

def liftBin₂ {β γ : Type u} (f : α → β → γ) : Val α → Val β → Val γ
  | origin, _                => origin
  | _, origin                => origin
  | container a, container b => container (f a b)
  | container a, contents b  => container (f a b)
  | contents a, container b  => container (f a b)
  | contents a, contents b   => contents (f a b)

@[simp] theorem liftBin₂_origin_left {β γ : Type u} (f : α → β → γ) (b : Val β) :
    liftBin₂ f origin b = origin := by cases b <;> rfl

@[simp] theorem liftBin₂_origin_right {β γ : Type u} (f : α → β → γ) (a : Val α) :
    liftBin₂ f a origin = origin := by cases a <;> rfl

@[simp] theorem liftBin₂_contents {β γ : Type u} (f : α → β → γ) (a : α) (b : β) :
    liftBin₂ f (contents a) (contents b) = contents (f a b) := rfl

@[simp] theorem liftBin₂_container_container {β γ : Type u} (f : α → β → γ) (a : α) (b : β) :
    liftBin₂ f (container a) (container b) = container (f a b) := rfl

@[simp] theorem liftBin₂_container_contents {β γ : Type u} (f : α → β → γ) (a : α) (b : β) :
    liftBin₂ f (container a) (contents b) = container (f a b) := rfl

@[simp] theorem liftBin₂_contents_container {β γ : Type u} (f : α → β → γ) (a : α) (b : β) :
    liftBin₂ f (contents a) (container b) = container (f a b) := rfl

theorem liftBin₂_contents_ne_origin {β γ : Type u} (f : α → β → γ) (a : α) (b : β) :
    liftBin₂ f (contents a) (contents b) ≠ origin := by simp

-- mul and add are same-type instances of liftBin₂
theorem mul_eq_liftBin₂ [ValArith α] :
    @mul α _ = liftBin₂ ValArith.mulF := by
  funext a b; cases a <;> cases b <;> rfl

theorem add_eq_liftBin₂ [ValArith α] :
    @add α _ = liftBin₂ ValArith.addF := by
  funext a b; cases a <;> cases b <;> rfl

-- ============================================================================
-- Inverse-Square Law (k/r²)
-- ============================================================================

-- Coulomb (kq/r²), gravity (GM/r²), and more.
-- At the singularity (r = origin): absorption. At contents: computes.

def invSquare [ValArith α] (k : α) (r : Val α) : Val α :=
  valMap (fun r₀ => ValArith.mulF k (ValArith.invF (ValArith.mulF r₀ r₀))) r

@[simp] theorem invSquare_origin [ValArith α] (k : α) :
    invSquare k (origin : Val α) = origin := rfl

@[simp] theorem invSquare_contents [ValArith α] (k r₀ : α) :
    invSquare k (contents r₀) =
    contents (ValArith.mulF k (ValArith.invF (ValArith.mulF r₀ r₀))) := rfl

theorem invSquare_ne_origin [ValArith α] (k r₀ : α) :
    invSquare k (contents r₀) ≠ origin := by simp [invSquare]

-- Superposition: two inverse-square fields combined.
theorem invSquare_super_origin_left [ValArith α] (k₁ k₂ : α) (r₂ : Val α) :
    add (invSquare k₁ origin) (invSquare k₂ r₂) = origin := by simp

theorem invSquare_super_origin_right [ValArith α] (k₁ k₂ : α) (r₁ : Val α) :
    add (invSquare k₁ r₁) (invSquare k₂ origin) = origin := by
  cases r₁ <;> simp [invSquare, add]

-- ============================================================================
-- Inverse Law (k/r)
-- ============================================================================

-- Potentials: V = kq/r, V = -GM/r.

def invLaw [ValArith α] (k : α) (r : Val α) : Val α :=
  valMap (fun r₀ => ValArith.mulF k (ValArith.invF r₀)) r

@[simp] theorem invLaw_origin [ValArith α] (k : α) :
    invLaw k (origin : Val α) = origin := rfl

@[simp] theorem invLaw_contents [ValArith α] (k r₀ : α) :
    invLaw k (contents r₀) =
    contents (ValArith.mulF k (ValArith.invF r₀)) := rfl

-- ============================================================================
-- Linear Observable (coupling × x)
-- ============================================================================

-- Field expectations, energies, momenta.

def linearObs [ValArith α] (coupling : α) (x : Val α) : Val α :=
  valMap (ValArith.mulF coupling) x

@[simp] theorem linearObs_origin [ValArith α] (c : α) :
    linearObs c (origin : Val α) = origin := rfl

@[simp] theorem linearObs_contents [ValArith α] (c x : α) :
    linearObs c (contents x) = contents (ValArith.mulF c x) := rfl

end Val
