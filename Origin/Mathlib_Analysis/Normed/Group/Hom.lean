/-
Extracted from Analysis/Normed/Group/Hom.lean
Genuine: 7 of 10 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory of `SeminormedAddGroupHom` and we specialize to `NormedAddGroupHom` when needed.
-/

noncomputable section

open NNReal

structure NormedAddGroupHom (V W : Type*) [SeminormedAddCommGroup V]
  [SeminormedAddCommGroup W] where
  /-- The function underlying a `NormedAddGroupHom` -/
  toFun : V → W
  /-- A `NormedAddGroupHom` is additive. -/
  map_add' : ∀ v₁ v₂, toFun (v₁ + v₂) = toFun v₁ + toFun v₂
  /-- A `NormedAddGroupHom` is bounded. -/
  bound' : ∃ C, ∀ v, ‖toFun v‖ ≤ C * ‖v‖

namespace AddMonoidHom

variable {V W : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
  {f g : NormedAddGroupHom V W}

def mkNormedAddGroupHom (f : V →+ W) (C : ℝ) (h : ∀ v, ‖f v‖ ≤ C * ‖v‖) : NormedAddGroupHom V W :=
  { f with bound' := ⟨C, h⟩ }

def mkNormedAddGroupHom' (f : V →+ W) (C : ℝ≥0) (hC : ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊) :
    NormedAddGroupHom V W :=
  { f with bound' := ⟨C, hC⟩ }

end AddMonoidHom

namespace NormedAddGroupHom

variable {V V₁ V₂ V₃ : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [SeminormedAddCommGroup V₃]

variable {f g : NormedAddGroupHom V₁ V₂}

def ofLipschitz (f : V₁ →+ V₂) {K : ℝ≥0} (h : LipschitzWith K f) : NormedAddGroupHom V₁ V₂ :=
  f.mkNormedAddGroupHom K fun x ↦ by simpa only [map_zero, dist_zero_right] using h.dist_le_mul x 0

-- INSTANCE (free from Core): funLike

-- INSTANCE (free from Core): toAddMonoidHomClass

initialize_simps_projections NormedAddGroupHom (toFun → apply)

theorem coe_inj (H : (f : V₁ → V₂) = g) : f = g := by
  cases f; cases g; congr

theorem coe_injective : @Function.Injective (NormedAddGroupHom V₁ V₂) (V₁ → V₂) toFun := by
  apply coe_inj

theorem coe_inj_iff : f = g ↔ (f : V₁ → V₂) = g :=
  ⟨congr_arg _, coe_inj⟩
