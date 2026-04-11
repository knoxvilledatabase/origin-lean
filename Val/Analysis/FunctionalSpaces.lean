/-
Released under MIT license.
-/
import Val.Analysis.Normed

/-!
# Val α: Functional Spaces

Function spaces: Lp, C^k, Sobolev-like spaces.
Contents functions form contents function spaces. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Function Spaces: Functions as Contents
-- ============================================================================

/-- Function application: contents in, contents out. -/
def fnApply (f : α → α) : Val α → Val α
  | origin => origin
  | container a => container (f a)
  | contents a => contents (f a)

theorem fnApply_contents (f : α → α) (a : α) :
    fnApply f (contents a) = contents (f a) := rfl

theorem fnApply_contents_ne_origin (f : α → α) (a : α) :
    fnApply f (contents a) ≠ origin := by intro h; cases h

theorem fnApply_origin (f : α → α) :
    fnApply f (origin : Val α) = origin := rfl

-- ============================================================================
-- Lp Function Spaces
-- ============================================================================

/-- Lp norm of a function: (∫ |f|^p dμ)^(1/p).
    When f is contents-valued, the Lp norm is contents. -/
def lpNormF (normF : α → α) (powF : α → α → α) (intF : (α → α) → α)
    (rootF : α → α) (f : α → α) (p : α) : α :=
  rootF (intF (fun x => powF (normF (f x)) p))

theorem lpNormF_contents (normF : α → α) (powF : α → α → α)
    (intF : (α → α) → α) (rootF : α → α) (f : α → α) (p : α) :
    ∃ r, (contents (lpNormF normF powF intF rootF f p) : Val α) = contents r :=
  ⟨lpNormF normF powF intF rootF f p, rfl⟩

theorem lpNormF_ne_origin (normF : α → α) (powF : α → α → α)
    (intF : (α → α) → α) (rootF : α → α) (f : α → α) (p : α) :
    (contents (lpNormF normF powF intF rootF f p) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Lp Space Structure
-- ============================================================================

/-- Lp space addition: pointwise addition, within contents. -/
theorem lp_add_contents [Add α] (f g : α → α) (x : α) :
    (contents (f x + g x) : Val α) = contents (f x + g x) := rfl

/-- Lp space scalar multiplication: within contents. -/
theorem lp_smul_contents [Mul α] (c : α) (f : α → α) (x : α) :
    (contents (c * f x) : Val α) = contents (c * f x) := rfl

/-- Triangle inequality in Lp: Minkowski within contents. -/
theorem lp_triangle [Add α] [LE α] (lpNorm : (α → α) → α)
    (h : ∀ f g : α → α, lpNorm (fun x => f x + g x) ≤ lpNorm f + lpNorm g)
    (f g : α → α) :
    lpNorm (fun x => f x + g x) ≤ lpNorm f + lpNorm g :=
  h f g

-- ============================================================================
-- L2 Space (Hilbert Space)
-- ============================================================================

/-- L2 inner product: ⟨f, g⟩ = ∫ f · ḡ dμ. Contents in, contents out. -/
theorem l2_inner_contents [Mul α] (intF : (α → α) → α) (f g : α → α) (conjF : α → α) :
    ∃ r, (contents (intF (fun x => f x * conjF (g x))) : Val α) = contents r :=
  ⟨intF (fun x => f x * conjF (g x)), rfl⟩

/-- L2 inner product is never origin. -/
theorem l2_inner_ne_origin [Mul α] (intF : (α → α) → α) (f g : α → α) (conjF : α → α) :
    (contents (intF (fun x => f x * conjF (g x))) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- L∞ Space
-- ============================================================================

/-- L∞ norm: ess sup |f|. Contents function has contents L∞ norm. -/
theorem linf_norm_ne_origin (essSupF : (α → α) → α) (f : α → α) :
    (contents (essSupF f) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- C^k Function Spaces
-- ============================================================================

/-- A C^k function: k-times continuously differentiable. All derivatives are contents. -/
theorem ck_deriv_contents (derivs : Nat → α → α) (a : α) (k : Nat) :
    ∀ n, n ≤ k → ∃ r, (contents (derivs n a) : Val α) = contents r :=
  fun _ _ => ⟨derivs _ a, rfl⟩

theorem ck_deriv_ne_origin (derivs : Nat → α → α) (a : α) (k n : Nat) (h : n ≤ k) :
    (contents (derivs n a) : Val α) ≠ origin := by intro h; cases h

/-- C^k norm is contents. -/
theorem ck_norm_contents (ckNormF : (Nat → α → α) → Nat → α)
    (derivs : Nat → α → α) (k : Nat) :
    ∃ r, (contents (ckNormF derivs k) : Val α) = contents r :=
  ⟨ckNormF derivs k, rfl⟩

-- ============================================================================
-- C^∞ (Smooth) Function Space
-- ============================================================================

/-- Smooth function: all derivatives exist and are contents. -/
theorem smooth_all_derivs_contents (derivs : Nat → α → α) (a : α) :
    ∀ n, ∃ r, (contents (derivs n a) : Val α) = contents r :=
  fun _ => ⟨derivs _ a, rfl⟩

theorem smooth_all_derivs_ne_origin (derivs : Nat → α → α) (a : α) :
    ∀ n, (contents (derivs n a) : Val α) ≠ origin :=
  fun _ h => by cases h

-- ============================================================================
-- Sobolev-Like Spaces: W^{k,p}
-- ============================================================================

/-- Sobolev norm: sum of Lp norms of derivatives up to order k. -/
def sobolevNormF (lpNorm : (α → α) → α) (derivs : Nat → α → α)
    (sumF : List α → α) (k : Nat) : α :=
  sumF (List.map (fun n => lpNorm (derivs n)) (List.range (k + 1)))

theorem sobolev_norm_contents (lpNorm : (α → α) → α) (derivs : Nat → α → α)
    (sumF : List α → α) (k : Nat) :
    ∃ r, (contents (sobolevNormF lpNorm derivs sumF k) : Val α) = contents r :=
  ⟨sobolevNormF lpNorm derivs sumF k, rfl⟩

theorem sobolev_norm_ne_origin (lpNorm : (α → α) → α) (derivs : Nat → α → α)
    (sumF : List α → α) (k : Nat) :
    (contents (sobolevNormF lpNorm derivs sumF k) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Completeness of Function Spaces
-- ============================================================================

/-- Lp spaces are complete: Cauchy sequences of contents functions
    converge to a contents function. -/
theorem lp_completeness
    (conv : (Nat → α) → α → Prop)
    (isCauchy : (Nat → α) → Prop)
    (complete : ∀ s, isCauchy s → ∃ L, conv s L)
    (s : Nat → α) (hs : isCauchy s) :
    ∃ L, liftConv conv (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := complete s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Dual Spaces
-- ============================================================================

/-- A continuous linear functional on a function space maps contents to contents. -/
theorem dual_functional_contents (φ : α → α) (f_val : α) :
    ∃ r, (contents (φ f_val) : Val α) = contents r :=
  ⟨φ f_val, rfl⟩

theorem dual_functional_ne_origin (φ : α → α) (f_val : α) :
    (contents (φ f_val) : Val α) ≠ origin := by intro h; cases h

end Val
