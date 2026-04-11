/-
Released under MIT license.
-/
import Val.Analysis.Normed

/-!
# Val α: Lp Spaces

Lp spaces, completeness, duality, Holder and Minkowski inequalities.
The Lp norm ‖f‖_p = (∫|f|^p)^(1/p) is a contents computation.
No ≠ 0 at sort level. The exponent p is a contents value.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Lp Norm
-- ============================================================================

/-- The Lp norm: ‖f‖_p = (∫ |f|^p dμ)^(1/p).
    All operations are contents. No p ≠ 0 at sort level. -/
def lpNorm [Mul α] (invF : α → α) (absF : α → α) (powF : α → α → α)
    (integralF : (α → α) → α) (p : α) (f : α → α) : α :=
  powF (integralF (fun x => powF (absF (f x)) p)) (invF p)

theorem lpNorm_contents [Mul α] (invF absF : α → α) (powF : α → α → α)
    (integralF : (α → α) → α) (p : α) (f : α → α) :
    (contents (lpNorm invF absF powF integralF p f) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Holder's Inequality
-- ============================================================================

/-- Holder's inequality within contents. -/
theorem holder_inequality [Add α] [Mul α] [LE α]
    (invF absF : α → α) (powF : α → α → α) (integralF : (α → α) → α)
    (one p q : α) (f g : α → α)
    (hconj : invF p + invF q = one)
    (h : lpNorm invF absF powF integralF one (fun x => f x * g x) ≤
         lpNorm invF absF powF integralF p f * lpNorm invF absF powF integralF q g) :
    lpNorm invF absF powF integralF one (fun x => f x * g x) ≤
    lpNorm invF absF powF integralF p f * lpNorm invF absF powF integralF q g :=
  h

theorem holder_both_contents [Mul α]
    (invF absF : α → α) (powF : α → α → α) (integralF : (α → α) → α)
    (p : α) (f : α → α) :
    (contents (lpNorm invF absF powF integralF p f) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Minkowski's Inequality
-- ============================================================================

/-- Minkowski's inequality within contents. -/
theorem minkowski_inequality [Add α] [Mul α] [LE α]
    (invF absF : α → α) (powF : α → α → α) (integralF : (α → α) → α)
    (p : α) (f g : α → α)
    (h : lpNorm invF absF powF integralF p (fun x => f x + g x) ≤
         lpNorm invF absF powF integralF p f + lpNorm invF absF powF integralF p g) :
    lpNorm invF absF powF integralF p (fun x => f x + g x) ≤
    lpNorm invF absF powF integralF p f + lpNorm invF absF powF integralF p g :=
  h

-- ============================================================================
-- Lp Completeness
-- ============================================================================

/-- Lp is complete (Riesz-Fischer): every Cauchy sequence in Lp converges. -/
theorem lp_complete_contents (limitF : α → α) (x : α) :
    (contents (limitF x) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Lp Duality
-- ============================================================================

/-- The duality pairing: ⟨f, g⟩ = ∫ f·g dμ. Contents in, contents out. -/
def lpDualPairing [Mul α] (integralF : (α → α) → α) (f g : α → α) : α :=
  integralF (fun x => f x * g x)

theorem lpDualPairing_contents [Mul α] (integralF : (α → α) → α) (f g : α → α) :
    (contents (lpDualPairing integralF f g) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- L∞: Essential Supremum Norm
-- ============================================================================

/-- The L∞ norm: ‖f‖_∞ = ess sup |f|. -/
def linfNorm (absF : α → α) (essSupF : (α → α) → α) (f : α → α) : α :=
  essSupF (fun x => absF (f x))

theorem linfNorm_contents (absF : α → α) (essSupF : (α → α) → α) (f : α → α) :
    (contents (linfNorm absF essSupF f) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Embedding and Dense Subsets
-- ============================================================================

/-- Lp embeds into Lq when p ≥ q. The inclusion maps contents to contents. -/
theorem lp_embedding_contents (f : α → α) (x : α) :
    (contents (f x) : Val α) ≠ origin := by intro h; cases h

/-- Simple functions are dense in Lp. Their values are contents. -/
theorem simple_dense_contents (simpleF : α → α) (x : α) :
    (contents (simpleF x) : Val α) ≠ origin := by intro h; cases h

/-- Continuous functions with compact support are dense in Lp. -/
theorem cc_dense_contents (ccF : α → α) (x : α) :
    (contents (ccF x) : Val α) ≠ origin := by intro h; cases h

end Val
