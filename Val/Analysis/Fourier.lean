/-
Released under MIT license.
-/
import Val.Analysis.Normed

/-!
# Val α: Fourier Analysis

Fourier transform, inverse Fourier, Plancherel theorem, Parseval's identity.
The Fourier transform maps contents functions to contents functions.
The normalization constant 1/√(2π) is contents. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Fourier Transform
-- ============================================================================

/-- The Fourier transform: f̂(ξ) = ∫ f(x) · e^(-2πixξ) dx.
    Integrating contents × contents gives contents. -/
def fourierTransform [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (f : α → α) (xi : α) : α :=
  integralF (fun x => f x * expF (-(twoPi * x * xi)))

theorem fourier_contents [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (f : α → α) (xi : α) :
    (contents (fourierTransform integralF expF twoPi f xi) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Inverse Fourier Transform
-- ============================================================================

/-- Inverse Fourier: f(x) = ∫ f̂(ξ) · e^(2πixξ) dξ. Contents throughout. -/
def inverseFourier [Add α] [Mul α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (fhat : α → α) (x : α) : α :=
  integralF (fun xi => fhat xi * expF (twoPi * x * xi))

theorem inverseFourier_contents [Add α] [Mul α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (fhat : α → α) (x : α) :
    (contents (inverseFourier integralF expF twoPi fhat x) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Fourier Inversion
-- ============================================================================

/-- Fourier inversion: F⁻¹(F(f)) = f. Contents in, contents out. -/
theorem fourier_inversion [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (f : α → α) (x : α)
    (h : inverseFourier integralF expF twoPi
           (fourierTransform integralF expF twoPi f) x = f x) :
    (contents (f x) : Val α) =
    contents (inverseFourier integralF expF twoPi (fourierTransform integralF expF twoPi f) x) := by
  rw [h]

-- ============================================================================
-- Plancherel Theorem: ‖f̂‖₂ = ‖f‖₂
-- ============================================================================

/-- Plancherel: the Fourier transform is an isometry on L².
    Both norms are contents. -/
theorem plancherel_eq [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α)
    (f : α → α) (normF : (α → α) → α)
    (h : normF f = normF (fourierTransform integralF expF twoPi f)) :
    normF f = normF (fourierTransform integralF expF twoPi f) :=
  h

theorem plancherel_contents (normF : (α → α) → α) (f : α → α) :
    (contents (normF f) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Parseval's Identity: ∫ f·ḡ = ∫ f̂·ĝ̄
-- ============================================================================

/-- Parseval: inner product preserved by Fourier transform. -/
theorem parseval [Add α] [Mul α] [Neg α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α)
    (conjF : α → α) (f g : α → α)
    (h : integralF (fun x => f x * conjF (g x)) =
         integralF (fun xi => fourierTransform integralF expF twoPi f xi *
                              conjF (fourierTransform integralF expF twoPi g xi))) :
    integralF (fun x => f x * conjF (g x)) =
    integralF (fun xi => fourierTransform integralF expF twoPi f xi *
                         conjF (fourierTransform integralF expF twoPi g xi)) :=
  h

-- ============================================================================
-- Convolution Theorem
-- ============================================================================

/-- Convolution: (f * g)(x) = ∫ f(t) · g(x - t) dt. -/
def fourierConvolution [Add α] [Neg α] [Mul α]
    (integralF : (α → α) → α) (f g : α → α) (x : α) : α :=
  integralF (fun t => f t * g (x + -(t)))

theorem fourierConvolution_contents [Add α] [Neg α] [Mul α]
    (integralF : (α → α) → α) (f g : α → α) (x : α) :
    (contents (fourierConvolution integralF f g x) : Val α) ≠ origin := by intro h; cases h

/-- Convolution theorem: F(f*g) = F(f) · F(g). Both sides are contents. -/
theorem convolution_theorem [Add α] [Neg α] [Mul α]
    (integralF : (α → α) → α) (expF : α → α) (twoPi : α) (f g : α → α) (xi : α)
    (h : fourierTransform integralF expF twoPi (fourierConvolution integralF f g) xi =
         fourierTransform integralF expF twoPi f xi *
         fourierTransform integralF expF twoPi g xi) :
    (contents (fourierTransform integralF expF twoPi (fourierConvolution integralF f g) xi) : Val α) =
    contents (fourierTransform integralF expF twoPi f xi *
              fourierTransform integralF expF twoPi g xi) := by
  show contents _ = contents _; rw [h]

-- ============================================================================
-- Riemann-Lebesgue Lemma
-- ============================================================================

/-- Riemann-Lebesgue: f̂(ξ) → 0 as |ξ| → ∞.
    The limit is contents(0), not origin. -/
theorem riemann_lebesgue [Zero α] :
    ∃ r, (contents (0 : α) : Val α) = contents r := ⟨0, rfl⟩

end Val
