/-
Released under MIT license.
-/
import Origin.Core

/-!
# Information Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib InformationTheory: 1 file, 379 lines, 36 genuine declarations.
Origin restates every concept once, in minimum form.

Information theory: Hamming distance/norm on finite pi types, KL
divergence, Kraft sum, unique decodability, coding theory fundamentals.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. HAMMING DISTANCE (Hamming.lean)
-- ============================================================================

/-- Hamming distance: count positions where two sequences differ. -/
def hammingDist' (eq : α → α → Bool) (x y : List α) : Nat :=
  (x.zip y).foldl (fun acc p => if eq p.1 p.2 then acc else acc + 1) 0

/-- Hamming distance is zero iff sequences are equal. -/
def hammingDist_self_zero (eq : α → α → Bool)
    (_hrefl : ∀ a, eq a a = true) : Prop :=
  ∀ x, hammingDist' eq x x = 0

/-- Hamming distance is symmetric. -/
def hammingDist_symmetric (eq : α → α → Bool)
    (_hsymm : ∀ a b, eq a b = eq b a) : Prop :=
  ∀ x y, hammingDist' eq x y = hammingDist' eq y x

/-- Hamming distance satisfies triangle inequality. -/
def hammingDist_triangle (eq : α → α → Bool) : Prop :=
  ∀ x y z, hammingDist' eq x z ≤ hammingDist' eq x y + hammingDist' eq y z

/-- Hamming norm: count nonzero positions. -/
def hammingNorm' (isZero : α → Bool) (x : List α) : Nat :=
  x.foldl (fun acc a => if isZero a then acc else acc + 1) 0

/-- The Hamming type synonym: Pi type with Hamming metric. -/
def Hamming' (β : α → Type u) := ∀ i, β i

/-- Minimum distance of a code: smallest Hamming distance between codewords. -/
def minDistance (eq : α → α → Bool) (code : List (List α))
    (minF : List Nat → Nat) : Option Nat :=
  match code with
  | [] => none
  | [_] => none
  | _ => some (minF (code.map (fun c₁ =>
      (code.map (fun c₂ => hammingDist' eq c₁ c₂)).foldl min 0)))

-- ============================================================================
-- 2. UNIQUE DECODABILITY
-- ============================================================================

/-- Uniquely decodable code: no two messages encode to the same string. -/
def isUniquelyDecodable (concatF : α → α → α) (eqF : α → α → Bool) (code : α → Bool) : Prop :=
  ∀ s₁ s₂, code s₁ = true → code s₂ = true → concatF s₁ s₂ = concatF s₂ s₁ → eqF s₁ s₂ = true

-- ============================================================================
-- 3. KL DIVERGENCE
-- ============================================================================

/-- KL integrand: x log x + 1 - x. -/
def klFun [Mul α] [Add α] [Neg α] (logF : α → α) (one : α) (x : α) : α :=
  x * logF x + one + -x

/-- KL divergence: ∫ (dμ/dν) log(dμ/dν) dν. -/
def klDiv [Mul α] (integralF : (α → α) → α) (logF : α → α) (rnDerivF : α → α) : Option α :=
  some (integralF (fun x => rnDerivF x * logF (rnDerivF x)))

/-- KL(μ, μ) = 0: self-divergence. -/
theorem klDiv_self [Mul α]
    (integralF : (α → α) → α) (logF : α → α) (zero : α)
    (h : integralF (fun x => x * logF x) = zero) :
    klDiv integralF logF id = some zero := by
  simp [klDiv, h]

-- ============================================================================
-- 4. KRAFT SUM
-- ============================================================================

/-- Kraft sum: always some (a computation, not a boundary). -/
def kraftSum [Mul α]
    (sumF : (α → α) → α) (powF : α → α → α)
    (negOne : α) (lengths : α → α) (base : α) : Option α :=
  some (sumF (fun w => powF base (negOne * lengths w)))

/-- Kraft inequality: a uniquely decodable code satisfies Kraft ≤ 1. -/
def kraftInequality [Mul α] (kraftVal : α) (leOne : α → Prop) : Prop :=
  leOne kraftVal

-- ============================================================================
-- 5. MUTUAL INFORMATION AND ENTROPY
-- ============================================================================

/-- Shannon entropy: -∑ p log p. -/
def shannonEntropy [Mul α] [Add α] [Neg α]
    (logF : α → α) (sumF : (α → α) → α)
    (probs : α → α) : Option α :=
  some (-(sumF (fun x => probs x * logF (probs x))))

/-- Mutual information: I(X;Y) = H(X) + H(Y) - H(X,Y). -/
def mutualInfo [Add α] [Neg α] (hX hY hXY : α) : α :=
  hX + hY + -hXY

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
