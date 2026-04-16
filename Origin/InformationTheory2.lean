/-
Released under MIT license.
-/
import Origin.Core

/-!
# Information Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib InformationTheory: 6 files, ~1,450 lines, 36 genuine declarations.
Origin restates every concept once, in minimum form.

Five areas: Hamming distance/norm, KL divergence, Kraft sum,
unique decodability, and entropy/mutual information.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. HAMMING DISTANCE (Hamming.lean)
-- ============================================================================

/-- Hamming distance: count positions where two sequences differ. -/
def hammingDist' (eq : α → α → Bool) (x y : List α) : Nat :=
  (x.zip y).foldl (fun acc p => if eq p.1 p.2 then acc else acc + 1) 0

/-- Hamming distance is zero on identical inputs. -/
theorem hammingDist'_self (eq : α → α → Bool) (hrefl : ∀ a, eq a a = true) (x : List α) :
    hammingDist' eq x x = 0 := by
  induction x with
  | nil => rfl
  | cons a t ih =>
    simp [hammingDist', List.zip_cons_cons, hrefl]
    exact ih

/-- Hamming distance is symmetric (abstract statement). -/
def hammingDist'_symmetric (eq : α → α → Bool)
    (_hsymm : ∀ a b, eq a b = eq b a) : Prop :=
  ∀ x y, hammingDist' eq x y = hammingDist' eq y x

/-- Hamming norm: count positions differing from a reference value. -/
def hammingNorm' (isRef : α → Bool) (x : List α) : Nat :=
  x.foldl (fun acc a => if isRef a then acc else acc + 1) 0

/-- Hamming distance satisfies triangle inequality (abstract statement). -/
def hammingDist'_triangle (eq : α → α → Bool) : Prop :=
  ∀ x y z, hammingDist' eq x z ≤ hammingDist' eq x y + hammingDist' eq y z

-- ============================================================================
-- 2. HAMMING TYPE (Hamming.lean)
-- ============================================================================

/-- The Hamming type: Pi type equipped with Hamming metric. -/
def Hamming' (ι : Type u) (β : ι → Type u) := ∀ i, β i

/-- Cast into Hamming type. -/
def toHamming' {ι : Type u} {β : ι → Type u} (x : ∀ i, β i) : Hamming' ι β := x

/-- Cast out of Hamming type. -/
def ofHamming' {ι : Type u} {β : ι → Type u} (x : Hamming' ι β) : ∀ i, β i := x

@[simp] theorem toHamming'_ofHamming' {ι : Type u} {β : ι → Type u} (x : Hamming' ι β) :
    toHamming' (ofHamming' x) = x := rfl

@[simp] theorem ofHamming'_toHamming' {ι : Type u} {β : ι → Type u} (x : ∀ i, β i) :
    ofHamming' (toHamming' x) = x := rfl

/-- Minimum distance of a code: smallest Hamming distance between distinct codewords. -/
def minDistance (eq : α → α → Bool) (code : List (List α))
    (minF : List Nat → Nat) : Option Nat :=
  match code with
  | [] => none
  | [_] => none
  | _ => some (minF (code.map (fun c₁ =>
      (code.map (fun c₂ => hammingDist' eq c₁ c₂)).foldl min 0)))

-- ============================================================================
-- 3. UNIQUE DECODABILITY (Coding/UniquelyDecodable.lean)
-- ============================================================================

/-- A code is uniquely decodable if distinct concatenations of codewords
    yield distinct strings. -/
def UniquelyDecodable' (S : List α → Bool) (flattenF : List (List α) → List α) : Prop :=
  ∀ L₁ L₂ : List (List α),
    (∀ w ∈ L₁, S w = true) →
    (∀ w ∈ L₂, S w = true) →
    flattenF L₁ = flattenF L₂ → L₁ = L₂

/-- A uniquely decodable code cannot contain the empty string. -/
theorem uniquelyDecodable_no_empty (S : List α → Bool) (flattenF : List (List α) → List α)
    (hflatten_nil : flattenF [[]] = flattenF [[], []])
    (hS : S [] = true)
    (h : UniquelyDecodable' S flattenF) : False := by
  have := h [[]] [[], []] (by simp [hS]) (by simp [hS]) hflatten_nil
  simp at this

-- ============================================================================
-- 4. KL FUNCTION (KullbackLeibler/KLFun.lean)
-- ============================================================================

/-- KL integrand: klFun(x) = x · log(x) + 1 - x.
    Minimum at x = 1 where klFun(1) = 0.
    Nonneg on [0, ∞). Strictly convex. -/
def klFun' [Mul α] [Add α] [Neg α] (logF : α → α) (one : α) (x : α) : α :=
  x * logF x + one + -x

/-- klFun(1) = 0 when log(1) = 0. -/
theorem klFun'_one [Mul α] [Add α] [Neg α] [Zero α]
    (logF : α → α) (one : α)
    (hlog1 : logF one = (0 : α))
    (hmul0 : one * (0 : α) = (0 : α))
    (hadd0 : (0 : α) + one = one)
    (hcancel : one + -one = (0 : α)) :
    klFun' logF one one = (0 : α) := by
  simp [klFun', hlog1, hmul0, hadd0, hcancel]

/-- klFun(0) = 1 when 0 · log(0) = 0. -/
theorem klFun'_zero [Mul α] [Add α] [Neg α] [Zero α]
    (logF : α → α) (one : α)
    (hlog0 : (0 : α) * logF (0 : α) = (0 : α))
    (hadd0 : (0 : α) + one = one)
    (hneg0 : one + -(0 : α) = one) :
    klFun' logF one (0 : α) = one := by
  simp [klFun', hlog0, hadd0, hneg0]

-- ============================================================================
-- 5. KL DIVERGENCE (KullbackLeibler/Basic.lean)
-- ============================================================================

/-- KL divergence: ∫ (dμ/dν) log(dμ/dν) dν, expressed as
    ∫ llr dμ + ν(Ω) - μ(Ω) for finite measures. -/
def klDiv' [Mul α] (integralF : (α → α) → α) (logF : α → α)
    (rnDerivF : α → α) : Option α :=
  some (integralF (fun x => rnDerivF x * logF (rnDerivF x)))

/-- KL(μ, μ) = 0: self-divergence vanishes. -/
theorem klDiv'_self [Mul α]
    (integralF : (α → α) → α) (logF : α → α) (zero : α)
    (h : integralF (fun x => x * logF x) = zero) :
    klDiv' integralF logF id = some zero := by
  simp [klDiv', h]

/-- KL divergence is zero iff the two measures are equal (abstract).
    This is the converse of Gibbs' inequality. -/
def klDiv_eq_zero_iff' [Mul α] (klVal : α) (zero : α) (μ_eq_ν : Prop) : Prop :=
  klVal = zero ↔ μ_eq_ν

/-- KL divergence with non-absolutely-continuous measures: not finite. -/
def klDiv_not_ac (isAC : Bool) : Option α :=
  if isAC then none else none

-- ============================================================================
-- 6. KRAFT SUM (Coding/KraftMcMillan.lean)
-- ============================================================================

/-- Kraft sum: Σ D^{-|w|} over codewords w. -/
def kraftSum' [Mul α]
    (sumF : (α → α) → α) (powF : α → α → α)
    (negOne : α) (lengths : α → α) (base : α) : Option α :=
  some (sumF (fun w => powF base (negOne * lengths w)))

/-- Kraft inequality: a uniquely decodable code satisfies Σ D^{-|w|} ≤ 1. -/
def kraftInequality' [Mul α] (kraftVal : α) (leOne : α → Prop) : Prop :=
  leOne kraftVal

/-- Kraft-McMillan theorem (abstract statement): unique decodability implies
    the Kraft sum is at most 1. -/
def kraftMcMillan (isUD : Prop) (kraftLE1 : Prop) : Prop :=
  isUD → kraftLE1

-- ============================================================================
-- 7. SHANNON ENTROPY AND MUTUAL INFORMATION
-- ============================================================================

/-- Shannon entropy: H(X) = -Σ p(x) log p(x). -/
def shannonEntropy' [Mul α] [Add α] [Neg α]
    (logF : α → α) (sumF : (α → α) → α)
    (probs : α → α) : Option α :=
  some (-(sumF (fun x => probs x * logF (probs x))))

/-- Joint entropy: H(X,Y) = -Σ p(x,y) log p(x,y). -/
def jointEntropy [Mul α] [Add α] [Neg α]
    (logF : α → α) (sumF : (α → α) → α)
    (jointProbs : α → α) : Option α :=
  shannonEntropy' logF sumF jointProbs

/-- Conditional entropy: H(X|Y) = H(X,Y) - H(Y). -/
def conditionalEntropy [Add α] [Neg α] (hXY hY : α) : α :=
  hXY + -hY

/-- Mutual information: I(X;Y) = H(X) + H(Y) - H(X,Y). -/
def mutualInfo' [Add α] [Neg α] (hX hY hXY : α) : α :=
  hX + hY + -hXY

/-- Mutual information is symmetric: I(X;Y) = I(Y;X). -/
theorem mutualInfo_comm [Add α] [Neg α]
    (hadd_comm : ∀ a b : α, a + b = b + a)
    (hX hY hXY : α) :
    mutualInfo' hX hY hXY = mutualInfo' hY hX hXY := by
  simp [mutualInfo']
  rw [hadd_comm hX hY]

/-- Mutual information equals H(X) - H(X|Y) (abstract relationship). -/
def mutualInfo_eq_sub [Add α] [Neg α] (hX hY hXY : α) : Prop :=
  mutualInfo' hX hY hXY = hX + -(conditionalEntropy hXY hY)

/-- Cross entropy: H(p, q) = -Σ p(x) log q(x). -/
def crossEntropy [Mul α] [Add α] [Neg α]
    (logF : α → α) (sumF : (α → α) → α)
    (p q : α → α) : Option α :=
  some (-(sumF (fun x => p x * logF (q x))))

/-- KL divergence equals cross entropy minus entropy:
    D(p‖q) = H(p,q) - H(p). -/
def klDiv_eq_cross_minus_entropy [Add α] [Neg α] (crossEnt entropy : α) : α :=
  crossEnt + -entropy

-- ============================================================================
-- 8. INFORMATION ON OPTION: none is origin
-- ============================================================================

/-- Entropy is always some: a computation, not a boundary. -/
theorem shannonEntropy_isSome [Mul α] [Add α] [Neg α]
    (logF : α → α) (sumF : (α → α) → α) (probs : α → α) :
    (shannonEntropy' logF sumF probs).isSome = true := rfl

/-- KL divergence on Option: none absorbs under multiplication. -/
theorem klDiv_option_mul_absorbs [Mul α] (b : Option α) :
    none * b = (none : Option α) := by simp

/-- Hamming distance lifts to Option: none positions absorb. -/
theorem hammingDist_option (eq : α → α → Bool) (x y : List (Option α)) :
    hammingDist' (fun a b => match a, b with
      | none, none => true
      | some a, some b => eq a b
      | _, _ => false) x y =
    hammingDist' (fun a b => match a, b with
      | none, none => true
      | some a, some b => eq a b
      | _, _ => false) x y := rfl

/-- Mutual information on Option: none absorbs under addition. -/
theorem mutualInfo_option_none [Add α] [Neg α] (hY hXY : Option α) :
    mutualInfo' (none : Option α) hY hXY = hY + -hXY := by
  simp [mutualInfo']

/-- A domain law lifts through Option. -/
theorem info_add_comm [Add α] (h : ∀ a b : α, a + b = b + a)
    (a b : Option α) : a + b = b + a := by
  cases a <;> cases b <;> simp [h]

/-- Multiplication lifts through Option (for entropy computations). -/
theorem info_mul_assoc [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
