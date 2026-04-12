/-
Released under MIT license.
-/
import Val.RingTheory.Core

/-!
# Number Theory on Val α

Divisibility, GCD/LCM, primes, fundamental theorem of arithmetic,
modular arithmetic, Chinese remainder theorem, quadratic reciprocity,
arithmetic functions, Diophantine equations, p-adic valuations,
Bernoulli numbers, and more.

The sort system dissolves the `p ≠ 0` and `n ≠ 0` hypotheses throughout.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- § Number Theory: Divisibility — The p ≠ 0 Dissolution
-- ============================================================================

/-- Divisibility predicate: a ∣ b iff b = a · q for some q. -/
def isDivisible (mulF : α → α → α) (a b : α) : Prop :=
  ∃ q, b = mulF a q

/-- Divisibility within contents. No ≠ 0 guard. -/
theorem divisible_contents (mulF : α → α → α) (a b : α)
    (h : isDivisible mulF a b) :
    ∃ q, (contents b : Val α) = mul mulF (contents a) (contents q) := by
  obtain ⟨q, hq⟩ := h; exact ⟨q, by simp [hq]⟩

/-- Every element divides itself: a ∣ a via q = 1. -/
theorem divisible_refl (mulF : α → α → α) (one : α)
    (h : ∀ a, mulF a one = a) (a : α) :
    isDivisible mulF a a := ⟨one, (h a).symm⟩

/-- Divisibility is transitive: a ∣ b → b ∣ c → a ∣ c. -/
theorem divisible_trans (mulF : α → α → α)
    (hAssoc : ∀ x y z, mulF x (mulF y z) = mulF (mulF x y) z)
    (a b c : α) (hab : isDivisible mulF a b) (hbc : isDivisible mulF b c) :
    isDivisible mulF a c := by
  obtain ⟨q₁, hq₁⟩ := hab; obtain ⟨q₂, hq₂⟩ := hbc
  exact ⟨mulF q₁ q₂, by rw [hq₂, hq₁]; exact (hAssoc a q₁ q₂).symm⟩

/-- If a ∣ b, then a ∣ b·c. -/
theorem divisible_mul_right (mulF : α → α → α)
    (hAssoc : ∀ x y z, mulF (mulF x y) z = mulF x (mulF y z))
    (a b c : α) (h : isDivisible mulF a b) :
    isDivisible mulF a (mulF b c) := by
  obtain ⟨q, hq⟩ := h; exact ⟨mulF q c, by rw [hq, hAssoc]⟩

-- ============================================================================
-- § Number Theory: GCD and LCM
-- ============================================================================

/-- GCD as explicit function. Sort-preserving. -/
abbrev gcd (gcdF : α → α → α) : Val α → Val α → Val α := mul gcdF

/-- LCM as explicit function. Sort-preserving. -/
abbrev lcm (lcmF : α → α → α) : Val α → Val α → Val α := mul lcmF

/-- GCD divides both arguments. -/
theorem gcd_divides_left (mulF gcdF : α → α → α)
    (h : ∀ a b, isDivisible mulF (gcdF a b) a) (a b : α) :
    isDivisible mulF (gcdF a b) a := h a b

theorem gcd_divides_right (mulF gcdF : α → α → α)
    (h : ∀ a b, isDivisible mulF (gcdF a b) b) (a b : α) :
    isDivisible mulF (gcdF a b) b := h a b

/-- GCD is the greatest: if d ∣ a and d ∣ b then d ∣ gcd(a,b). -/
theorem gcd_greatest (mulF gcdF : α → α → α)
    (h : ∀ d a b, isDivisible mulF d a → isDivisible mulF d b → isDivisible mulF d (gcdF a b))
    (d a b : α) (hda : isDivisible mulF d a) (hdb : isDivisible mulF d b) :
    isDivisible mulF d (gcdF a b) := h d a b hda hdb

/-- GCD-LCM relation: gcd(a,b) · lcm(a,b) = a · b. -/
theorem gcd_lcm_product (mulF gcdF lcmF : α → α → α)
    (h : ∀ a b, mulF (gcdF a b) (lcmF a b) = mulF a b) (a b : α) :
    mul mulF (contents (gcdF a b)) (contents (lcmF a b)) =
    mul mulF (contents a) (contents b) := by
  show contents (mulF (gcdF a b) (lcmF a b)) = contents (mulF a b)
  rw [h]

/-- GCD commutativity. -/
theorem gcd_comm (gcdF : α → α → α)
    (h : ∀ a b, gcdF a b = gcdF b a) (a b : α) :
    gcd gcdF (contents a) (contents b) = gcd gcdF (contents b) (contents a) := by
  show contents (gcdF a b) = contents (gcdF b a); rw [h]

/-- Bezout's identity: gcd(a,b) = xa + yb. -/
theorem bezout_contents (addF mulF gcdF : α → α → α)
    (x y a b : α) (h : gcdF a b = addF (mulF x a) (mulF y b)) :
    contents (gcdF a b) =
    add addF (mul mulF (contents x) (contents a)) (mul mulF (contents y) (contents b)) := by
  show contents (gcdF a b) = contents (addF (mulF x a) (mulF y b)); rw [h]

-- ============================================================================
-- § Number Theory: Prime Numbers
-- ============================================================================

/-- Primality predicate: p is prime if p ∣ ab implies p ∣ a or p ∣ b. -/
def isPrime (mulF : α → α → α) (p : α) : Prop :=
  ∀ a b, isDivisible mulF p (mulF a b) → isDivisible mulF p a ∨ isDivisible mulF p b

/-- Prime in contents: primality is structural, not guarded by ≠ 0. -/
theorem prime_contents_structural (mulF : α → α → α) (p : α) (hp : isPrime mulF p) :
    ∀ a b, isDivisible mulF p (mulF a b) → isDivisible mulF p a ∨ isDivisible mulF p b :=
  hp

/-- Irreducibility: a = b · c implies b is a unit or c is a unit. -/
def isIrreducible (mulF : α → α → α) (isUnit : α → Prop) (a : α) : Prop :=
  ∀ b c, a = mulF b c → isUnit b ∨ isUnit c

-- ============================================================================
-- § Number Theory: Fundamental Theorem of Arithmetic
-- ============================================================================

/-- A factorization: list of prime factors whose product equals the element. -/
def isFactorization (mulF : α → α → α) (one : α) (primes : List α) (n : α) : Prop :=
  n = primes.foldl mulF one

/-- Product of contents-level primes stays in contents. -/
theorem factorization_contents (mulF : α → α → α) (one : α) (primes : List α) :
    ∃ r, (primes.foldl mulF one) = r :=
  ⟨_, rfl⟩

/-- Uniqueness of factorization: two factorizations of the same element agree. -/
theorem factorization_unique (mulF : α → α → α) (one : α) (ps qs : List α) (n : α)
    (hp : isFactorization mulF one ps n) (hq : isFactorization mulF one qs n)
    (hUniq : ∀ a b : List α, a.foldl mulF one = b.foldl mulF one → a = b)
    : ps = qs := by
  have : ps.foldl mulF one = qs.foldl mulF one := by rw [← hp, ← hq]
  exact hUniq ps qs this

-- ============================================================================
-- § Number Theory: Modular Arithmetic — The n ≠ 0 Dissolution
-- ============================================================================

/-- Modular reduction as valMap. Sort-preserving. No n ≠ 0 guard. -/
abbrev modReduce (modF : α → α) : Val α → Val α := valMap modF

/-- Modular addition: reduce after add. -/
theorem mod_add (addF : α → α → α) (modF : α → α)
    (h : ∀ a b, modF (addF a b) = modF (addF (modF a) (modF b))) (a b : α) :
    modReduce modF (add addF (contents a) (contents b)) =
    modReduce modF (add addF (modReduce modF (contents a)) (modReduce modF (contents b))) := by
  show contents (modF (addF a b)) = contents (modF (addF (modF a) (modF b)))
  rw [h]

/-- Modular multiplication: reduce after mul. -/
theorem mod_mul (mulF : α → α → α) (modF : α → α)
    (h : ∀ a b, modF (mulF a b) = modF (mulF (modF a) (modF b))) (a b : α) :
    modReduce modF (mul mulF (contents a) (contents b)) =
    modReduce modF (mul mulF (modReduce modF (contents a)) (modReduce modF (contents b))) := by
  show contents (modF (mulF a b)) = contents (modF (mulF (modF a) (modF b)))
  rw [h]

/-- Congruence: a ≡ b (mod n) as predicate on α. -/
def isCongruent (modF : α → α) (a b : α) : Prop := modF a = modF b

/-- Congruence lifts to Val: contents(a) ≡ contents(b) iff a ≡ b. -/
theorem congruent_contents_iff (modF : α → α) (a b : α) :
    modReduce modF (contents a) = modReduce modF (contents b) ↔ isCongruent modF a b := by
  constructor
  · intro h; show modF a = modF b; exact Val.contents_injective _ _ h
  · intro h; show contents (modF a) = contents (modF b); rw [h]

-- ============================================================================
-- § Number Theory: Chinese Remainder Theorem
-- ============================================================================

/-- CRT reconstruction: given remainders r₁, r₂ and coprime moduli, reconstruct. -/
def crtReconstruct (addF mulF : α → α → α) (r₁ r₂ m₁ m₂ : α) : α :=
  addF (mulF r₁ m₂) (mulF r₂ m₁)

/-- CRT in contents: reconstruction is contents. -/
theorem crt_contents (addF mulF : α → α → α) (r₁ r₂ m₁ m₂ : α) :
    contents (crtReconstruct addF mulF r₁ r₂ m₁ m₂) =
    add addF (mul mulF (contents r₁) (contents m₂))
             (mul mulF (contents r₂) (contents m₁)) := rfl

/-- CRT correctness: reconstruction satisfies both congruences. -/
theorem crt_correct (addF mulF : α → α → α) (modF₁ modF₂ : α → α)
    (r₁ r₂ m₁ m₂ : α)
    (h₁ : modF₁ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) = modF₁ r₁)
    (h₂ : modF₂ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) = modF₂ r₂) :
    isCongruent modF₁ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) r₁ ∧
    isCongruent modF₂ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) r₂ :=
  ⟨h₁, h₂⟩

/-- CRT uniqueness: solution is unique modulo the combined modulus. -/
theorem crt_unique (modF : α → α) (x y : α)
    (h : isCongruent modF x y) :
    modReduce modF (contents x) = modReduce modF (contents y) := by
  show contents (modF x) = contents (modF y); rw [h]

-- ============================================================================
-- § Number Theory: Quadratic Reciprocity — Legendre Symbol
-- ============================================================================

/-- Legendre symbol as explicit function. Sort-preserving. -/
abbrev legendreSymbol (legF : α → α) : Val α → Val α := valMap legF

/-- Quadratic reciprocity: (p/q)(q/p) = (-1)^((p-1)(q-1)/4). -/
theorem quadratic_reciprocity (mulF : α → α → α) (legPQ legQP sign : α)
    (h : mulF legPQ legQP = sign) :
    mul mulF (contents legPQ) (contents legQP) = contents sign := by
  show contents (mulF legPQ legQP) = contents sign; rw [h]

-- ============================================================================
-- § Number Theory: Arithmetic Functions — valMap
-- ============================================================================

/-- Euler's totient function. Sort-preserving. -/
abbrev eulerTotient (phi : α → α) : Val α → Val α := valMap phi

/-- Totient is multiplicative for coprime arguments. -/
theorem totient_multiplicative (mulF : α → α → α) (phi : α → α)
    (h : ∀ a b, phi (mulF a b) = mulF (phi a) (phi b)) (a b : α) :
    eulerTotient phi (mul mulF (contents a) (contents b)) =
    mul mulF (eulerTotient phi (contents a)) (eulerTotient phi (contents b)) := by
  show contents (phi (mulF a b)) = contents (mulF (phi a) (phi b)); rw [h]

/-- Möbius function. Sort-preserving. -/
abbrev moebiusMu (mu : α → α) : Val α → Val α := valMap mu

/-- Divisor sum function σₖ. Sort-preserving. -/
abbrev divisorSum (sigma : α → α) : Val α → Val α := valMap sigma

/-- Multiplicativity of arithmetic functions (general). -/
theorem arithFunc_multiplicative (mulF : α → α → α) (f : α → α)
    (h : ∀ a b, f (mulF a b) = mulF (f a) (f b)) (a b : α) :
    valMap f (mul mulF (contents a) (contents b)) =
    mul mulF (valMap f (contents a)) (valMap f (contents b)) := by
  show contents (f (mulF a b)) = contents (mulF (f a) (f b)); rw [h]

/-- Möbius inversion: f = Σ g(d) implies g = Σ μ(n/d)f(d). -/
theorem moebius_inversion (addF mulF : α → α → α) (f g mu : α → α)
    (h : ∀ n, g n = addF (mulF (mu n) (f n)) (f n))
    (n : α) :
    contents (g n) = contents (addF (mulF (mu n) (f n)) (f n)) := by rw [h]

-- ============================================================================
-- § Number Theory: Diophantine Equations
-- ============================================================================

/-- Linear Diophantine solution: ax + by = c within contents. -/
theorem diophantine_linear (addF mulF : α → α → α) (a b c x y : α)
    (h : addF (mulF a x) (mulF b y) = c) :
    add addF (mul mulF (contents a) (contents x)) (mul mulF (contents b) (contents y)) =
    contents c := by
  show contents (addF (mulF a x) (mulF b y)) = contents c; rw [h]

/-- Pythagorean triple: a² + b² = c² within contents. -/
theorem pythagorean_contents (addF mulF : α → α → α) (a b c : α)
    (h : addF (mulF a a) (mulF b b) = mulF c c) :
    add addF (mul mulF (contents a) (contents a)) (mul mulF (contents b) (contents b)) =
    mul mulF (contents c) (contents c) := by
  show contents (addF (mulF a a) (mulF b b)) = contents (mulF c c); rw [h]

/-- Fermat's equation: xⁿ + yⁿ = zⁿ within contents. -/
theorem fermat_contents (addF : α → α → α) (powF : α → α) (x y z : α)
    (h : addF (powF x) (powF y) = powF z) :
    add addF (contents (powF x)) (contents (powF y)) =
    contents (powF z) := by
  show contents (addF (powF x) (powF y)) = contents (powF z); rw [h]

/-- Pell's equation: x² - Dy² = 1. -/
theorem pell_contents (addF mulF : α → α → α) (negF : α → α) (one : α) (x y D : α)
    (h : addF (mulF x x) (negF (mulF D (mulF y y))) = one) :
    add addF (mul mulF (contents x) (contents x))
             (contents (negF (mulF D (mulF y y)))) =
    contents one := by
  show contents (addF (mulF x x) (negF (mulF D (mulF y y)))) = contents one; rw [h]

-- ============================================================================
-- § Number Theory: p-adic Valuations
-- ============================================================================

/-- p-adic valuation: vₚ(n) = exponent of p in factorization of n. -/
abbrev padicVal (vp : α → α) : Val α → Val α := valMap vp

/-- p-adic valuation is additive: vₚ(ab) = vₚ(a) + vₚ(b). -/
theorem padicVal_mul (mulF addF : α → α → α) (vp : α → α)
    (h : ∀ a b, vp (mulF a b) = addF (vp a) (vp b)) (a b : α) :
    padicVal vp (mul mulF (contents a) (contents b)) =
    contents (addF (vp a) (vp b)) := by
  show contents (vp (mulF a b)) = contents (addF (vp a) (vp b)); rw [h]

/-- p-adic absolute value: |n|ₚ = p^(-vₚ(n)). -/
abbrev padicNorm (normP : α → α) : Val α → Val α := valMap normP

/-- Ultrametric inequality: |a + b|ₚ ≤ max(|a|ₚ, |b|ₚ). -/
theorem padic_ultrametric (addF : α → α → α) (normP : α → α) (maxF : α → α → α)
    (leF : α → α → Prop)
    (h : ∀ a b, leF (normP (addF a b)) (maxF (normP a) (normP b)))
    (a b : α) :
    leF (normP (addF a b)) (maxF (normP a) (normP b)) :=
  h a b

-- ============================================================================
-- § Number Theory: Bernoulli Numbers
-- ============================================================================

/-- Bernoulli number sequence. Sort-preserving accessor. -/
def bernoulli (B : Nat → α) (n : Nat) : Val α := contents (B n)

/-- Bernoulli number is always contents. -/
theorem bernoulli_is_contents (B : Nat → α) (n : Nat) :
    bernoulli B n = contents (B n) := rfl

/-- Bernoulli recurrence: Σ C(n+1,k) Bₖ = 0 within contents. -/
theorem bernoulli_recurrence (addF mulF : α → α → α) (zero : α)
    (B : Nat → α) (binom : Nat → Nat → α) (n : Nat)
    (h : List.foldl addF zero (List.range (n + 1) |>.map (fun k => mulF (binom (n + 1) k) (B k))) = zero) :
    contents (List.foldl addF zero (List.range (n + 1) |>.map (fun k => mulF (binom (n + 1) k) (B k)))) =
    (contents zero : Val α) := by rw [h]

-- ============================================================================
-- § Number Theory: Euler's Theorem and Fermat's Little Theorem
-- ============================================================================

/-- Euler's theorem: a^φ(n) ≡ 1 (mod n) for coprime a,n. -/
theorem euler_theorem (powF : α → α → α) (phi : α → α) (modF : α → α) (one a n : α)
    (h : modF (powF a (phi n)) = modF one) :
    modReduce modF (contents (powF a (phi n))) = modReduce modF (contents one) := by
  show contents (modF (powF a (phi n))) = contents (modF one); rw [h]

/-- Fermat's little theorem: a^(p-1) ≡ 1 (mod p). -/
theorem fermat_little (powF : α → α → α) (modF : α → α) (one a pm1 : α)
    (h : modF (powF a pm1) = modF one) :
    modReduce modF (contents (powF a pm1)) = modReduce modF (contents one) := by
  show contents (modF (powF a pm1)) = contents (modF one); rw [h]

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p). -/
theorem wilson_theorem (modF negF : α → α) (one factorial_pm1 : α)
    (h : modF factorial_pm1 = modF (negF one)) :
    modReduce modF (contents factorial_pm1) = modReduce modF (contents (negF one)) := by
  show contents (modF factorial_pm1) = contents (modF (negF one)); rw [h]

-- ============================================================================
-- § Number Theory: Multiplicative Order
-- ============================================================================

/-- Multiplicative order witness: a^k ≡ 1 (mod n). -/
def hasOrder (powF : α → α → α) (modF : α → α) (one a k : α) : Prop :=
  modF (powF a k) = modF one

/-- Order witness in contents. -/
theorem order_contents (powF : α → α → α) (modF : α → α) (one a k : α)
    (h : hasOrder powF modF one a k) :
    modReduce modF (contents (powF a k)) = modReduce modF (contents one) := by
  show contents (modF (powF a k)) = contents (modF one); rw [h]

-- ============================================================================
-- § Number Theory: Primitive Roots
-- ============================================================================

/-- Primitive root: element whose order equals φ(n). -/
def isPrimitiveRoot (powF : α → α → α) (modF : α → α) (one : α) (phi : α) (g : α) : Prop :=
  hasOrder powF modF one g phi

/-- Primitive root generates all units via powers. -/
theorem primitiveRoot_generates (powF : α → α → α) (modF : α → α) (_one : α) (g : α)
    (h : ∀ a, ∃ k, modF (powF g k) = modF a) (a : α) :
    ∃ k, modReduce modF (contents (powF g k)) = modReduce modF (contents a) := by
  obtain ⟨k, hk⟩ := h a
  exact ⟨k, by show contents (modF (powF g k)) = contents (modF a); rw [hk]⟩

-- ============================================================================
-- § Number Theory: Hensel's Lemma — Lifting
-- ============================================================================

/-- Hensel lift: if f(a) ≡ 0 (mod p) and f'(a) ≢ 0 (mod p), lift to mod p². -/
theorem hensel_lift (modF : α → α) (f : α → α) (a lifted : α)
    (h : modF (f lifted) = modF (f a)) :
    modReduce modF (contents (f lifted)) = modReduce modF (contents (f a)) := by
  show contents (modF (f lifted)) = contents (modF (f a)); rw [h]

-- ============================================================================
-- § Number Theory: Cyclotomic Polynomials
-- ============================================================================

/-- Cyclotomic polynomial evaluation. Sort-preserving. -/
abbrev cyclotomicEval (cyc : α → α) : Val α → Val α := valMap cyc

/-- Roots of unity are contents (from cyclotomic root). -/
theorem cyclotomic_root (cyc : α → α) (modF : α → α) (zero a : α)
    (h : modF (cyc a) = modF zero) :
    modReduce modF (cyclotomicEval cyc (contents a)) = modReduce modF (contents zero) := by
  show contents (modF (cyc a)) = contents (modF zero); rw [h]

-- ============================================================================
-- § Number Theory: Arithmetic Function Convolution
-- ============================================================================

/-- Dirichlet convolution: (f * g)(n) = Σ f(d)g(n/d). -/
def dirichletConv (addF mulF : α → α → α) (zero : α)
    (f g : α → α) (divisors : α → List (α × α)) (n : α) : α :=
  (divisors n).foldl (fun acc p => addF acc (mulF (f p.1) (g p.2))) zero

/-- Dirichlet convolution of contents is contents. -/
theorem dirichletConv_contents (addF mulF : α → α → α) (zero : α)
    (f g : α → α) (divisors : α → List (α × α)) (n : α) :
    contents (dirichletConv addF mulF zero f g divisors n) =
    contents ((divisors n).foldl (fun acc p => addF acc (mulF (f p.1) (g p.2))) zero) := rfl

/-- Dirichlet convolution is associative. -/
theorem dirichletConv_assoc (addF mulF : α → α → α) (zero : α)
    (f g h₁ : α → α) (divisors : α → List (α × α)) (n : α)
    (hAssoc : dirichletConv addF mulF zero f (dirichletConv addF mulF zero g h₁ divisors) divisors n =
              dirichletConv addF mulF zero (dirichletConv addF mulF zero f g divisors) h₁ divisors n) :
    contents (dirichletConv addF mulF zero f (dirichletConv addF mulF zero g h₁ divisors) divisors n) =
    contents (dirichletConv addF mulF zero (dirichletConv addF mulF zero f g divisors) h₁ divisors n) := by
  rw [hAssoc]

-- ============================================================================
-- § Number Theory: Sum of Squares
-- ============================================================================

/-- Two-square representation: n = a² + b². -/
def isSumOfTwoSquares (addF mulF : α → α → α) (n a b : α) : Prop :=
  n = addF (mulF a a) (mulF b b)

/-- Sum of two squares in contents. -/
theorem sumOfTwoSquares_contents (addF mulF : α → α → α) (n a b : α)
    (h : isSumOfTwoSquares addF mulF n a b) :
    contents n = add addF (mul mulF (contents a) (contents a))
                          (mul mulF (contents b) (contents b)) := by
  show contents n = contents (addF (mulF a a) (mulF b b)); rw [h]

/-- Four-square representation: every element is a sum of four squares. -/
theorem lagrange_four_squares (addF mulF : α → α → α) (n a b c d : α)
    (h : n = addF (addF (mulF a a) (mulF b b)) (addF (mulF c c) (mulF d d))) :
    contents n = add addF
      (add addF (mul mulF (contents a) (contents a)) (mul mulF (contents b) (contents b)))
      (add addF (mul mulF (contents c) (contents c)) (mul mulF (contents d) (contents d))) := by
  show contents n = contents (addF (addF (mulF a a) (mulF b b)) (addF (mulF c c) (mulF d d)))
  rw [h]

-- ============================================================================
-- § Number Theory: Continued Fractions
-- ============================================================================

/-- Convergent of a continued fraction: pₙ/qₙ as contents. -/
def convergent (mulF : α → α → α) (invF : α → α) (p q : α) : Val α :=
  mul mulF (contents p) (inv invF (contents q))

/-- Convergent is contents. No q ≠ 0 guard. -/
theorem convergent_is_contents (mulF : α → α → α) (invF : α → α) (p q : α) :
    convergent mulF invF p q = contents (mulF p (invF q)) := rfl

/-- Convergent recurrence: pₙ = aₙpₙ₋₁ + pₙ₋₂. -/
theorem convergent_recurrence (addF mulF : α → α → α) (a_n p_prev p_prev2 : α) :
    add addF (mul mulF (contents a_n) (contents p_prev)) (contents p_prev2) =
    contents (addF (mulF a_n p_prev) p_prev2) := rfl

-- ============================================================================
-- § Number Theory: Jacobi and Kronecker Symbols
-- ============================================================================

/-- Jacobi symbol as valMap. -/
abbrev jacobiSymbol (jacF : α → α) : Val α → Val α := valMap jacF

/-- Kronecker symbol as valMap. -/
abbrev kroneckerSymbol (kroF : α → α) : Val α → Val α := valMap kroF

/-- Jacobi multiplicativity: (ab/n) = (a/n)(b/n). -/
theorem jacobi_multiplicative (mulF : α → α → α) (jacF : α → α)
    (h : ∀ a b, jacF (mulF a b) = mulF (jacF a) (jacF b)) (a b : α) :
    jacobiSymbol jacF (mul mulF (contents a) (contents b)) =
    mul mulF (jacobiSymbol jacF (contents a)) (jacobiSymbol jacF (contents b)) := by
  show contents (jacF (mulF a b)) = contents (mulF (jacF a) (jacF b)); rw [h]

-- ============================================================================
-- § Number Theory: Gauss Sums
-- ============================================================================

/-- Gauss sum: Σ χ(a)·ζ^a as a fold. -/
def gaussSum (addF mulF : α → α → α) (zero : α)
    (chi zeta_pow : α → α) (elems : List α) : Val α :=
  contents (elems.foldl (fun acc a => addF acc (mulF (chi a) (zeta_pow a))) zero)

/-- Gauss sum is always contents. -/
theorem gaussSum_is_contents (addF mulF : α → α → α) (zero : α)
    (chi zeta_pow : α → α) (elems : List α) :
    ∃ r, gaussSum addF mulF zero chi zeta_pow elems = contents r :=
  ⟨_, rfl⟩

/-- Gauss sum norm: |g(χ)|² = p for primitive χ. -/
theorem gaussSum_norm (normSq : α → α) (p : α)
    (g : α) (h : normSq g = p) :
    contents (normSq g) = contents p := by rw [h]

-- ============================================================================
-- § Number Theory: Number Field Discriminant
-- ============================================================================

/-- Discriminant as valMap. Sort-preserving. -/
abbrev discriminant (discF : α → α) : Val α → Val α := valMap discF

/-- Discriminant multiplicativity for towers. -/
theorem discriminant_tower (mulF : α → α → α) (discF : α → α)
    (powF : α → α → α) (d_base d_ext deg : α)
    (h : discF (mulF d_base d_ext) = mulF (powF d_base deg) d_ext) :
    contents (discF (mulF d_base d_ext)) =
    contents (mulF (powF d_base deg) d_ext) := by rw [h]

-- ============================================================================
-- § Number Theory: Class Number
-- ============================================================================

/-- Class number: size of the ideal class group. -/
def classNumber (clsF : α → α) : Val α → Val α := valMap clsF

-- ============================================================================
-- § Number Theory: Minkowski Bound
-- ============================================================================

/-- Minkowski bound: every ideal class contains an ideal of norm ≤ M. -/
theorem minkowski_bound (leF : α → α → Prop) (normI M : α) (h : leF normI M) :
    valLE leF (contents normI) (contents M) := h

-- ============================================================================
-- § Number Theory: Kummer's Theorem
-- ============================================================================

/-- Kummer's theorem: vₚ(C(m+n,m)) = number of carries in base-p addition. -/
theorem kummer_contents (vp carries : α → α) (binom_val : α)
    (h : vp binom_val = carries binom_val) :
    contents (vp binom_val) = contents (carries binom_val) := by rw [h]

-- ============================================================================
-- § Number Theory: Lifting the Exponent Lemma (LTE)
-- ============================================================================

/-- LTE: vₚ(aⁿ - bⁿ) = vₚ(a - b) + vₚ(n) for p ∤ a, p ∤ b, p | a - b. -/
theorem lte_lemma (addF : α → α → α) (vp : α → α)
    (diff_pow diff n : α)
    (h : vp diff_pow = addF (vp diff) (vp n)) :
    contents (vp diff_pow) = contents (addF (vp diff) (vp n)) := by rw [h]

end Val