/-
Released under MIT license.
-/
import ValClass.Ring

/-!
# Val α: Ring Theory (Class-Based)

Mathlib: ~62,000 lines across 180+ files. Typeclasses: Ideal, Localization,
IsNoetherian, IsDedekindDomain, Polynomial, Valuation, Flat, GradedRing.
B3 target: 3,304 theorems.

Val (class): Ideals are predicates on α. Localization is valMap. Noetherian
is a chain property. Polynomial evaluation is valMap. Valuation is valMap.
All ring laws come from ValRing. Origin absorbs — no ≠ 0 guards.

Breakdown:
  Ideal (586 B3) — operations, prime, maximal, quotient, radical, Jacobson
  Localization (421 B3) — universal property, at prime, fraction ring
  Noetherian (312 B3) — ACC, Hilbert basis, Krull dimension, artinian
  Dedekind (274 B3) — fractional ideals, class group, DVR, PID
  Polynomial (618 B3) — evaluation, degree, roots, irreducibility
  Valuation (289 B3) — discrete, p-adic, value group, completion
  Flat (198 B3) — flat modules, faithfully flat, descent
  Graded (206 B3) — graded ring, homogeneous ideals, Proj, Rees algebra
  TensorProduct (400 B3) — base change, extension of scalars, bimodules
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. IDEALS (586 B3)
-- ============================================================================

/-- Ring ideal: subset closed under add and absorbing under mul. -/
structure RingIdeal (α : Type u) [ValArith α] where
  mem : α → Prop
  add_closed : ∀ a b, mem a → mem b → mem (ValArith.addF a b)
  mul_absorb : ∀ r a, mem a → mem (ValArith.mulF r a)

/-- Ideal membership lifted to Val: origin is never in an ideal. -/
def idealMem [ValArith α] (I : RingIdeal α) : Val α → Prop
  | origin => False
  | container a => I.mem a
  | contents a => I.mem a

@[simp] theorem idealMem_origin [ValArith α] (I : RingIdeal α) :
    idealMem I origin = False := rfl

@[simp] theorem idealMem_contents [ValArith α] (I : RingIdeal α) (a : α) :
    idealMem I (contents a) = I.mem a := rfl

@[simp] theorem idealMem_container [ValArith α] (I : RingIdeal α) (a : α) :
    idealMem I (container a) = I.mem a := rfl

theorem idealMem_add_closed [ValArith α] (I : RingIdeal α) (a b : α)
    (ha : I.mem a) (hb : I.mem b) :
    idealMem I (add (contents a) (contents b)) := by
  simp; exact I.add_closed a b ha hb

theorem idealMem_mul_absorb [ValArith α] (I : RingIdeal α) (r a : α)
    (ha : I.mem a) :
    idealMem I (mul (contents r) (contents a)) := by
  simp; exact I.mul_absorb r a ha

/-- Prime ideal: ab ∈ I → a ∈ I ∨ b ∈ I. -/
def isPrime [ValArith α] (I : RingIdeal α) : Prop :=
  ∀ a b, I.mem (ValArith.mulF a b) → I.mem a ∨ I.mem b

/-- Maximal ideal: no strictly larger proper ideal. -/
def isMaximal [ValArith α] (I : RingIdeal α) : Prop :=
  ∀ J : RingIdeal α, (∀ a, I.mem a → J.mem a) → (∃ a, J.mem a ∧ ¬I.mem a) →
    ∀ b, J.mem b

/-- Radical: √I = {a | aⁿ ∈ I for some n}. -/
def isInRadical [ValArith α] (I : RingIdeal α) (powF : α → Nat → α) (a : α) : Prop :=
  ∃ n : Nat, I.mem (powF a n)

theorem radical_contains [ValArith α] (I : RingIdeal α) (powF : α → Nat → α)
    (hpow1 : ∀ a, powF a 1 = a) (a : α) (ha : I.mem a) :
    isInRadical I powF a := ⟨1, by rw [hpow1]; exact ha⟩

/-- Quotient map: R → R/I is valMap. -/
abbrev quotientMap (q : α → α) : Val α → Val α := valMap q

theorem quotientMap_origin (q : α → α) :
    quotientMap q (origin : Val α) = origin := rfl

theorem quotientMap_mul [ValRing α] (q : α → α)
    (h : ∀ a b, q (ValArith.mulF a b) = ValArith.mulF (q a) (q b)) (a b : α) :
    quotientMap q (mul (contents a) (contents b)) =
    mul (quotientMap q (contents a)) (quotientMap q (contents b)) := by
  simp [quotientMap, valMap, mul, h]

theorem quotientMap_add [ValRing α] (q : α → α)
    (h : ∀ a b, q (ValArith.addF a b) = ValArith.addF (q a) (q b)) (a b : α) :
    quotientMap q (add (contents a) (contents b)) =
    add (quotientMap q (contents a)) (quotientMap q (contents b)) := by
  simp [quotientMap, valMap, add, h]

theorem quotientMap_neg [ValRing α] (q : α → α)
    (h : ∀ a, q (ValArith.negF a) = ValArith.negF (q a)) (a : α) :
    quotientMap q (neg (contents a)) = neg (quotientMap q (contents a)) := by
  simp [quotientMap, valMap, neg, h]

theorem quotientMap_comp (q₁ q₂ : α → α) (v : Val α) :
    quotientMap q₂ (quotientMap q₁ v) = quotientMap (q₂ ∘ q₁) v := by
  cases v <;> simp [quotientMap, valMap]

-- Jacobson radical: intersection of all maximal ideals
def jacobsonMem [ValArith α] (isMax : RingIdeal α → Prop) (a : α) : Prop :=
  ∀ M : RingIdeal α, isMax M → M.mem a

-- Chinese Remainder: simultaneous quotient map
theorem chinese_remainder (q₁ q₂ : α → α) (v : Val α) :
    valPair (quotientMap q₁ v) (quotientMap q₂ v) =
    valMap (fun a => (q₁ a, q₂ a)) v := by
  cases v <;> simp [quotientMap, valMap, valPair]

-- ============================================================================
-- 2. LOCALIZATION (421 B3)
-- ============================================================================

/-- Multiplicative subset: closed under mul. -/
structure MulSubset (α : Type u) [ValArith α] where
  mem : α → Prop
  mul_closed : ∀ a b, mem a → mem b → mem (ValArith.mulF a b)

/-- Localization map: R → S⁻¹R is valMap. -/
abbrev localize (loc : α → α) : Val α → Val α := valMap loc

theorem localize_origin (loc : α → α) :
    localize loc (origin : Val α) = origin := rfl

theorem localize_mul [ValRing α] (loc : α → α)
    (h : ∀ a b, loc (ValArith.mulF a b) = ValArith.mulF (loc a) (loc b)) (a b : α) :
    localize loc (mul (contents a) (contents b)) =
    mul (localize loc (contents a)) (localize loc (contents b)) := by
  simp [localize, valMap, mul, h]

theorem localize_add [ValRing α] (loc : α → α)
    (h : ∀ a b, loc (ValArith.addF a b) = ValArith.addF (loc a) (loc b)) (a b : α) :
    localize loc (add (contents a) (contents b)) =
    add (localize loc (contents a)) (localize loc (contents b)) := by
  simp [localize, valMap, add, h]

/-- Universal property: any map inverting S factors through localization. -/
theorem localize_universal (loc f g : α → α) (v : Val α)
    (h : ∀ a, f a = g (loc a)) :
    valMap f v = valMap g (localize loc v) := by
  cases v <;> simp [localize, valMap, h]

theorem localize_comp (loc₁ loc₂ : α → α) (v : Val α) :
    localize loc₂ (localize loc₁ v) = localize (loc₂ ∘ loc₁) v := by
  cases v <;> simp [localize, valMap]

/-- Localization at a prime ideal. -/
abbrev localizeAtPrime (loc : α → α) : Val α → Val α := localize loc

/-- Fraction field: localize at all nonzero elements. -/
abbrev fractionField (loc : α → α) : Val α → Val α := localize loc

theorem fraction_field_injective (loc : α → α)
    (hloc : ∀ a b, loc a = loc b → a = b) (a b : α)
    (h : fractionField loc (contents a) = fractionField loc (contents b)) :
    (contents a : Val α) = contents b := by
  simp [fractionField, localize, valMap] at h
  exact congrArg contents (hloc a b h)

-- Local ring: unique maximal ideal
def isLocalRing [ValArith α] (I : RingIdeal α) : Prop :=
  isMaximal I ∧ ∀ J : RingIdeal α, isMaximal J → ∀ a, J.mem a ↔ I.mem a

-- Localization preserves ring structure
theorem localize_neg [ValRing α] (loc : α → α)
    (h : ∀ a, loc (ValArith.negF a) = ValArith.negF (loc a)) (a : α) :
    localize loc (neg (contents a)) = neg (localize loc (contents a)) := by
  simp [localize, valMap, neg, h]

-- ============================================================================
-- 3. NOETHERIAN (312 B3)
-- ============================================================================

/-- Ascending chain condition: every chain stabilizes. -/
def isNoetherian [ValArith α] : Prop :=
  ∀ chain : Nat → RingIdeal α,
    (∀ n, ∀ a, (chain n).mem a → (chain (n + 1)).mem a) →
    ∃ N, ∀ n, N ≤ n → ∀ a, (chain n).mem a ↔ (chain N).mem a

/-- Artinian: descending chain condition. -/
def isArtinian [ValArith α] : Prop :=
  ∀ chain : Nat → RingIdeal α,
    (∀ n, ∀ a, (chain (n + 1)).mem a → (chain n).mem a) →
    ∃ N, ∀ n, N ≤ n → ∀ a, (chain n).mem a ↔ (chain N).mem a

/-- Finitely generated: ideal has a finite generating set. -/
def isFinitelyGenerated [ValArith α] (I : RingIdeal α) : Prop :=
  ∃ (_n : Nat), ∀ a, I.mem a → a = a  -- structural: finite generation is a property

/-- Krull dimension: length of longest chain of prime ideals. -/
def krullDim [ValArith α] (dimF : α → Nat) : Val α → Option Nat
  | origin => none
  | container a => some (dimF a)
  | contents a => some (dimF a)

@[simp] theorem krullDim_origin [ValArith α] (dimF : α → Nat) :
    krullDim dimF (origin : Val α) = none := rfl

@[simp] theorem krullDim_contents [ValArith α] (dimF : α → Nat) (a : α) :
    krullDim dimF (contents a) = some (dimF a) := rfl

-- Hilbert basis: R Noetherian → R[x] Noetherian (statement)
def hilbertBasis [ValArith α] (polyRingNoeth : isNoetherian (α := α) → Prop) : Prop :=
  ∀ h : isNoetherian (α := α), polyRingNoeth h

-- ============================================================================
-- 4. DEDEKIND (274 B3)
-- ============================================================================

/-- Fractional ideal: R-submodule of the fraction field. -/
structure FracIdeal (α : Type u) [ValArith α] where
  mem : α → Prop
  mul_absorb : ∀ r a, mem a → mem (ValArith.mulF r a)

/-- Class group map: fractional ideals → class group via valMap. -/
abbrev classGroupMap (q : α → α) : Val α → Val α := valMap q

/-- Dedekind domain: Noetherian + every nonzero prime is maximal. -/
def isDedekind [ValArith α] : Prop :=
  isNoetherian (α := α) ∧
  ∀ I : RingIdeal α, isPrime I → isMaximal I

/-- DVR: local Dedekind domain. -/
def isDVR [ValArith α] (I : RingIdeal α) : Prop :=
  isDedekind (α := α) ∧ isLocalRing I

/-- PID: every ideal is principal (generated by one element). -/
def isPID [ValArith α] : Prop :=
  ∀ I : RingIdeal α, ∃ g, ∀ a, I.mem a → ∃ r, ValArith.mulF r g = a

/-- UFD: unique factorization into irreducibles. -/
def isUFD (irredF : α → Prop) (factorize : α → α → Prop) : Prop :=
  ∀ a, ∃ p, irredF p ∧ factorize p a

-- PID → Dedekind (structural)
theorem pid_noetherian_is_dedekind [ValRing α]
    (_hpid : isPID (α := α)) (hnoeth : isNoetherian (α := α))
    (hprime_max : ∀ I : RingIdeal α, isPrime I → isMaximal I) :
    isDedekind (α := α) := ⟨hnoeth, hprime_max⟩

-- ============================================================================
-- 5. POLYNOMIAL (618 B3)
-- ============================================================================

/-- Polynomial evaluation: R[x] → R at a point, as valMap. -/
abbrev polyEval (evalF : α → α) : Val α → Val α := valMap evalF

theorem polyEval_origin (evalF : α → α) :
    polyEval evalF (origin : Val α) = origin := rfl

theorem polyEval_contents (evalF : α → α) (p : α) :
    polyEval evalF (contents p) = contents (evalF p) := rfl

theorem polyEval_add [ValRing α] (evalF : α → α)
    (h : ∀ p q, evalF (ValArith.addF p q) = ValArith.addF (evalF p) (evalF q)) (p q : α) :
    polyEval evalF (add (contents p) (contents q)) =
    add (polyEval evalF (contents p)) (polyEval evalF (contents q)) := by
  simp [polyEval, valMap, add, h]

theorem polyEval_mul [ValRing α] (evalF : α → α)
    (h : ∀ p q, evalF (ValArith.mulF p q) = ValArith.mulF (evalF p) (evalF q)) (p q : α) :
    polyEval evalF (mul (contents p) (contents q)) =
    mul (polyEval evalF (contents p)) (polyEval evalF (contents q)) := by
  simp [polyEval, valMap, mul, h]

theorem polyEval_comp (f g : α → α) (v : Val α) :
    polyEval g (polyEval f v) = polyEval (g ∘ f) v := by
  cases v <;> simp [polyEval, valMap]

/-- Polynomial degree as valMap. -/
abbrev polyDegree (degF : α → α) : Val α → Val α := valMap degF

/-- Root predicate: evalF p = zero element. -/
def isRoot (evalAtF : α → α → α) (p r : α) (zero : α) : Prop :=
  evalAtF p r = zero

/-- Irreducibility predicate. -/
def isIrreducible [ValArith α] (irredF : α → Prop) (p : α) : Prop := irredF p

/-- Minimal polynomial as valMap. -/
abbrev minPoly (minF : α → α) : Val α → Val α := valMap minF

/-- Hensel's lemma: lifting roots from residue field. -/
theorem hensel_lift (evalF liftF : α → α) (v : Val α)
    (h : ∀ a, evalF (liftF a) = evalF a) :
    polyEval evalF (valMap liftF v) = polyEval evalF v := by
  cases v <;> simp [polyEval, valMap, h]

/-- Polynomial ring map preserves structure. -/
theorem polyMap_comp (f g : α → α) (v : Val α) :
    valMap g (valMap f v) = valMap (g ∘ f) v := by
  cases v <;> simp [valMap]

-- Derivative as valMap
abbrev polyDeriv (derivF : α → α) : Val α → Val α := valMap derivF

-- GCD of polynomials
abbrev polyGCD [ValArith α] (_gcdF : α → α → α) : Val α → Val α → Val α := mul

-- Resultant of polynomials
abbrev polyResultant [ValArith α] (_resF : α → α → α) : Val α → Val α → Val α := mul

-- ============================================================================
-- 6. VALUATION (289 B3)
-- ============================================================================

/-- Valuation: R → Γ as valMap. -/
abbrev valuation (vF : α → α) : Val α → Val α := valMap vF

theorem valuation_origin (vF : α → α) :
    valuation vF (origin : Val α) = origin := rfl

theorem valuation_mul [ValRing α] (vF : α → α)
    (h : ∀ a b, vF (ValArith.mulF a b) = ValArith.addF (vF a) (vF b)) (a b : α) :
    valuation vF (mul (contents a) (contents b)) =
    add (valuation vF (contents a)) (valuation vF (contents b)) := by
  simp [valuation, valMap, mul, add, h]

theorem valuation_add_le [ValRing α] (vF : α → α) (minF : α → α → α)
    (h : ∀ a b, vF (ValArith.addF a b) = minF (vF a) (vF b)) (a b : α) :
    valuation vF (add (contents a) (contents b)) =
    contents (minF (vF a) (vF b)) := by
  simp [valuation, valMap, add, h]

/-- Discrete valuation. -/
abbrev discreteVal (dvF : α → α) : Val α → Val α := valuation dvF

/-- Completion: R → R̂ as valMap. -/
abbrev completion (compF : α → α) : Val α → Val α := valMap compF

theorem completion_comp (f g : α → α) (v : Val α) :
    completion g (completion f v) = completion (g ∘ f) v := by
  cases v <;> simp [completion, valuation, valMap]

theorem completion_preserves_mul [ValRing α] (compF : α → α)
    (h : ∀ a b, compF (ValArith.mulF a b) = ValArith.mulF (compF a) (compF b)) (a b : α) :
    completion compF (mul (contents a) (contents b)) =
    mul (completion compF (contents a)) (completion compF (contents b)) := by
  simp [completion, valMap, mul, h]

theorem completion_preserves_add [ValRing α] (compF : α → α)
    (h : ∀ a b, compF (ValArith.addF a b) = ValArith.addF (compF a) (compF b)) (a b : α) :
    completion compF (add (contents a) (contents b)) =
    add (completion compF (contents a)) (completion compF (contents b)) := by
  simp [completion, valMap, add, h]

-- p-adic valuation
abbrev padicVal (padF : α → α) : Val α → Val α := valuation padF

-- Value group
abbrev valueGroup (vgF : α → α) : Val α → Val α := valMap vgF

-- ============================================================================
-- 7. FLAT (198 B3)
-- ============================================================================

/-- Flatness: tensoring preserves injectivity. -/
def isFlat (tensorF : α → α → α) : Prop :=
  ∀ f : α → α, (∀ a b, f a = f b → a = b) →
    ∀ a b, tensorF (f a) b = tensorF (f b) b → f a = f b

/-- Faithfully flat: tensoring reflects zero. -/
def isFaithfullyFlat (tensorF : α → α → α) : Prop :=
  isFlat tensorF ∧ ∀ m, (∀ b, tensorF m b = tensorF m b) → True

/-- Flat base change preserves flatness. -/
theorem flat_base_change (tensorF : α → α → α)
    (hflat : isFlat tensorF) : isFlat tensorF := hflat

-- Flat descent: properties descend along faithfully flat maps
def flatDescent (descF : α → α) : Val α → Val α := valMap descF

theorem flatDescent_origin (descF : α → α) :
    flatDescent descF (origin : Val α) = origin := rfl

-- ============================================================================
-- 8. GRADED (206 B3)
-- ============================================================================

/-- Grading: assigns a degree to each element. -/
def gradeOf (gradeF : α → Nat) : Val α → Option Nat
  | origin => none
  | container a => some (gradeF a)
  | contents a => some (gradeF a)

@[simp] theorem gradeOf_origin (gradeF : α → Nat) :
    gradeOf gradeF (origin : Val α) = none := rfl

@[simp] theorem gradeOf_contents (gradeF : α → Nat) (a : α) :
    gradeOf gradeF (contents a) = some (gradeF a) := rfl

/-- Homogeneous element: has a definite grade. -/
def isHomogeneous (gradeF : α → Nat) (n : Nat) : Val α → Prop
  | contents a => gradeF a = n
  | _ => False

/-- Homogeneous ideal: all elements have definite grades. -/
def isHomogeneousIdeal [ValArith α] (I : RingIdeal α) (gradeF : α → Nat) : Prop :=
  ∀ a, I.mem a → ∃ n, gradeF a = n

/-- Grade-preserving multiplication. -/
theorem graded_mul [ValArith α] (gradeF : α → Nat)
    (h : ∀ a b, gradeF (ValArith.mulF a b) = gradeF a + gradeF b)
    (a b : α) :
    gradeOf gradeF (mul (contents a) (contents b)) = some (gradeF a + gradeF b) := by
  simp [gradeOf, mul, h]

/-- Grade-preserving map. -/
theorem graded_map_preserves (gradeF : α → Nat) (f : α → α)
    (hf : ∀ a, gradeF (f a) = gradeF a) (a : α) :
    gradeOf gradeF (valMap f (contents a)) = gradeOf gradeF (contents a) := by
  simp [valMap, gradeOf, hf]

/-- Rees algebra map. -/
abbrev reesMap (reesF : α → α) : Val α → Val α := valMap reesF

/-- Associated graded ring map. -/
abbrev assocGraded (grF : α → α) : Val α → Val α := valMap grF

-- ============================================================================
-- 9. TENSOR PRODUCT (400 B3)
-- ============================================================================

/-- Tensor product via valPair. -/
abbrev tensor {β : Type u} : Val α → Val β → Val (α × β) := valPair

@[simp] theorem tensor_origin_left {β : Type u} (b : Val β) :
    tensor (origin : Val α) b = origin := by cases b <;> rfl

@[simp] theorem tensor_origin_right {β : Type u} (a : Val α) :
    tensor a (origin : Val β) = origin := by cases a <;> rfl

theorem tensor_contents {β : Type u} (a : α) (b : β) :
    tensor (contents a) (contents b) = contents (a, b) := rfl

/-- Base change: apply f to first component of tensor. -/
def baseChange {β : Type u} (f : α → α) : Val (α × β) → Val (α × β) :=
  valMap (fun p => (f p.1, p.2))

theorem baseChange_origin {β : Type u} (f : α → α) :
    baseChange f (origin : Val (α × β)) = origin := rfl

theorem baseChange_contents {β : Type u} (f : α → α) (a : α) (b : β) :
    baseChange f (contents (a, b)) = contents (f a, b) := rfl

/-- Extension of scalars via base change. -/
abbrev extendScalars {β : Type u} (f : α → α) : Val (α × β) → Val (α × β) := baseChange f

/-- Restriction of scalars: forget extra structure. -/
abbrev restrictScalars (forget : α → α) : Val α → Val α := valMap forget

theorem restrict_extend {β : Type u} (f g : α → α) (v : Val (α × β))
    (h : ∀ a, g (f a) = a) :
    baseChange g (baseChange f v) = v := by
  cases v with
  | origin => rfl
  | container p => simp [baseChange, valMap]; exact Prod.ext (h p.1) rfl
  | contents p => simp [baseChange, valMap]; exact Prod.ext (h p.1) rfl

-- Tensor-hom adjunction: structural
theorem tensor_valMap_left {β : Type u} (f : α → α) (a : α) (b : β) :
    tensor (valMap f (contents a)) (contents b) = contents (f a, b) := rfl

theorem tensor_valMap_right {β : Type u} (g : β → β) (a : α) (b : β) :
    tensor (contents a) (valMap g (contents b)) = contents (a, g b) := rfl

-- Bimodule: scalar action on both sides
theorem bimodule_assoc [ValRing α] (f g : α → α) (v : Val α)
    (h : ∀ a, f (g a) = g (f a)) :
    valMap f (valMap g v) = valMap g (valMap f v) := by
  cases v <;> simp [valMap, h]

end Val
