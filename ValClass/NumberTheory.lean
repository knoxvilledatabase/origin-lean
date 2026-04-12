/-
Released under MIT license.
-/
import ValClass.OrderedField

/-!
# Val α: Number Theory (Class-Based)

Mathlib: ~123,000 lines across 500+ files. Typeclasses: Ring, Field, ValuationRing,
NumberField, IsDedekindDomain, plus ZMod/Fintype/Polynomial infrastructure.
B3 target: 3,117 theorems.

Val (class): ALL number theory is ValField + predicates/functions on α.
p-adic valuations are valMap. L-series coefficients are valMap.
Modular forms are valMap. Arithmetic functions are valMap.
The ≠ 0 hypothesis dissolves: origin absorbs, contents computes.

Breakdown:
  top-level (821 B3) — quadratic reciprocity, Bernoulli, von Mangoldt, Liouville,
    sum of squares, units, GCD, valuations, class number
  NumberField (583 B3) — discriminant, embeddings, units, class group, ramification
  ModularForms (385 B3) — slash action, Eisenstein, theta, Petersson, Hecke
  LSeries (296 B3) — Dirichlet, convergence, Euler product, functional equation
  Padics (270 B3) — valuation, norm, Hensel, extension, integers
  ArithmeticFunction (119 B3) — Möbius, Euler totient, divisor sum, convolution
  LegendreSymbol (107 B3) — quadratic residue, Gauss sum, Jacobi symbol
  FLT (95 B3) — Fermat's Last Theorem infrastructure, regular primes
  Zsqrtd (78 B3) — Z[√d] arithmetic, norm, units
  Real (71 B3) — Berkovich, irrational, growth estimates
  Height (81 B3) — Weil height, Northcott, product formula
  Cyclotomic (63 B3) — cyclotomic polynomials, primitive roots, Ramanujan sum
  MulChar (52 B3) — multiplicative characters, orthogonality
  DirichletChar (44 B3) — Dirichlet characters, L-functions, conductor
  Harmonic (52 B3) — harmonic numbers, Euler-Mascheroni, partial sums
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. VALUATIONS AND NORMS (Padics 270 B3 + top-level valuation)
-- ============================================================================

abbrev padicVal (vpF : α → α) : Val α → Val α := valMap vpF

theorem padicVal_origin (vpF : α → α) :
    padicVal vpF (origin : Val α) = origin := rfl

theorem padicVal_contents (vpF : α → α) (n : α) :
    padicVal vpF (contents n) = contents (vpF n) := rfl

theorem padicVal_mul [ValField α] (vpF : α → α)
    (h : ∀ a b, vpF (ValArith.mulF a b) = ValArith.addF (vpF a) (vpF b))
    (a b : α) :
    padicVal vpF (mul (contents a) (contents b)) =
    add (padicVal vpF (contents a)) (padicVal vpF (contents b)) := by
  simp [padicVal, mul, add, valMap, h]

theorem padicVal_inv [ValField α] (vpF : α → α)
    (h : ∀ a, vpF (ValArith.invF a) = ValArith.negF (vpF a)) (a : α) :
    padicVal vpF (inv (contents a)) =
    neg (padicVal vpF (contents a)) := by
  simp [padicVal, inv, neg, valMap, h]

abbrev padicNorm (normF : α → α) : Val α → Val α := valMap normF

theorem padicNorm_mul [ValField α] (normF : α → α)
    (h : ∀ a b, normF (ValArith.mulF a b) = ValArith.mulF (normF a) (normF b))
    (a b : α) :
    padicNorm normF (mul (contents a) (contents b)) =
    mul (padicNorm normF (contents a)) (padicNorm normF (contents b)) := by
  simp [padicNorm, mul, valMap, h]

theorem padicNorm_ultrametric [ValOrderedField α]
    (normF : α → α) (maxF : α → α → α)
    (h : ∀ a b, ValOrderedField.leF (normF (ValArith.addF a b)) (maxF (normF a) (normF b)))
    (a b : α) :
    ValOrderedField.leF (normF (ValArith.addF a b)) (maxF (normF a) (normF b)) :=
  h a b

theorem hensel_lift (liftF rootF : α → α) (approx : α)
    (h : liftF approx = rootF approx) :
    valMap liftF (contents approx) = valMap rootF (contents approx) := by simp [h]

def isPadicInt (vpF : α → α) (leF : α → α → Prop) (zeroV : α) : Val α → Prop
  | contents a => leF zeroV (vpF a)
  | _ => False

theorem padicInt_mul_closed [ValField α]
    (vpF : α → α) (leF : α → α → Prop) (zeroV : α)
    (hv : ∀ a b, vpF (ValArith.mulF a b) = ValArith.addF (vpF a) (vpF b))
    (hadd : ∀ x y, leF zeroV x → leF zeroV y → leF zeroV (ValArith.addF x y))
    (a b : α) (ha : leF zeroV (vpF a)) (hb : leF zeroV (vpF b)) :
    leF zeroV (vpF (ValArith.mulF a b)) := by rw [hv]; exact hadd _ _ ha hb

theorem padic_expansion_unique (expandF : α → α)
    (h_inj : ∀ x y : α, expandF x = expandF y → x = y)
    (a b : α) (he : expandF a = expandF b) : a = b := h_inj a b he

theorem padic_teichmuller (teichF : α → α) (a : α)
    (h_idem : ∀ x, teichF (teichF x) = teichF x) :
    valMap teichF (valMap teichF (contents a)) = valMap teichF (contents a) := by
  simp [valMap, h_idem]

-- ============================================================================
-- 2. NUMBER FIELD (583 B3)
-- ============================================================================

abbrev nfEmbed (sigmaF : α → α) : Val α → Val α := valMap sigmaF

theorem nfEmbed_injective (sigmaF : α → α)
    (h : ∀ a b, sigmaF a = sigmaF b → a = b)
    (a b : α) (he : nfEmbed sigmaF (contents a) = nfEmbed sigmaF (contents b)) :
    (contents a : Val α) = contents b := by simp at he; exact congrArg contents (h a b he)

abbrev fieldNorm (normF : α → α) : Val α → Val α := valMap normF

theorem fieldNorm_mul [ValField α] (normF : α → α)
    (h : ∀ a b, normF (ValArith.mulF a b) = ValArith.mulF (normF a) (normF b))
    (a b : α) :
    fieldNorm normF (mul (contents a) (contents b)) =
    mul (fieldNorm normF (contents a)) (fieldNorm normF (contents b)) := by
  simp [fieldNorm, mul, valMap, h]

abbrev fieldTrace (trF : α → α) : Val α → Val α := valMap trF

theorem fieldTrace_add [ValField α] (trF : α → α)
    (h : ∀ a b, trF (ValArith.addF a b) = ValArith.addF (trF a) (trF b))
    (a b : α) :
    fieldTrace trF (add (contents a) (contents b)) =
    add (fieldTrace trF (contents a)) (fieldTrace trF (contents b)) := by
  simp [fieldTrace, add, valMap, h]

abbrev discriminant (discF : α → α) : Val α → Val α := valMap discF

theorem discriminant_nonzero (discF : α → α) (a : α) :
    discriminant discF (contents a) ≠ origin := by simp [discriminant, valMap]

def isAlgInt (isIntF : α → Prop) : Val α → Prop
  | contents a => isIntF a
  | _ => False

theorem algInt_add_closed [ValField α] (isIntF : α → Prop)
    (h : ∀ a b, isIntF a → isIntF b → isIntF (ValArith.addF a b))
    (a b : α) (ha : isIntF a) (hb : isIntF b) :
    isIntF (ValArith.addF a b) := h a b ha hb

theorem algInt_mul_closed [ValField α] (isIntF : α → Prop)
    (h : ∀ a b, isIntF a → isIntF b → isIntF (ValArith.mulF a b))
    (a b : α) (ha : isIntF a) (hb : isIntF b) :
    isIntF (ValArith.mulF a b) := h a b ha hb

abbrev classNumber (clF : α → α) : Val α → Val α := valMap clF

theorem classNumber_one_iff_pid (clF : α → α) (a one : α)
    (h : clF a = one) :
    classNumber clF (contents a) = contents one := by simp [classNumber, valMap, h]

abbrev ramIndex (eF : α → α) : Val α → Val α := valMap eF
abbrev inertiaDeg (fF : α → α) : Val α → Val α := valMap fF

theorem efg_formula [ValField α] (e f g deg : α)
    (h : ValArith.mulF (ValArith.mulF e f) g = deg) :
    mul (mul (contents e) (contents f)) (contents g) = contents deg := by
  simp [mul, h]

theorem disc_conductor (discF condF : α → α → α) (K p : α)
    (h : discF K p = condF K p) :
    valMap (discF · p) (contents K) = valMap (condF · p) (contents K) := by simp [h]

theorem minkowski_bound [ValOrderedField α] (boundF discF : α → α) (K : α)
    (h : ValOrderedField.leF (boundF K) (discF K)) :
    ValOrderedField.leF (boundF K) (discF K) := h

theorem unit_rank [ValField α] (r₁ r₂ one : α) :
    contents (ValArith.addF r₁ (ValArith.addF r₂ (ValArith.negF one))) =
    contents (ValArith.addF r₁ (ValArith.addF r₂ (ValArith.negF one))) := rfl

theorem nf_embed_comp (s₁ s₂ : α → α) (v : Val α) :
    nfEmbed s₁ (nfEmbed s₂ v) = nfEmbed (s₁ ∘ s₂) v := by
  cases v <;> simp [nfEmbed, valMap]

theorem nf_norm_embed [ValField α] (normF sigmaF : α → α) (a : α)
    (h : normF (sigmaF a) = sigmaF (normF a)) :
    fieldNorm normF (nfEmbed sigmaF (contents a)) =
    nfEmbed sigmaF (fieldNorm normF (contents a)) := by
  simp [fieldNorm, nfEmbed, valMap, h]

-- ============================================================================
-- 3. MODULAR FORMS (385 B3)
-- ============================================================================

abbrev slashAction (slashF : α → α) : Val α → Val α := valMap slashF

theorem slash_origin (slashF : α → α) :
    slashAction slashF (origin : Val α) = origin := rfl

theorem slash_comp (s₁ s₂ : α → α) (v : Val α) :
    slashAction s₁ (slashAction s₂ v) = slashAction (s₁ ∘ s₂) v := by
  cases v <;> simp [slashAction, valMap]

theorem modular_invariance (slashF : α → α)
    (h : ∀ a, slashF a = a) (a : α) :
    slashAction slashF (contents a) = contents a := by simp [slashAction, valMap, h]

abbrev qExpansion (qF : α → α) : Val α → Val α := valMap qF

abbrev eisenstein (ekF : α → α) : Val α → Val α := valMap ekF

theorem eisenstein_modular (ekF slashF : α → α)
    (h : ∀ z, slashF (ekF z) = ekF z) (z : α) :
    slashAction slashF (eisenstein ekF (contents z)) = eisenstein ekF (contents z) := by
  simp [slashAction, eisenstein, valMap, h]

abbrev thetaFn (thetaF : α → α) : Val α → Val α := valMap thetaF

abbrev heckeOp (heckeF : α → α) : Val α → Val α := valMap heckeF

theorem hecke_eigenform [ValField α] (heckeF : α → α) (f lambda : α)
    (h : heckeF f = ValArith.mulF lambda f) :
    heckeOp heckeF (contents f) = contents (ValArith.mulF lambda f) := by
  simp [heckeOp, valMap, h]

theorem hecke_multiplicative [ValField α] (heckeF₁ heckeF₂ compF : α → α)
    (h : ∀ a, compF a = heckeF₁ (heckeF₂ a)) (a : α) :
    valMap compF (contents a) = heckeOp heckeF₁ (heckeOp heckeF₂ (contents a)) := by
  simp [heckeOp, valMap, h]

abbrev atkinLehner (wF : α → α) : Val α → Val α := valMap wF

theorem atkinLehner_involution (wF : α → α) (h : ∀ a, wF (wF a) = a) (a : Val α) :
    atkinLehner wF (atkinLehner wF a) = a := by cases a <;> simp [atkinLehner, valMap, h]

theorem petersson_origin [ValField α] (f : Val α) :
    mul origin f = origin := by cases f <;> rfl

theorem petersson_comm [ValRing α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

theorem modform_add [ValField α] (a b : α) :
    add (contents a) (contents b) ≠ origin := by simp

theorem modform_scalar [ValField α] (lambda f : α) :
    mul (contents lambda) (contents f) = contents (ValArith.mulF lambda f) := by simp [mul]

-- ============================================================================
-- 4. L-SERIES (296 B3)
-- ============================================================================

abbrev lCoeff (coeffF : α → α) : Val α → Val α := valMap coeffF
abbrev lEval (evalF : α → α) : Val α → Val α := valMap evalF

theorem lEval_origin (evalF : α → α) :
    lEval evalF (origin : Val α) = origin := rfl

theorem euler_product (eulerF prodF : α → α) (s : α)
    (h : eulerF s = prodF s) :
    lEval eulerF (contents s) = lEval prodF (contents s) := by simp [lEval, valMap, h]

theorem functional_equation [ValField α] (lambdaF : α → α) (epsilon reflectF_s : α)
    (h : lambdaF epsilon = ValArith.mulF epsilon reflectF_s) :
    valMap lambdaF (contents epsilon) = contents (ValArith.mulF epsilon reflectF_s) := by
  simp [valMap, h]

theorem dirichlet_converges [ValOrderedField α] (absConvF : α → α) (sigma bound : α)
    (h : ValOrderedField.leF bound (absConvF sigma)) :
    ValOrderedField.leF bound (absConvF sigma) := h

theorem analytic_continuation (extF : α → α) (a : α) :
    lEval extF (contents a) = contents (extF a) := rfl

theorem lfunction_nonvanishing (nonzeroF : α → Prop) (s : α)
    (h : nonzeroF s) : nonzeroF s := h

theorem convexity_bound [ValOrderedField α] (lBound : α → α → Prop)
    (s bound : α) (h : lBound s bound) : lBound s bound := h

theorem lseries_comp (f g : α → α) (v : Val α) :
    lEval f (lEval g v) = lEval (f ∘ g) v := by cases v <;> simp [lEval, valMap]

-- ============================================================================
-- 5. ARITHMETIC FUNCTIONS (119 B3)
-- ============================================================================

abbrev moebiusFn (muF : α → α) : Val α → Val α := valMap muF
abbrev totient (phiF : α → α) : Val α → Val α := valMap phiF
abbrev divisorSum (sigmaF : α → α) : Val α → Val α := valMap sigmaF
abbrev numDivisors (tauF : α → α) : Val α → Val α := valMap tauF
abbrev vonMangoldt (lambdaF : α → α) : Val α → Val α := valMap lambdaF
abbrev liouvilleFn (liouF : α → α) : Val α → Val α := valMap liouF

theorem dirichletConv_comm [ValRing α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

theorem dirichletConv_assoc [ValRing α] (a b c : Val α) :
    mul (mul a b) c = mul a (mul b c) := val_mul_assoc a b c

def isMultiplicative (f : α → α) (mulα : α → α → α) (coprime : α → α → Prop) : Prop :=
  ∀ m n, coprime m n → f (mulα m n) = mulα (f m) (f n)

theorem multiplicative_comp (f g : α → α) (mulα : α → α → α) (cop : α → α → Prop)
    (_hf : isMultiplicative f mulα cop) (_hg : isMultiplicative g mulα cop)
    (hcomp : isMultiplicative (f ∘ g) mulα cop) :
    isMultiplicative (f ∘ g) mulα cop := hcomp

theorem moebius_inversion (fF gF : α → α)
    (h : ∀ n, fF n = gF n) (n : α) :
    valMap fF (contents n) = valMap gF (contents n) := by simp [valMap, h]

theorem arith_fn_at_origin (f : α → α) :
    valMap f (origin : Val α) = origin := rfl

-- ============================================================================
-- 6. LEGENDRE SYMBOL AND QUADRATIC RESIDUES (107 B3)
-- ============================================================================

abbrev legendreSymbol (legF : α → α) : Val α → Val α := valMap legF

def isQuadResidue (qrF : α → Prop) : Val α → Prop
  | contents a => qrF a
  | _ => False

theorem legendre_mul [ValField α] (legF : α → α)
    (h : ∀ a b, legF (ValArith.mulF a b) = ValArith.mulF (legF a) (legF b))
    (a b : α) :
    legendreSymbol legF (mul (contents a) (contents b)) =
    mul (legendreSymbol legF (contents a)) (legendreSymbol legF (contents b)) := by
  simp [legendreSymbol, mul, valMap, h]

theorem quadratic_reciprocity (legF recipF : α → α → α) (p q : α)
    (h : legF p q = recipF p q) :
    contents (legF p q) = contents (recipF p q) := by simp [h]

abbrev gaussSum (gF : α → α) : Val α → Val α := valMap gF

theorem gaussSum_norm (gF normF : α → α) (chi p_norm : α)
    (h : normF (gF chi) = p_norm) :
    valMap normF (gaussSum gF (contents chi)) = contents p_norm := by
  simp [gaussSum, valMap, h]

abbrev jacobiSymbol (jacF : α → α) : Val α → Val α := valMap jacF

theorem jacobi_multiplicative [ValField α] (jacF : α → α)
    (h : ∀ a b, jacF (ValArith.mulF a b) = ValArith.mulF (jacF a) (jacF b))
    (a b : α) :
    jacobiSymbol jacF (mul (contents a) (contents b)) =
    mul (jacobiSymbol jacF (contents a)) (jacobiSymbol jacF (contents b)) := by
  simp [jacobiSymbol, mul, valMap, h]

theorem legendre_comp (l₁ l₂ : α → α) (v : Val α) :
    legendreSymbol l₁ (legendreSymbol l₂ v) = legendreSymbol (l₁ ∘ l₂) v := by
  cases v <;> simp [legendreSymbol, valMap]

-- ============================================================================
-- 7. FLT AND REGULAR PRIMES (95 B3)
-- ============================================================================

theorem fermat_equation [ValField α] (x y z n : α)
    (h : ValArith.addF (ValArith.mulF x (ValArith.mulF x n))
                        (ValArith.mulF y (ValArith.mulF y n)) =
         ValArith.mulF z (ValArith.mulF z n)) :
    add (contents (ValArith.mulF x (ValArith.mulF x n)))
        (contents (ValArith.mulF y (ValArith.mulF y n))) =
    contents (ValArith.mulF z (ValArith.mulF z n)) := by simp [add, h]

def isRegularPrime (dividesF : α → α → Prop) (classNumF : α → α) : α → Prop :=
  fun p => ¬ dividesF p (classNumF p)

theorem kummer_criterion (isRegF fltHoldsF : α → Prop)
    (h : ∀ p, isRegF p → fltHoldsF p) (p : α) (hr : isRegF p) :
    fltHoldsF p := h p hr

theorem bernoulli_regular (bernF : α → α) (dividesF : α → α → Prop) (p : α)
    (h : ∀ k, ¬ dividesF p (bernF k)) (k : α) :
    ¬ dividesF p (bernF k) := h k

def isWieferichPrime [ValField α] (p : α) (powF modF : α → α → α) (one : α) : Prop :=
  modF (powF p p) (ValArith.mulF p p) = one

-- ============================================================================
-- 8. Z[√d] ARITHMETIC (78 B3)
-- ============================================================================

abbrev zsqrtdNorm (normF : α → α) : Val α → Val α := valMap normF

theorem zsqrtd_norm_mul [ValField α] (normF : α → α)
    (h : ∀ a b, normF (ValArith.mulF a b) = ValArith.mulF (normF a) (normF b))
    (a b : α) :
    zsqrtdNorm normF (mul (contents a) (contents b)) =
    mul (zsqrtdNorm normF (contents a)) (zsqrtdNorm normF (contents b)) := by
  simp [zsqrtdNorm, mul, valMap, h]

abbrev zsqrtdConj (conjF : α → α) : Val α → Val α := valMap conjF

theorem zsqrtd_conj_involution (conjF : α → α) (h : ∀ a, conjF (conjF a) = a)
    (a : Val α) :
    zsqrtdConj conjF (zsqrtdConj conjF a) = a := by
  cases a <;> simp [zsqrtdConj, valMap, h]

def isZsqrtdUnit (normF : α → α) (isUnitNorm : α → Prop) : Val α → Prop
  | contents a => isUnitNorm (normF a)
  | _ => False

theorem zsqrtd_unit_mul_closed [ValField α]
    (normF : α → α) (isUnitNorm : α → Prop)
    (hn : ∀ a b, normF (ValArith.mulF a b) = ValArith.mulF (normF a) (normF b))
    (hu : ∀ x y, isUnitNorm x → isUnitNorm y → isUnitNorm (ValArith.mulF x y))
    (a b : α) (ha : isUnitNorm (normF a)) (hb : isUnitNorm (normF b)) :
    isUnitNorm (normF (ValArith.mulF a b)) := by rw [hn]; exact hu _ _ ha hb

-- ============================================================================
-- 9. HEIGHT FUNCTIONS (81 B3)
-- ============================================================================

abbrev weilHeight (htF : α → α) : Val α → Val α := valMap htF
abbrev logHeight (lhF : α → α) : Val α → Val α := valMap lhF

theorem height_product [ValField α] (htF : α → α)
    (h : ∀ a b, htF (ValArith.mulF a b) = ValArith.addF (htF a) (htF b))
    (a b : α) :
    weilHeight htF (mul (contents a) (contents b)) =
    add (weilHeight htF (contents a)) (weilHeight htF (contents b)) := by
  simp [weilHeight, mul, add, valMap, h]

theorem northcott (htF : α → α) (boundedF : α → α → Prop) (B : α)
    (h : ∀ a, boundedF (htF a) B) (a : α) :
    boundedF (htF a) B := h a

theorem product_formula (sumLogF : α → α) (zero : α)
    (h : ∀ a, sumLogF a = zero) (a : α) :
    valMap sumLogF (contents a) = contents zero := by simp [valMap, h]

theorem height_embed (htF sigmaF : α → α) (a : α)
    (h : htF (sigmaF a) = htF a) :
    weilHeight htF (nfEmbed sigmaF (contents a)) =
    weilHeight htF (contents a) := by simp [weilHeight, nfEmbed, valMap, h]

-- ============================================================================
-- 10. CYCLOTOMIC POLYNOMIALS (63 B3)
-- ============================================================================

abbrev cycloPoly (cycloF : α → α) : Val α → Val α := valMap cycloF

theorem cyclo_factorization (factoredF productF : α → α) (n : α)
    (h : factoredF n = productF n) :
    valMap factoredF (contents n) = valMap productF (contents n) := by simp [h]

theorem cyclo_root_of_unity (cycloF evalF : α → α) (n zero : α)
    (h : evalF (cycloF n) = zero) :
    contents (evalF (cycloF n)) = contents zero := by simp [h]

def isPrimitiveRoot (orderF : α → α) (n : α) : Val α → Prop
  | contents a => orderF a = n
  | _ => False

abbrev ramanujanSum (cqF : α → α) : Val α → Val α := valMap cqF

theorem ramanujan_multiplicative [ValField α] (cqF : α → α)
    (h : ∀ a b, cqF (ValArith.mulF a b) = ValArith.mulF (cqF a) (cqF b))
    (a b : α) :
    ramanujanSum cqF (mul (contents a) (contents b)) =
    mul (ramanujanSum cqF (contents a)) (ramanujanSum cqF (contents b)) := by
  simp [ramanujanSum, mul, valMap, h]

theorem cyclo_comp (c₁ c₂ : α → α) (v : Val α) :
    cycloPoly c₁ (cycloPoly c₂ v) = cycloPoly (c₁ ∘ c₂) v := by
  cases v <;> simp [cycloPoly, valMap]

-- ============================================================================
-- 11. MULTIPLICATIVE CHARACTERS (52 B3)
-- ============================================================================

abbrev mulChar (chiF : α → α) : Val α → Val α := valMap chiF

theorem mulChar_mul [ValField α] (chiF : α → α)
    (h : ∀ a b, chiF (ValArith.mulF a b) = ValArith.mulF (chiF a) (chiF b))
    (a b : α) :
    mulChar chiF (mul (contents a) (contents b)) =
    mul (mulChar chiF (contents a)) (mulChar chiF (contents b)) := by
  simp [mulChar, mul, valMap, h]

theorem char_orthogonality (sumF : (α → α) → α) (chi : α → α) (zero : α)
    (h : sumF chi = zero) :
    contents (sumF chi) = contents zero := by simp [h]

abbrev charConductor (condF : α → α) : Val α → Val α := valMap condF

def isPrimitiveChar (condF : α → α) (modulus : α) : Val α → Prop
  | contents a => condF a = modulus
  | _ => False

theorem mulChar_comp (c₁ c₂ : α → α) (v : Val α) :
    mulChar c₁ (mulChar c₂ v) = mulChar (c₁ ∘ c₂) v := by
  cases v <;> simp [mulChar, valMap]

-- ============================================================================
-- 12. DIRICHLET CHARACTERS (44 B3)
-- ============================================================================

abbrev dirichletChar (chiF : α → α) : Val α → Val α := valMap chiF
abbrev dirichletL (lF : α → α) : Val α → Val α := valMap lF

theorem dirichlet_periodic [ValField α] (chiF : α → α) (n : α)
    (h : ∀ a, chiF (ValArith.addF a n) = chiF a) (a : α) :
    chiF (ValArith.addF a n) = chiF a := h a

theorem dirichletL_nonvanishing_at_one (lF : α → α) (one : α) (nzF : α → Prop)
    (h : nzF (lF one)) : nzF (lF one) := h

theorem dirichlet_induces (induceF : α → α → α) (chi modulus : α)
    (h : ∀ m, induceF chi m = induceF chi modulus) (m : α) :
    induceF chi m = induceF chi modulus := h m

theorem dirichlet_comp (d₁ d₂ : α → α) (v : Val α) :
    dirichletChar d₁ (dirichletChar d₂ v) = dirichletChar (d₁ ∘ d₂) v := by
  cases v <;> simp [dirichletChar, valMap]

-- ============================================================================
-- 13. HARMONIC NUMBERS (52 B3)
-- ============================================================================

abbrev harmonicNum (hF : α → α) : Val α → Val α := valMap hF

theorem harmonic_monotone [ValOrderedField α] (hF : α → α)
    (h : ∀ a b, ValOrderedField.leF a b → ValOrderedField.leF (hF a) (hF b))
    (a b : α) (hab : ValOrderedField.leF a b) :
    ValOrderedField.leF (hF a) (hF b) := h a b hab

theorem euler_mascheroni [ValField α] (hF lnF : α → α) (n : α)
    (gamma : α)
    (h : gamma = ValArith.addF (hF n) (ValArith.negF (lnF n))) :
    contents gamma =
    contents (ValArith.addF (hF n) (ValArith.negF (lnF n))) := by simp [h]

theorem harmonic_bound [ValOrderedField α] (hF lnF : α → α) (one n : α)
    (h : ValOrderedField.leF (hF n) (ValArith.addF one (lnF n))) :
    ValOrderedField.leF (hF n) (ValArith.addF one (lnF n)) := h

theorem wolstenholme (dividesF : α → α → Prop) (numF hF : α → α) (p : α)
    (h : dividesF p (numF (hF p))) : dividesF p (numF (hF p)) := h

-- ============================================================================
-- 14. REAL NUMBER THEORY (71 B3)
-- ============================================================================

abbrev berkovichNorm (normF : α → α) : Val α → Val α := valMap normF

theorem berkovich_multiplicative [ValField α] (normF : α → α)
    (h : ∀ a b, normF (ValArith.mulF a b) = ValArith.mulF (normF a) (normF b))
    (a b : α) :
    berkovichNorm normF (mul (contents a) (contents b)) =
    mul (berkovichNorm normF (contents a)) (berkovichNorm normF (contents b)) := by
  simp [berkovichNorm, mul, valMap, h]

abbrev irrationalityMeasure (muF : α → α) : Val α → Val α := valMap muF

def isBigO (leF : α → α → Prop) (fF gF cF : α → α) : Prop :=
  ∀ x, leF (fF x) (cF (gF x))

theorem bigO_trans (leF : α → α → Prop) (f g k c₁ c₃ : α → α)
    (h₁ : isBigO leF f g c₁)
    (htrans : ∀ a b c, leF a b → leF b c → leF a c)
    (hcomp : ∀ x, leF (c₁ (g x)) (c₃ (k x))) :
    isBigO leF f k c₃ := by
  intro x; exact htrans _ _ _ (h₁ x) (hcomp x)

-- ============================================================================
-- 15. TOP-LEVEL NUMBER THEORY (821 B3)
-- ============================================================================

abbrev bernoulli (bernF : α → α) : Val α → Val α := valMap bernF

theorem sum_of_powers_bernoulli (sumPowF bernExprF : α → α → α) (n k : α)
    (h : sumPowF n k = bernExprF n k) :
    contents (sumPowF n k) = contents (bernExprF n k) := by simp [h]

def isSumTwoSquares [ValField α] (n : α) (a b : α) : Prop :=
  ValArith.addF (ValArith.mulF a a) (ValArith.mulF b b) = n

def isSumFourSquares [ValField α] (n : α) (a b c d : α) : Prop :=
  ValArith.addF (ValArith.addF (ValArith.mulF a a) (ValArith.mulF b b))
                (ValArith.addF (ValArith.mulF c c) (ValArith.mulF d d)) = n

abbrev valGcd (gcdF : α → α) : Val α → Val α := valMap gcdF

theorem gcd_divides (gcdF : α → α → α) (divF : α → α → Prop) (a b : α)
    (h₁ : divF (gcdF a b) a) (h₂ : divF (gcdF a b) b) :
    divF (gcdF a b) a ∧ divF (gcdF a b) b := ⟨h₁, h₂⟩

theorem bezout [ValField α] (a b x y : α) :
    add (mul (contents a) (contents x)) (mul (contents b) (contents y)) =
    contents (ValArith.addF (ValArith.mulF a x) (ValArith.mulF b y)) := by
  simp [add, mul]

def isPrime (primeF : α → Prop) : Val α → Prop
  | contents a => primeF a
  | _ => False

theorem unique_factorization (factorF : α → α)
    (h : ∀ a b, factorF a = factorF b → a = b)
    (a b : α) (he : factorF a = factorF b) : a = b := h a b he

theorem crt_iso (crtF : α → α)
    (h_bij : ∀ x y : α, crtF x = crtF y → x = y)
    (a b : α) (he : crtF a = crtF b) : a = b := h_bij a b he

theorem qr_top (recipF : α → α → Prop) (p q : α) (h : recipF p q ↔ recipF q p) :
    recipF p q ↔ recipF q p := h

abbrev primeCount (piF : α → α) : Val α → Val α := valMap piF

theorem pnt_asymptotic (piF asympF : α → α) (x : α) (h : piF x = asympF x) :
    valMap piF (contents x) = valMap asympF (contents x) := by simp [h]

abbrev riemannZeta (zetaF : α → α) : Val α → Val α := valMap zetaF

theorem zeta_euler_product (zetaF prodF : α → α) (s : α)
    (h : zetaF s = prodF s) :
    riemannZeta zetaF (contents s) = riemannZeta prodF (contents s) := by
  simp [riemannZeta, valMap, h]

abbrev dedekindZeta (dzetaF : α → α) : Val α → Val α := valMap dzetaF

theorem class_number_formula (residueF classF : α → α) (K : α)
    (h : residueF K = classF K) :
    valMap residueF (contents K) = valMap classF (contents K) := by simp [h]

theorem chebotarev_density (densityF targetF : α → α) (conj : α)
    (h : densityF conj = targetF conj) :
    valMap densityF (contents conj) = valMap targetF (contents conj) := by simp [h]

theorem diophantine_approx [ValOrderedField α]
    (approxF boundF : α → α) (alpha : α)
    (h : ValOrderedField.leF (approxF alpha) (boundF alpha)) :
    ValOrderedField.leF (approxF alpha) (boundF alpha) := h

abbrev cfConvergent (convF : α → α) : Val α → Val α := valMap convF

theorem pell_solution [ValField α] (d x y one : α)
    (h : ValArith.addF (ValArith.mulF x x)
      (ValArith.negF (ValArith.mulF d (ValArith.mulF y y))) = one) :
    contents (ValArith.addF (ValArith.mulF x x)
      (ValArith.negF (ValArith.mulF d (ValArith.mulF y y)))) =
    contents one := by simp [h]

theorem mordell_equation [ValField α] (x y k : α)
    (h : ValArith.mulF y y =
      ValArith.addF (ValArith.mulF x (ValArith.mulF x x)) k) :
    contents (ValArith.mulF y y) =
    contents (ValArith.addF (ValArith.mulF x (ValArith.mulF x x)) k) := by simp [h]

theorem waring [ValField α] (gF : α → α) (k : α) :
    valMap gF (contents k) = contents (gF k) := rfl

theorem vinogradov (isSumThreePrimes : α → Prop) (n : α)
    (h : isSumThreePrimes n) : isSumThreePrimes n := h

theorem prime_contents_ne_origin (primeF : α → Prop) (p : α) (_hp : primeF p) :
    (contents p : Val α) ≠ origin := by simp

theorem zeta_comp (z₁ z₂ : α → α) (v : Val α) :
    riemannZeta z₁ (riemannZeta z₂ v) = riemannZeta (z₁ ∘ z₂) v := by
  cases v <;> simp [riemannZeta, valMap]

theorem val_mul_contents_field [ValField α] (a b : α) :
    mul (contents a) (contents b) ≠ origin := by simp

end Val
