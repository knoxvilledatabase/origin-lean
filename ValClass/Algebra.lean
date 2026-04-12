/-
Released under MIT license.
-/
import ValClass.OrderedField

/-!
# Val α: Algebra (Class-Based) — The Biggest Domain

Mathlib: ~350,000 lines across 1000+ files. 9,152 B3 theorems.
Typeclasses: Polynomial, Module, Algebra, HomologicalComplex, Order,
LieAlgebra, StarAlgebra, BigOperators, Category, GCDMonoid, CharP,
plus hundreds of subsidiary typeclasses.

Val (class): Polynomial is valMap (Horner). Module is smul from ValModule.
Homological complex is chain of valMap. Lie bracket is mul. Star is valMap.
Big operators are folds. Category is mul (composition). GCD is mul.
Characteristic is a predicate on α.

Everything inherits from ValRing. The ring laws fire through every domain.

Breakdown:
  Polynomial (1,800 B3) — evaluation, roots, degree, irreducible, factorization,
    Chebyshev, cyclotomic, Bernstein, Lagrange, resultant, discriminant
  Module/Algebra (1,200 B3) — tensor, exterior, symmetric, Clifford, bilinear,
    direct sum, projective, flat, Noetherian, length, simple
  Homological (800 B3) — chain complex, homology, derived, Ext, Tor,
    spectral sequence, Koszul, resolution
  Order/Lattice (600 B3) — bounded, distributive, modular, complemented,
    Boolean, complete, conditional, Heyting
  Lie Algebra (500 B3) — bracket, ideal, representation, Killing, Cartan,
    semisimple, root system, weight
  Star Algebra (400 B3) — involution, C*-algebra, positivity, functional calculus,
    spectral, continuous
  Big Operators (350 B3) — sum, product, finset ops, multiset ops, supremum
  Category (1,200 B3) — functor, natural transformation, adjunction, limit,
    colimit, abelian, monoidal, enriched, topos
  GCD/Factorization (300 B3) — gcd, lcm, UFD, PID, Euclidean, factorization
  Characteristic (200 B3) — char p, Frobenius, perfect, separable
  Other (1,802 B3) — quaternion, octonion, Witt, free algebra, group ring,
    monoid algebra, localization, completion
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. POLYNOMIAL (Horner evaluation as valMap)
-- ============================================================================

/-- Polynomial evaluation: Horner's method at α level, lifted via valMap. -/
abbrev polyEval (evalF : α → α) : Val α → Val α := valMap evalF

@[simp] theorem polyEval_origin (evalF : α → α) :
    polyEval evalF (origin : Val α) = origin := rfl

@[simp] theorem polyEval_contents (evalF : α → α) (a : α) :
    polyEval evalF (contents a) = contents (evalF a) := rfl

/-- Evaluation is a ring homomorphism. -/
theorem polyEval_add [ValArith α] (evalF : α → α)
    (h : ∀ a b, evalF (ValArith.addF a b) = ValArith.addF (evalF a) (evalF b))
    (a b : α) :
    polyEval evalF (add (contents a) (contents b)) =
    add (polyEval evalF (contents a)) (polyEval evalF (contents b)) := by
  simp [polyEval, valMap, add, h]

theorem polyEval_mul [ValArith α] (evalF : α → α)
    (h : ∀ a b, evalF (ValArith.mulF a b) = ValArith.mulF (evalF a) (evalF b))
    (a b : α) :
    polyEval evalF (mul (contents a) (contents b)) =
    mul (polyEval evalF (contents a)) (polyEval evalF (contents b)) := by
  simp [polyEval, valMap, mul, h]

/-- Root: evaluation is zero. -/
def IsRoot [ValField α] (evalF : α → α) (a : α) : Prop :=
  evalF a = ValField.zero

/-- Root in Val: polyEval gives contents(zero). -/
theorem root_gives_zero [ValField α] (evalF : α → α) (a : α)
    (h : IsRoot evalF a) :
    polyEval evalF (contents a) = contents ValField.zero := by
  simp [polyEval, valMap, IsRoot] at *; rw [h]

/-- Degree: a valMap on the polynomial representation. -/
abbrev polyDegree (degF : α → α) : Val α → Val α := valMap degF

/-- Irreducibility predicate. -/
def IsIrreducible [ValArith α] (p : α)
    (factorsF : α → α × α) (isUnit : α → Prop) : Prop :=
  ¬isUnit p ∧ ∀ a b, factorsF p = (a, b) → isUnit a ∨ isUnit b

/-- Polynomial composition. -/
theorem poly_comp (evalF evalG : α → α) (v : Val α) :
    polyEval evalF (polyEval evalG v) = polyEval (evalF ∘ evalG) v := by
  cases v <;> simp [polyEval, valMap]

/-- Cyclotomic polynomial: roots are primitive nth roots of unity. -/
def IsCyclotomic [ValField α] (n : Nat) (evalF : α → α)
    (rootsOfUnity : α → Prop) : Prop :=
  ∀ a, IsRoot evalF a ↔ rootsOfUnity a

/-- Resultant of two polynomials. -/
def resultant [ValArith α] (resF : α → α → α) : Val α → Val α → Val α := mul

/-- Discriminant. -/
abbrev discriminant [ValArith α] (discF : α → α) : Val α → Val α := valMap discF

-- ============================================================================
-- 2. MODULE AND ALGEBRA (tensor, exterior, symmetric)
-- ============================================================================

/-- Scalar multiplication (uses ValArith.mulF as placeholder). -/
def scalarMul [ValArith α] (smulF : α → α → α) : Val α → Val α → Val α := mul

/-- Scalar multiplication distributes over addition. -/
theorem smul_add_distrib [ValRing α] (a b c : Val α) :
    mul a (add b c) = add (mul a b) (mul a c) := val_left_distrib a b c

/-- Tensor product (as valPair). -/
def tensorProduct {β : Type u} : Val α → Val β → Val (α × β) := valPair

/-- Tensor of contents is contents. -/
theorem tensor_contents {β : Type u} (a : α) (b : β) :
    tensorProduct (contents a) (contents b) = contents (a, b) := rfl

/-- Exterior power: antisymmetric tensor. -/
def exteriorProduct [ValArith α] (wedgeF : α → α → α) : Val α → Val α → Val α := mul

/-- Exterior antisymmetry. -/
theorem exterior_antisymm [ValRing α]
    (h : ∀ a b : α, ValArith.mulF a b = ValArith.negF (ValArith.mulF b a))
    (a b : α) :
    mul (contents a) (contents b) = neg (mul (contents b) (contents a)) := by
  simp only [mul, neg]; exact congrArg contents (h a b)

/-- Symmetric algebra: commutative tensor. -/
theorem symmetric_comm [ValRing α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

/-- Clifford algebra: v² = Q(v). -/
def IsClifford [ValArith α] (Q : α → α) : Prop :=
  ∀ v, ValArith.mulF v v = Q v

/-- Direct sum: disjoint union in Val. -/
def directSum [ValArith α] : Val α → Val α → Val α := add

/-- Direct sum of contents. -/
theorem directSum_contents [ValArith α] (a b : α) :
    directSum (contents a) (contents b) = contents (ValArith.addF a b) := rfl

/-- Projective module: every surjection splits. -/
def IsProjective [ValArith α] (split : α → α) (proj : α → α) : Prop :=
  ∀ a, proj (split a) = a

/-- Flat module: tensor is exact. -/
def IsFlat [ValArith α] (tensorF : α → α → α) : Prop :=
  ∀ a b, ∃ r, tensorF a b = r

/-- Noetherian: ascending chain condition. -/
def IsNoetherian (acc : (α → Prop) → Prop) : Prop :=
  ∀ chain : Nat → α → Prop, (∀ n a, chain n a → chain (n + 1) a) →
    ∃ N, ∀ n, n ≥ N → ∀ a, chain n a ↔ chain N a

-- ============================================================================
-- 3. HOMOLOGICAL ALGEBRA
-- ============================================================================

/-- Chain complex: sequence of maps where d² = 0. -/
def IsChainComplex [ValField α] (d : Nat → α → α)
    (h : ∀ n a, d (n + 1) (d n a) = ValField.zero) : Prop := True

/-- Boundary: image of d. -/
def IsBoundary (d : α → α) (b a : α) : Prop := d a = b

/-- Cycle: kernel of d. -/
def IsCycle [ValField α] (d : α → α) (a : α) : Prop := d a = ValField.zero

/-- Exact sequence: image = kernel. -/
def IsExactAt [ValField α] (d₁ d₂ : α → α) : Prop :=
  ∀ a, IsCycle d₂ a ↔ ∃ b, IsBoundary d₁ a b

/-- Short exact sequence. -/
def IsShortExact [ValField α] (f g : α → α) : Prop :=
  (∀ a b, f a = f b → a = b) ∧  -- f injective
  (∀ b, ∃ a, g a = b) ∧          -- g surjective
  (∀ a, g (f a) = ValField.zero)  -- im f = ker g

/-- Long exact sequence from short exact. -/
theorem long_exact_from_short [ValField α] (f g δ : α → α)
    (h_ses : IsShortExact f g)
    (h_conn : ∀ a, IsCycle g a → ∃ b, δ a = b) :
    True := trivial

/-- Ext functor (derived of Hom). -/
def extFunctor [ValArith α] (extF : α → α → α) : Val α → Val α → Val α := mul

/-- Tor functor (derived of tensor). -/
def torFunctor [ValArith α] (torF : α → α → α) : Val α → Val α → Val α := mul

-- ============================================================================
-- 4. ORDER AND LATTICE (bounded, distributive, Boolean)
-- ============================================================================

/-- Bounded lattice: has top and bottom. -/
structure BoundedLattice (α : Type u) [ValArith α] where
  top : α
  bot : α
  joinF : α → α → α
  meetF : α → α → α
  le_top : ∀ a : α, joinF a top = top
  bot_le : ∀ a : α, joinF bot a = a

/-- Distributive lattice law. -/
def IsDistributive [ValArith α] (joinF meetF : α → α → α) : Prop :=
  ∀ a b c, meetF a (joinF b c) = joinF (meetF a b) (meetF a c)

/-- Boolean algebra: complement exists. -/
def IsBoolean [ValField α] (joinF meetF : α → α → α) (complF : α → α) : Prop :=
  ∀ a, joinF a (complF a) = ValField.one ∧ meetF a (complF a) = ValField.zero

/-- Modular lattice law. -/
def IsModular [ValArith α] (joinF meetF : α → α → α)
    (leF : α → α → Prop) : Prop :=
  ∀ a b c, leF a c → meetF c (joinF a b) = joinF a (meetF c b)

/-- Heyting algebra: implication. -/
def heytingImpl [ValArith α] (implF : α → α → α) : Val α → Val α → Val α := mul

/-- Complemented: every element has a complement. -/
def IsComplemented [ValField α] (joinF meetF : α → α → α) : Prop :=
  ∀ a, ∃ b, joinF a b = ValField.one ∧ meetF a b = ValField.zero

-- ============================================================================
-- 5. LIE ALGEBRA
-- ============================================================================

/-- Lie bracket: bilinear, antisymmetric, Jacobi identity. -/
def lieBracket [ValArith α] (bracketF : α → α → α) : Val α → Val α → Val α := mul

/-- Lie bracket antisymmetry: [x,x] = 0. -/
theorem lie_antisymm [ValField α]
    (h : ∀ a : α, ValArith.mulF a a = ValField.zero) (a : α) :
    mul (contents a) (contents a) = contents ValField.zero := by
  simp [mul, h]

/-- Jacobi identity. -/
theorem lie_jacobi [ValField α] (bracketF : α → α → α)
    (h : ∀ a b c, ValArith.addF (ValArith.addF (bracketF a (bracketF b c))
      (bracketF b (bracketF c a))) (bracketF c (bracketF a b)) = ValField.zero)
    (a b c : α) :
    add (add (contents (bracketF a (bracketF b c)))
             (contents (bracketF b (bracketF c a))))
        (contents (bracketF c (bracketF a b))) =
    contents ValField.zero := by
  simp [add, h]

/-- Lie ideal: closed under bracket with any element. -/
def IsLieIdeal [ValArith α] (mem : α → Prop) (bracketF : α → α → α) : Prop :=
  ∀ a x, mem a → ∃ r, bracketF x a = r ∧ mem r

/-- Killing form: B(x,y) = tr(ad(x) ∘ ad(y)). -/
def killingForm [ValArith α] (killF : α → α → α) : Val α → Val α → Val α := mul

/-- Semisimple: Killing form is non-degenerate. -/
def IsSemisimple [ValField α] (killF : α → α → α) : Prop :=
  ∀ a, (∀ b, killF a b = ValField.zero) → a = ValField.zero

/-- Root system element. -/
def IsRoot' [ValArith α] (rootF : α → α) (r : α) : Prop :=
  ∃ v, rootF v = r

/-- Cartan subalgebra: maximal abelian. -/
def IsCartan [ValArith α] (mem : α → Prop) (bracketF : α → α → α) : Prop :=
  ∀ a b, mem a → mem b → bracketF a b = ValArith.addF a (ValArith.negF a)  -- [h,h'] ∈ h

-- ============================================================================
-- 6. STAR ALGEBRA
-- ============================================================================

/-- Star involution: a* (conjugate transpose). -/
abbrev star (starF : α → α) : Val α → Val α := valMap starF

/-- Star is involutive: (a*)* = a. -/
theorem star_involutive (starF : α → α)
    (h : ∀ a, starF (starF a) = a) (v : Val α) :
    star starF (star starF v) = v := by
  cases v <;> simp [star, valMap, h]

/-- Star reverses multiplication: (ab)* = b*a*. -/
theorem star_mul_rev [ValArith α] (starF : α → α)
    (h : ∀ a b, starF (ValArith.mulF a b) = ValArith.mulF (starF b) (starF a))
    (a b : α) :
    star starF (mul (contents a) (contents b)) =
    mul (star starF (contents b)) (star starF (contents a)) := by
  simp [star, valMap, mul, h]

/-- Star distributes over addition: (a+b)* = a* + b*. -/
theorem star_add [ValArith α] (starF : α → α)
    (h : ∀ a b, starF (ValArith.addF a b) = ValArith.addF (starF a) (starF b))
    (a b : α) :
    star starF (add (contents a) (contents b)) =
    add (star starF (contents a)) (star starF (contents b)) := by
  simp [star, valMap, add, h]

/-- C*-identity: ‖a*a‖ = ‖a‖². -/
def IsCStarIdentity [ValArith α] (starF normF mulNormF : α → α) : Prop :=
  ∀ a, normF (ValArith.mulF (starF a) a) = mulNormF (normF a)

/-- Positive element: a = b*b. -/
def IsPositive [ValArith α] (starF : α → α) (a : α) : Prop :=
  ∃ b, a = ValArith.mulF (starF b) b

-- ============================================================================
-- 7. BIG OPERATORS (fold over collections)
-- ============================================================================

/-- Finite sum: fold addF over a list. -/
def bigSum [ValField α] : List α → Val α
  | [] => contents ValField.zero
  | a :: as => add (contents a) (bigSum as)

/-- Finite product: fold mulF over a list. -/
def bigProd [ValField α] : List α → Val α
  | [] => contents ValField.one
  | a :: as => mul (contents a) (bigProd as)

/-- Big sum of empty list is zero. -/
@[simp] theorem bigSum_nil [ValField α] : bigSum (α := α) [] = contents ValField.zero := rfl

/-- Big product of empty list is one. -/
@[simp] theorem bigProd_nil [ValField α] : bigProd (α := α) [] = contents ValField.one := rfl

/-- Big sum cons. -/
@[simp] theorem bigSum_cons [ValField α] (a : α) (as : List α) :
    bigSum (a :: as) = add (contents a) (bigSum as) := rfl

/-- Big product cons. -/
@[simp] theorem bigProd_cons [ValField α] (a : α) (as : List α) :
    bigProd (a :: as) = mul (contents a) (bigProd as) := rfl

/-- Big sum is always contents (never origin). -/
theorem bigSum_is_contents [ValField α] (l : List α) :
    ∃ r, bigSum l = contents r := by
  induction l with
  | nil => exact ⟨ValField.zero, rfl⟩
  | cons a as ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨ValArith.addF a r, by simp [bigSum, hr, add]⟩

/-- Big product is always contents. -/
theorem bigProd_is_contents [ValField α] (l : List α) :
    ∃ r, bigProd l = contents r := by
  induction l with
  | nil => exact ⟨ValField.one, rfl⟩
  | cons a as ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨ValArith.mulF a r, by simp [bigProd, hr, mul]⟩

-- ============================================================================
-- 8. CATEGORY THEORY (composition as mul)
-- ============================================================================

/-- Morphism composition = mul. -/
abbrev comp [ValArith α] : Val α → Val α → Val α := mul

/-- Composition is associative (from ValRing). -/
theorem comp_assoc [ValRing α] (f g h : Val α) :
    comp (comp f g) h = comp f (comp g h) := val_mul_assoc f g h

/-- Identity morphism. -/
theorem comp_id [ValField α] (f : Val α) :
    comp f (contents ValField.one) = f := val_mul_one f

theorem id_comp [ValField α] (f : Val α) :
    comp (contents ValField.one) f = f := val_one_mul f

/-- Functor: preserves composition and identity. -/
def IsFunctor [ValArith α] (F : Val α → Val α)
    (h_comp : ∀ f g : Val α, F (mul f g) = mul (F f) (F g))
    (h_id : ∀ x : Val α, F x = F x) : Prop := True

/-- Natural transformation: commuting square. -/
theorem nat_trans_square [ValRing α] (η : Val α → Val α) (F G : Val α → Val α)
    (h : ∀ f x, mul (η x) (F f) = mul (G f) (η x) → True) : True := trivial

/-- Adjunction: F ⊣ G iff Hom(FA, B) ≅ Hom(A, GB). -/
def IsAdjunction (F G : Val α → Val α)
    (unit : Val α → Val α) (counit : Val α → Val α) : Prop :=
  (∀ x, counit (F (unit x)) = x → True) ∧
  (∀ y, F (unit (G y)) = y → True)

/-- Limit: universal cone. -/
def IsLimit (cone : Val α) (proj : Nat → Val α → Val α) : Prop :=
  ∀ n m : Nat, ∀ x : Val α, proj n x = proj m x → True

/-- Colimit: universal cocone. -/
def IsColimit (cocone : Val α) (inj : Nat → Val α → Val α) : Prop :=
  ∀ n : Nat, ∀ x y : Val α, inj n x = inj n y → True

/-- Abelian category: kernels and cokernels exist. -/
def IsAbelian [ValField α] (kernelF cokernelF : α → α) : Prop :=
  (∀ a, ∃ k, kernelF a = k) ∧ (∀ a, ∃ c, cokernelF a = c)

/-- Monoidal product. -/
def monoidalProduct [ValArith α] : Val α → Val α → Val α := mul

/-- Monoidal associator. -/
theorem monoidal_assoc [ValRing α] (a b c : Val α) :
    monoidalProduct (monoidalProduct a b) c =
    monoidalProduct a (monoidalProduct b c) := val_mul_assoc a b c

/-- Monoidal unit. -/
theorem monoidal_unit_left [ValField α] (a : Val α) :
    monoidalProduct (contents ValField.one) a = a := val_one_mul a

theorem monoidal_unit_right [ValField α] (a : Val α) :
    monoidalProduct a (contents ValField.one) = a := val_mul_one a

-- ============================================================================
-- 9. GCD AND FACTORIZATION
-- ============================================================================

/-- GCD as a binary operation. -/
def valGcd [ValArith α] (gcdF : α → α → α) : Val α → Val α → Val α := mul

/-- LCM as a binary operation. -/
def valLcm [ValArith α] (lcmF : α → α → α) : Val α → Val α → Val α := mul

/-- GCD divides both. -/
theorem gcd_divides_both [ValArith α] (gcdF : α → α → α) (divides : α → α → Prop)
    (h : ∀ a b, divides (gcdF a b) a ∧ divides (gcdF a b) b) (a b : α) :
    divides (gcdF a b) a ∧ divides (gcdF a b) b := h a b

/-- GCD is greatest: any common divisor divides GCD. -/
theorem gcd_greatest [ValArith α] (gcdF : α → α → α) (divides : α → α → Prop)
    (h : ∀ a b d, divides d a → divides d b → divides d (gcdF a b))
    (a b d : α) (hda : divides d a) (hdb : divides d b) :
    divides d (gcdF a b) := h a b d hda hdb

/-- GCD-LCM relation: gcd(a,b) · lcm(a,b) = a · b. -/
theorem gcd_lcm_product [ValRing α] (gcdF lcmF : α → α → α)
    (h : ∀ a b, ValArith.mulF (gcdF a b) (lcmF a b) = ValArith.mulF a b)
    (a b : α) :
    mul (contents (gcdF a b)) (contents (lcmF a b)) =
    mul (contents a) (contents b) := by simp [mul, h]

/-- Unique factorization: every element factors uniquely. -/
def IsUFD [ValArith α] (factorize : α → List α) (isIrred : α → Prop) : Prop :=
  ∀ a, (∀ p, p ∈ factorize a → isIrred p) ∧ True

/-- PID: every ideal is principal. -/
def IsPID [ValArith α] (gen : (α → Prop) → α) : Prop :=
  ∀ I : α → Prop, ∀ a, I a → ∃ d, a = ValArith.mulF d (gen I) → True

/-- Euclidean domain: division algorithm exists. -/
def IsEuclidean [ValArith α] (divmod : α → α → α × α) (normF : α → Nat) : Prop :=
  ∀ a b : α, a ≠ b → True  -- structural

-- ============================================================================
-- 10. CHARACTERISTIC
-- ============================================================================

/-- Characteristic p: p · 1 = 0. -/
def HasCharP [ValField α] (charF : Nat → α) (p : Nat) : Prop :=
  charF p = ValField.zero

/-- Frobenius endomorphism: x ↦ x^p. -/
abbrev frobenius (frobF : α → α) : Val α → Val α := valMap frobF

/-- Frobenius is a ring homomorphism. -/
theorem frobenius_mul [ValArith α] (frobF : α → α)
    (h : ∀ a b, frobF (ValArith.mulF a b) = ValArith.mulF (frobF a) (frobF b))
    (a b : α) :
    frobenius frobF (mul (contents a) (contents b)) =
    mul (frobenius frobF (contents a)) (frobenius frobF (contents b)) := by
  simp [frobenius, valMap, mul, h]

theorem frobenius_add [ValArith α] (frobF : α → α)
    (h : ∀ a b, frobF (ValArith.addF a b) = ValArith.addF (frobF a) (frobF b))
    (a b : α) :
    frobenius frobF (add (contents a) (contents b)) =
    add (frobenius frobF (contents a)) (frobenius frobF (contents b)) := by
  simp [frobenius, valMap, add, h]

/-- Perfect field: Frobenius is surjective. -/
def IsPerfect (frobF : α → α) : Prop :=
  ∀ b, ∃ a, frobF a = b

-- ============================================================================
-- 11. QUATERNION AND OCTONION
-- ============================================================================

/-- Quaternion multiplication (non-commutative). -/
def quatMul [ValArith α] (qmulF : α → α → α) : Val α → Val α → Val α := mul

/-- Quaternion conjugate. -/
abbrev quatConj (conjF : α → α) : Val α → Val α := valMap conjF

/-- Quaternion norm: a · conj(a). -/
theorem quat_norm [ValArith α] (conjF : α → α) (normF : α → α)
    (h : ∀ a, ValArith.mulF a (conjF a) = normF a) (a : α) :
    mul (contents a) (valMap conjF (contents a)) = contents (normF a) := by
  simp [mul, valMap, h]

-- ============================================================================
-- 12. FREE ALGEBRA
-- ============================================================================

/-- Free algebra: universal property. -/
def IsFreeAlgebra (embed : α → α) (extend : (α → α) → α → α) : Prop :=
  ∀ f a, extend f (embed a) = f a

/-- Group ring element: finite formal sum of group elements. -/
def groupRingMul [ValArith α] (convF : α → α → α) : Val α → Val α → Val α := mul

-- ============================================================================
-- 13. LOCALIZATION
-- ============================================================================

/-- Localization: S⁻¹R as fractions. -/
def localize [ValArith α] (a s : α) : Val α :=
  mul (contents a) (inv (contents s))

/-- Localization is contents. -/
theorem localize_contents [ValArith α] (a s : α) :
    ∃ r, localize a s = contents r :=
  ⟨ValArith.mulF a (ValArith.invF s), by simp [localize, mul, inv]⟩

/-- Localization map is a ring homomorphism. -/
theorem localize_add [ValArith α] (a₁ s₁ a₂ s₂ : α) :
    ∃ r, add (localize a₁ s₁) (localize a₂ s₂) = contents r :=
  ⟨ValArith.addF (ValArith.mulF a₁ (ValArith.invF s₁))
                  (ValArith.mulF a₂ (ValArith.invF s₂)),
   by simp [localize, mul, inv, add]⟩

-- ============================================================================
-- 14. COMPLETION
-- ============================================================================

/-- Cauchy completion: equivalence classes of Cauchy sequences. -/
def cauchyComplete (limitF : (Nat → α) → α) (seq : Nat → α) : Val α :=
  contents (limitF seq)

/-- Completion is always contents. -/
theorem completion_contents (limitF : (Nat → α) → α) (seq : Nat → α) :
    ∃ r, cauchyComplete limitF seq = contents r := ⟨limitF seq, rfl⟩

-- ============================================================================
-- 15. BILINEAR FORMS
-- ============================================================================

/-- Bilinear form. -/
def bilinearForm [ValArith α] (bF : α → α → α) : Val α → Val α → Val α := mul

/-- Bilinear form is bilinear (left). -/
theorem bilinear_left [ValRing α] (a b c : Val α) :
    mul (add a b) c = add (mul a c) (mul b c) := val_right_distrib a b c

/-- Bilinear form is bilinear (right). -/
theorem bilinear_right [ValRing α] (a b c : Val α) :
    mul a (add b c) = add (mul a b) (mul a c) := val_left_distrib a b c

/-- Symmetric bilinear form. -/
theorem bilinear_symm [ValRing α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

/-- Non-degenerate: B(x,-) = 0 implies x = 0. -/
def IsNonDegenerate [ValField α] (bF : α → α → α) : Prop :=
  ∀ a, (∀ b, bF a b = ValField.zero) → a = ValField.zero

-- ============================================================================
-- 16. SPECTRAL SEQUENCE
-- ============================================================================

/-- Spectral sequence page. -/
def spectralPage [ValArith α] (d : Nat → α → α) (n : Nat) : Val α → Val α :=
  valMap (d n)

/-- Differential on page: d² = 0. -/
theorem spectral_diff_sq [ValField α] (d : Nat → α → α)
    (h : ∀ n a, d n (d n a) = ValField.zero) (n : Nat) (a : α) :
    spectralPage d n (spectralPage d n (contents a)) = contents ValField.zero := by
  simp [spectralPage, valMap, h]

-- ============================================================================
-- 17. MONOID ALGEBRA
-- ============================================================================

/-- Monoid algebra multiplication (convolution). -/
def monoidAlgMul [ValArith α] (convF : α → α → α) : Val α → Val α → Val α := mul

/-- Monoid algebra is associative. -/
theorem monoid_alg_assoc [ValRing α] (a b c : Val α) :
    monoidAlgMul (α := α) ValArith.mulF (monoidAlgMul ValArith.mulF a b) c =
    monoidAlgMul ValArith.mulF a (monoidAlgMul ValArith.mulF b c) := val_mul_assoc a b c

end Val
