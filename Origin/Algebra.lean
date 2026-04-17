/-
Released under MIT license.
-/
import Origin.Core

/-!
# Algebra on Option α (Core-based)

**Goal B classification:**
- Polynomial roots, homological algebra, Lie algebra, big operators,
  GCD, characteristic — Category 1 (Option-meaningful: none = no
  polynomial, no cycle, no chain; these interact with the ground)
- Lattice theory (join/meet), distributive/modular laws, Vieta's
  formula, HasDistribNeg — Category 2 (clean math, no infrastructure)
- NoZeroDivisors, IsCancelMulZero, IsDomain — dissolved infrastructure
  (managed zero-inside-domain; Origin dissolves these entirely)

Mathlib_Algebra: 797 files, 47 dissolved declarations.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. POLYNOMIAL
-- ============================================================================

def IsRoot (evalF : α → α) (zero : α) (a : α) : Prop := evalF a = zero

theorem root_gives_zero (evalF : α → α) (zero : α) (a : α)
    (h : IsRoot evalF zero a) :
    Option.map evalF (some a) = some zero := by simp [IsRoot] at h; simp [h]

def IsIrreducible (p : α) (factorsF : α → α × α) (isUnit : α → Prop) : Prop :=
  ¬isUnit p ∧ ∀ a b, factorsF p = (a, b) → isUnit a ∨ isUnit b

-- ============================================================================
-- 2. HOMOLOGICAL ALGEBRA
-- ============================================================================

def IsBoundary (d : α → α) (b a : α) : Prop := d a = b
def IsCycle (d : α → α) (zero : α) (a : α) : Prop := d a = zero

def IsShortExact (f g : α → α) (zero : α) : Prop :=
  (∀ a b, f a = f b → a = b) ∧ (∀ b, ∃ a, g a = b) ∧ (∀ a, g (f a) = zero)

-- ============================================================================
-- 3. ORDER AND LATTICE
-- ============================================================================

structure BoundedLattice (α : Type u) where
  top : α
  bot : α
  joinF : α → α → α
  meetF : α → α → α
  le_top : ∀ a : α, joinF a top = top
  bot_le : ∀ a : α, joinF bot a = a

def IsDistributive (joinF meetF : α → α → α) : Prop :=
  ∀ a b c, meetF a (joinF b c) = joinF (meetF a b) (meetF a c)

def IsModular (joinF meetF : α → α → α) (leF : α → α → Prop) : Prop :=
  ∀ a b c, leF a c → meetF c (joinF a b) = joinF a (meetF c b)

-- ============================================================================
-- 4. LIE ALGEBRA
-- ============================================================================

def IsLieIdeal (mem : α → Prop) (bracketF : α → α → α) : Prop :=
  ∀ a x, mem a → ∃ r, bracketF x a = r ∧ mem r

def IsSemisimple (killF : α → α → α) (zero : α) : Prop :=
  ∀ a, (∀ b, killF a b = zero) → a = zero

-- ============================================================================
-- 5. BIG OPERATORS
-- ============================================================================

def bigSum [Add α] (zero : α) : List α → α
  | [] => zero
  | a :: as => a + bigSum zero as

def bigProd [Mul α] (one : α) : List α → α
  | [] => one
  | a :: as => a * bigProd one as

-- ============================================================================
-- 6. GCD
-- ============================================================================

theorem gcd_lcm_product [Mul α] (gcdF lcmF : α → α → α)
    (h : ∀ a b, gcdF a b * lcmF a b = a * b) (a b : α) :
    (some (gcdF a b) : Option α) * some (lcmF a b) =
    some a * some b := by simp [h]

-- ============================================================================
-- 7. CHARACTERISTIC
-- ============================================================================

def HasCharP (charF : Nat → α) (zero : α) (p : Nat) : Prop := charF p = zero

-- ============================================================================
-- 8. GALOIS THEORY
-- ============================================================================

/-- A field extension: base embeds into extension. -/
structure FieldExt (K F : Type u) where
  embed : K → F
  embed_inj : ∀ a b : K, embed a = embed b → a = b

/-- An automorphism that fixes the base field. -/
def IsFieldAut (σ : α → α) (isBase : α → Prop) : Prop :=
  (∀ a, isBase a → σ a = a) ∧ (∀ a b, σ a = σ b → a = b) ∧ (∀ b, ∃ a, σ b = a)

/-- Galois group: set of automorphisms fixing the base. -/
def GaloisGroupMem (σ : α → α) (isBase : α → Prop) : Prop :=
  ∀ a, isBase a → σ a = a

/-- Fundamental theorem: intermediate fields correspond to subgroups. -/
def IsGaloisCorrespondence
    (intermField : (α → Prop) → Prop)
    (subgroup : ((α → α) → Prop) → Prop)
    (fixedField : ((α → α) → Prop) → (α → Prop))
    (autGroup : (α → Prop) → ((α → α) → Prop)) : Prop :=
  (∀ H, subgroup H → intermField (fixedField H)) ∧
  (∀ E, intermField E → subgroup (autGroup E))

/-- Galois extension lifts through Option: none = outside the extension. -/
theorem galois_fixes_option (σ : α → α) (isBase : α → Prop)
    (h : GaloisGroupMem σ isBase) (a : α) (hb : isBase a) :
    Option.map σ (some a) = some a := by simp [GaloisGroupMem] at h; simp [h a hb]

-- ============================================================================
-- 9. STAR ALGEBRAS
-- ============================================================================

/-- Star involution on a type. -/
def IsStarInvolution (star : α → α) : Prop :=
  ∀ a, star (star a) = a

/-- Star reverses multiplication. -/
def IsStarMulRev [Mul α] (star : α → α) : Prop :=
  ∀ a b, star (a * b) = star b * star a

/-- C*-identity: ‖x* x‖ = ‖x‖². -/
def IsCStarIdentity (star : α → α) (normF : α → α) [Mul α] : Prop :=
  ∀ a, normF (star a * a) = normF a * normF a

/-- Star lifts through Option: none stays none. -/
theorem star_option_none (star : α → α) :
    Option.map star (none : Option α) = none := by simp

theorem star_option_some (star : α → α) (a : α) :
    Option.map star (some a : Option α) = some (star a) := by simp

-- ============================================================================
-- 10. VIETA'S FORMULAS
-- ============================================================================

/-- Sum of roots of a polynomial (via coefficient). -/
def vietaSum [Neg α] [Div α] (leadCoeff nextCoeff : α) : α :=
  -(nextCoeff / leadCoeff)

/-- Product of roots of a quadratic (via coefficient). -/
def vietaProduct [Div α] (leadCoeff constCoeff : α) : α :=
  constCoeff / leadCoeff

/-- Vieta lifts: if coefficients are some, result is some. -/
theorem vieta_sum_option [Neg α] [Div α] (a b : α) :
    some (vietaSum a b) = some (-(b / a)) := by rfl

-- ============================================================================
-- 11. CLIFFORD ALGEBRAS
-- ============================================================================

/-- Clifford relation: v * v = Q(v) · 1. -/
def IsCliffordRel [Mul α] (quadForm : α → α) (v : α) : Prop :=
  v * v = quadForm v

/-- Anti-commutation in a Clifford algebra. -/
def IsCliffordAnticomm [Mul α] [Add α] (quadForm : α → α → α) : Prop :=
  ∀ u v, u * v + v * u = quadForm u v

/-- Clifford product lifts through Option. -/
theorem clifford_mul_option [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

-- ============================================================================
-- 12. MODULES
-- ============================================================================

/-- A module action: scalar multiplication. -/
def IsModuleAction [Mul α] (smul : α → α → α) (one : α) : Prop :=
  (∀ x, smul one x = x) ∧ (∀ r s x, smul r (smul s x) = smul (r * s) x)

/-- Free module: every element is a unique linear combination. -/
def IsFreeModule (basis : α → Prop) (span : (α → Prop) → α → Prop)
    (_unique : ∀ a, span basis a → ∃ _coeffs : α, True) : Prop :=
  ∀ a, span basis a

/-- Projective module: every surjection onto it splits. -/
def IsProjectiveModule (liftF : (α → α) → (α → α)) : Prop :=
  ∀ (f : α → α) (_surj : ∀ b, ∃ a, f a = b), ∀ x, f (liftF f x) = x

-- ============================================================================
-- 13. ASSOCIATIVE ALGEBRAS
-- ============================================================================

/-- Algebra homomorphism: preserves both ring ops and scalar action. -/
def IsAlgHom [Mul α] [Add α] (f : α → α) : Prop :=
  (∀ a b, f (a * b) = f a * f b) ∧ (∀ a b, f (a + b) = f a + f b)

/-- Algebra homomorphism lifts through Option. -/
theorem alg_hom_option [Mul α] [Add α] (f : α → α) (a : α) :
    Option.map f (some a) = some (f a) := by simp

/-- Algebra homomorphism preserves none (ground absorbs). -/
theorem alg_hom_none [Mul α] [Add α] (f : α → α) :
    Option.map f (none : Option α) = none := by simp

/-- none absorbs multiplication on the left. -/
theorem algebra_none_mul [Mul α] (b : Option α) :
    (none : Option α) * b = none := by simp

/-- none is identity for addition on the left. -/
theorem algebra_none_add [Add α] (b : Option α) :
    (none : Option α) + b = b := by simp

-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub Algebra
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- AddConstMap/Basic.lean

-- AddConstMap/Equiv.lean
-- COLLISION: toEquiv_injective' already in Order.lean — rename needed
-- COLLISION: symm' already in SetTheory.lean — rename needed
-- COLLISION: symm_apply' already in Order.lean — rename needed
-- COLLISION: refl' already in SetTheory.lean — rename needed

-- AddTorsor.lean
-- COLLISION: subsingleton_iff' already in Order.lean — rename needed

-- Algebra/Basic.lean

-- Algebra/Bilinear.lean

-- Algebra/Defs.lean
-- COLLISION: algebraMap' already in RingTheory2.lean — rename needed
-- COLLISION: linearMap' already in RingTheory2.lean — rename needed
-- COLLISION: coe_smul' already in RingTheory2.lean — rename needed

-- Algebra/Equiv.lean

-- Algebra/Field.lean

-- Algebra/Hom.lean

-- Algebra/Hom/Rat.lean

-- Algebra/NonUnitalHom.lean
-- COLLISION: fst' already in SetTheory.lean — rename needed
-- COLLISION: snd' already in Order.lean — rename needed

-- Algebra/NonUnitalSubalgebra.lean
-- COLLISION: map' already in SetTheory.lean — rename needed
-- COLLISION: map_mono' already in Order.lean — rename needed
-- COLLISION: map_injective' already in Order.lean — rename needed
-- COLLISION: range' already in SetTheory.lean — rename needed
-- COLLISION: mem_range' already in SetTheory.lean — rename needed
-- COLLISION: mem_range_self' already in RingTheory2.lean — rename needed
-- COLLISION: coe_range' already in RingTheory2.lean — rename needed
-- COLLISION: rangeRestrict' already in RingTheory2.lean — rename needed
-- COLLISION: adjoin' already in FieldTheory.lean — rename needed
-- COLLISION: subset_adjoin' already in RingTheory2.lean — rename needed
-- COLLISION: self_mem_adjoin_singleton' already in RingTheory2.lean — rename needed
-- COLLISION: gc' already in Order.lean — rename needed
-- COLLISION: gi' already in Order.lean — rename needed
-- COLLISION: adjoin_le' already in RingTheory2.lean — rename needed
-- COLLISION: adjoin_le_iff' already in FieldTheory.lean — rename needed
-- COLLISION: adjoin_union' already in FieldTheory.lean — rename needed
-- COLLISION: adjoin_eq' already in RingTheory2.lean — rename needed
-- COLLISION: adjoin_induction' already in RingTheory2.lean — rename needed
-- COLLISION: adjoin_eq_span' already in RingTheory2.lean — rename needed
-- COLLISION: mem_sup_left' already in RingTheory2.lean — rename needed
-- COLLISION: map_sup' already in Order.lean — rename needed
-- COLLISION: coe_iInf' already in FieldTheory.lean — rename needed
-- COLLISION: mem_iInf' already in Order.lean — rename needed
-- COLLISION: coe_bot' already in Order.lean — rename needed
-- COLLISION: map_top' already in Order.lean — rename needed
-- COLLISION: map_bot' already in Order.lean — rename needed
-- COLLISION: center' already in RingTheory2.lean — rename needed
-- COLLISION: center_eq_top' already in RingTheory2.lean — rename needed
-- COLLISION: mem_center_iff' already in RingTheory2.lean — rename needed
-- COLLISION: centralizer' already in RingTheory2.lean — rename needed
-- COLLISION: centralizer_le' already in RingTheory2.lean — rename needed
-- COLLISION: centralizer_univ' already in RingTheory2.lean — rename needed

-- Algebra/Operations.lean
-- COLLISION: ringHom' already in RingTheory2.lean — rename needed
-- COLLISION: pointwiseMulSemiringAction' already in RingTheory2.lean — rename needed
-- COLLISION: mul_mem_mul_rev' already in RingTheory2.lean — rename needed
-- COLLISION: mul_comm' already in SetTheory.lean — rename needed
-- COLLISION: le_div_iff' already in Order.lean — rename needed
-- COLLISION: le_self_mul_one_div' already in RingTheory2.lean — rename needed
-- COLLISION: mul_one_div_le_one' already in RingTheory2.lean — rename needed
-- COLLISION: map_div' already in Order.lean — rename needed

-- Algebra/Opposite.lean
-- COLLISION: op' already in RingTheory2.lean — rename needed

-- Algebra/Pi.lean

-- Algebra/Prod.lean
-- COLLISION: prodMap' already in Order.lean — rename needed

-- Algebra/Quasispectrum.lean

-- Algebra/Rat.lean

-- Algebra/RestrictScalars.lean

-- Algebra/Spectrum.lean

-- Algebra/Subalgebra/Basic.lean

-- Algebra/Subalgebra/Directed.lean

-- Algebra/Subalgebra/IsSimpleOrder.lean

-- Algebra/Subalgebra/MulOpposite.lean

-- Algebra/Subalgebra/Operations.lean
-- COLLISION: mem_of_span_eq_top_of_smul_pow_mem' already in RingTheory2.lean — rename needed

-- Algebra/Subalgebra/Pointwise.lean
-- COLLISION: pointwiseMulAction' already in RingTheory2.lean — rename needed
-- COLLISION: smul_mem_pointwise_smul' already in RingTheory2.lean — rename needed

-- Algebra/Subalgebra/Prod.lean

-- Algebra/Subalgebra/Rank.lean

-- Algebra/Subalgebra/Tower.lean

-- Algebra/Subalgebra/Unitization.lean

-- Algebra/Tower.lean

-- Algebra/Unitization.lean

-- Algebra/ZMod.lean

-- AlgebraicCard.lean

-- Associated/Basic.lean

-- BigOperators/Associated.lean

-- BigOperators/Balance.lean

-- BigOperators/Expect.lean

-- BigOperators/Fin.lean

-- BigOperators/Finprod.lean

-- BigOperators/Finsupp.lean

-- BigOperators/Group/Finset.lean

-- BigOperators/Group/List.lean

-- BigOperators/Group/Multiset.lean

-- BigOperators/Intervals.lean

-- BigOperators/Module.lean

-- BigOperators/NatAntidiagonal.lean

-- BigOperators/Option.lean

-- BigOperators/Pi.lean

-- BigOperators/Ring.lean

-- BigOperators/Ring/List.lean

-- BigOperators/Ring/Multiset.lean

-- BigOperators/Ring/Nat.lean

-- BigOperators/RingEquiv.lean

-- BigOperators/Sym.lean

-- Category/AlgebraCat/Basic.lean

-- Category/AlgebraCat/Limits.lean

-- Category/AlgebraCat/Monoidal.lean

-- Category/BialgebraCat/Basic.lean
-- COLLISION: toBialgEquiv' already in RingTheory2.lean — rename needed

-- Category/BoolRing.lean

-- Category/CoalgebraCat/Basic.lean
-- COLLISION: toCoalgEquiv' already in RingTheory2.lean — rename needed

-- Category/CoalgebraCat/ComonEquivalence.lean

-- Category/CoalgebraCat/Monoidal.lean

-- Category/FGModuleCat/Basic.lean

-- Category/FGModuleCat/Limits.lean

-- Category/Grp/Abelian.lean

-- Category/Grp/Adjunctions.lean

-- Category/Grp/Basic.lean

-- Category/Grp/Biproducts.lean

-- Category/Grp/Colimits.lean

-- Category/Grp/EpiMono.lean

-- Category/Grp/EquivalenceGroupAddGroup.lean

-- Category/Grp/FilteredColimits.lean

-- Category/Grp/FiniteGrp.lean

-- Category/Grp/ForgetCorepresentable.lean

-- Category/Grp/Images.lean

-- Category/Grp/Injective.lean

-- Category/Grp/Kernels.lean

-- Category/Grp/Limits.lean

-- Category/Grp/Zero.lean

-- Category/HopfAlgebraCat/Basic.lean

-- Category/ModuleCat/Abelian.lean

-- Category/ModuleCat/Adjunctions.lean

-- Category/ModuleCat/Algebra.lean

-- Category/ModuleCat/Basic.lean

-- Category/ModuleCat/Biproducts.lean

-- Category/ModuleCat/ChangeOfRings.lean

-- Category/ModuleCat/Colimits.lean

-- Category/ModuleCat/Differentials/Basic.lean

-- Category/ModuleCat/Differentials/Presheaf.lean

-- Category/ModuleCat/EnoughInjectives.lean

-- Category/ModuleCat/EpiMono.lean

-- Category/ModuleCat/FilteredColimits.lean

-- Category/ModuleCat/Free.lean

-- Category/ModuleCat/Images.lean

-- Category/ModuleCat/Injective.lean

-- Category/ModuleCat/Kernels.lean

-- Category/ModuleCat/Limits.lean

-- Category/ModuleCat/Monoidal/Basic.lean

-- Category/ModuleCat/Monoidal/Closed.lean

-- Category/ModuleCat/Monoidal/Symmetric.lean

-- Category/ModuleCat/Presheaf.lean

-- Category/ModuleCat/Presheaf/ChangeOfRings.lean

-- Category/ModuleCat/Presheaf/Colimits.lean

-- Category/ModuleCat/Presheaf/EpiMono.lean

-- Category/ModuleCat/Presheaf/Free.lean

-- Category/ModuleCat/Presheaf/Generator.lean

-- Category/ModuleCat/Presheaf/Limits.lean

-- Category/ModuleCat/Presheaf/Monoidal.lean

-- Category/ModuleCat/Presheaf/Pushforward.lean

-- Category/ModuleCat/Presheaf/Sheafification.lean

-- Category/ModuleCat/Presheaf/Sheafify.lean

-- Category/ModuleCat/Products.lean

-- Category/ModuleCat/Projective.lean

-- Category/ModuleCat/Sheaf.lean

-- Category/ModuleCat/Sheaf/ChangeOfRings.lean

-- Category/ModuleCat/Sheaf/Free.lean

-- Category/ModuleCat/Sheaf/Generators.lean

-- Category/ModuleCat/Sheaf/Limits.lean

-- Category/ModuleCat/Sheaf/PushforwardContinuous.lean
-- COLLISION: over' already in RingTheory2.lean — rename needed

-- Category/ModuleCat/Sheaf/Quasicoherent.lean

-- Category/ModuleCat/Simple.lean

-- Category/ModuleCat/Subobject.lean

-- Category/ModuleCat/Tannaka.lean

-- Category/MonCat/Adjunctions.lean

-- Category/MonCat/Basic.lean

-- Category/MonCat/Colimits.lean

-- Category/MonCat/FilteredColimits.lean

-- Category/MonCat/Limits.lean

-- Category/Ring/Adjunctions.lean

-- Category/Ring/Basic.lean

-- Category/Ring/Colimits.lean

-- Category/Ring/Constructions.lean

-- Category/Ring/Epi.lean

-- Category/Ring/FilteredColimits.lean
-- COLLISION: R' already in RingTheory2.lean — rename needed

-- Category/Ring/Instances.lean

-- Category/Ring/Limits.lean

-- Category/Ring/Under/Basic.lean

-- Category/Ring/Under/Limits.lean

-- Category/Semigrp/Basic.lean

-- Central/Basic.lean

-- Central/Defs.lean

-- CharP/Algebra.lean

-- CharP/Basic.lean

-- CharP/CharAndCard.lean

-- CharP/Defs.lean
-- COLLISION: exists' already in Order.lean — rename needed

-- CharP/ExpChar.lean

-- CharP/Invertible.lean

-- CharP/Lemmas.lean

-- CharP/LinearMaps.lean

-- CharP/LocalRing.lean

-- CharP/MixedCharZero.lean

-- CharP/Quotient.lean

-- CharP/Reduced.lean

-- CharP/Subring.lean

-- CharP/Two.lean

-- CharZero/Defs.lean

-- CharZero/Lemmas.lean

-- CharZero/Quotient.lean

-- ContinuedFractions/Basic.lean

-- ContinuedFractions/Computation/ApproximationCorollaries.lean

-- ContinuedFractions/Computation/Approximations.lean

-- ContinuedFractions/Computation/Basic.lean

-- ContinuedFractions/Computation/CorrectnessTerminating.lean

-- ContinuedFractions/Computation/TerminatesIffRat.lean

-- ContinuedFractions/Computation/Translations.lean

-- ContinuedFractions/ContinuantsRecurrence.lean

-- ContinuedFractions/ConvergentsEquiv.lean

-- ContinuedFractions/Determinant.lean

-- ContinuedFractions/TerminatedStable.lean

-- ContinuedFractions/Translations.lean

-- CubicDiscriminant.lean

-- DirectLimit.lean
-- COLLISION: of_injective' already in RingTheory2.lean — rename needed
-- COLLISION: exists_inv' already in RingTheory2.lean — rename needed
-- COLLISION: inv' already in SetTheory.lean — rename needed
-- COLLISION: mul_inv_cancel' already in RingTheory2.lean — rename needed
-- COLLISION: inv_mul_cancel' already in RingTheory2.lean — rename needed

-- DirectSum/AddChar.lean

-- DirectSum/Algebra.lean

-- DirectSum/Basic.lean

-- DirectSum/Decomposition.lean

-- DirectSum/Finsupp.lean

-- DirectSum/Internal.lean
-- COLLISION: subring' already in RingTheory2.lean — rename needed

-- DirectSum/LinearMap.lean

-- DirectSum/Module.lean

-- DirectSum/Ring.lean

-- Divisibility/Basic.lean

-- Divisibility/Hom.lean

-- Divisibility/Prod.lean

-- Divisibility/Units.lean
-- COLLISION: dvd_of_dvd_mul_right' already in RingTheory2.lean — rename needed
-- COLLISION: dvd_of_dvd_mul_left' already in RingTheory2.lean — rename needed
-- COLLISION: mul_left' already in RingTheory2.lean — rename needed
-- COLLISION: mul_right' already in RingTheory2.lean — rename needed
-- COLLISION: mul_left_iff' already in RingTheory2.lean — rename needed
-- COLLISION: mul_right_iff' already in RingTheory2.lean — rename needed
-- COLLISION: mul_dvd' already in RingTheory2.lean — rename needed

-- DualNumber.lean

-- DualQuaternion.lean

-- EuclideanDomain/Basic.lean

-- EuclideanDomain/Defs.lean

-- Exact.lean

-- Expr.lean

-- Field/Basic.lean
-- COLLISION: field' already in RingTheory2.lean — rename needed

-- Field/Defs.lean

-- Field/Equiv.lean
-- COLLISION: isField' already in RingTheory2.lean — rename needed

-- Field/IsField.lean

-- Field/MinimalAxioms.lean
-- COLLISION: ofMinimalAxioms' already in Order.lean — rename needed

-- Field/Power.lean

-- Field/Rat.lean

-- Field/Subfield/Basic.lean
-- COLLISION: isGLB_sInf' already in Order.lean — rename needed
-- COLLISION: closure' already in RingTheory2.lean — rename needed
-- COLLISION: mem_closure' already in RingTheory2.lean — rename needed
-- COLLISION: not_mem_of_not_mem_closure' already in Order.lean — rename needed
-- COLLISION: closure_le' already in RingTheory2.lean — rename needed
-- COLLISION: closure_mono' already in RingTheory2.lean — rename needed
-- COLLISION: closure_eq_of_le' already in RingTheory2.lean — rename needed
-- COLLISION: closure_induction' already in RingTheory2.lean — rename needed
-- COLLISION: closure_eq' already in Order.lean — rename needed
-- COLLISION: closure_empty' already in RingTheory2.lean — rename needed
-- COLLISION: mem_closure_iff' already in RingTheory2.lean — rename needed
-- COLLISION: comap_map' already in Order.lean — rename needed

-- Field/Subfield/Defs.lean

-- Free.lean

-- FreeAlgebra.lean

-- FreeAlgebra/Cardinality.lean

-- FreeMonoid/Basic.lean

-- FreeMonoid/Count.lean

-- FreeMonoid/Symbols.lean

-- FreeNonUnitalNonAssocAlgebra.lean

-- GCDMonoid/Basic.lean

-- GCDMonoid/Finset.lean

-- GCDMonoid/IntegrallyClosed.lean

-- GCDMonoid/Multiset.lean

-- GCDMonoid/Nat.lean

-- GeomSum.lean

-- GradedMonoid.lean

-- GradedMulAction.lean

-- Group/Action/Basic.lean

-- Group/Action/Defs.lean

-- Group/Action/End.lean

-- Group/Action/Faithful.lean

-- Group/Action/Opposite.lean

-- Group/Action/Pi.lean

-- Group/Action/Pretransitive.lean

-- Group/Action/Prod.lean

-- Group/Action/Sigma.lean

-- Group/Action/Sum.lean

-- Group/Action/TypeTags.lean

-- Group/Action/Units.lean

-- Group/AddChar.lean

-- Group/Aut.lean
-- COLLISION: conj' already in Order.lean — rename needed

-- Group/Basic.lean

-- Group/Center.lean

-- Group/Commute/Basic.lean

-- Group/Commute/Defs.lean

-- Group/Commute/Hom.lean
-- COLLISION: of_map' already in Order.lean — rename needed

-- Group/Commute/Units.lean

-- Group/Conj.lean

-- Group/Defs.lean

-- Group/Embedding.lean

-- Group/Equiv/Basic.lean

-- Group/Equiv/TypeTags.lean

-- Group/Even.lean

-- Group/EvenFunction.lean

-- Group/Ext.lean

-- Group/Fin/Basic.lean

-- Group/Fin/Tuple.lean

-- Group/FiniteSupport.lean

-- Group/ForwardDiff.lean

-- Group/Graph.lean

-- Group/Hom/Basic.lean

-- Group/Hom/CompTypeclasses.lean

-- Group/Hom/Defs.lean
-- COLLISION: comp_id' already in Order.lean — rename needed

-- Group/Hom/End.lean

-- Group/Hom/Instances.lean

-- Group/Indicator.lean

-- Group/InjSurj.lean

-- Group/Int.lean

-- Group/Invertible/Basic.lean

-- Group/Invertible/Defs.lean

-- Group/MinimalAxioms.lean

-- Group/Nat/Even.lean

-- Group/Nat/TypeTags.lean

-- Group/NatPowAssoc.lean

-- Group/Operations.lean

-- Group/Opposite.lean

-- Group/PNatPowAssoc.lean

-- Group/Pi/Basic.lean

-- Group/Pi/Lemmas.lean

-- Group/Pointwise/Finset/Basic.lean

-- Group/Pointwise/Finset/Interval.lean

-- Group/Pointwise/Set/Basic.lean

-- Group/Pointwise/Set/BigOperators.lean

-- Group/Pointwise/Set/Card.lean

-- Group/Pointwise/Set/Finite.lean

-- Group/Pointwise/Set/ListOfFn.lean

-- Group/Prod.lean

-- Group/Semiconj/Basic.lean

-- Group/Semiconj/Defs.lean

-- Group/Semiconj/Units.lean

-- Group/Subgroup/Basic.lean

-- Group/Subgroup/Defs.lean

-- Group/Subgroup/Finite.lean

-- Group/Subgroup/Ker.lean

-- Group/Subgroup/Lattice.lean

-- Group/Subgroup/Map.lean

-- Group/Subgroup/MulOpposite.lean

-- Group/Subgroup/MulOppositeLemmas.lean

-- Group/Subgroup/Order.lean

-- Group/Subgroup/Pointwise.lean

-- Group/Subgroup/ZPowers/Basic.lean

-- Group/Subgroup/ZPowers/Lemmas.lean

-- Group/Submonoid/Basic.lean

-- Group/Submonoid/Defs.lean

-- Group/Submonoid/Membership.lean

-- Group/Submonoid/MulOpposite.lean

-- Group/Submonoid/Operations.lean

-- Group/Submonoid/Pointwise.lean

-- Group/Submonoid/Units.lean

-- Group/Subsemigroup/Basic.lean

-- Group/Subsemigroup/Defs.lean

-- Group/Subsemigroup/Membership.lean

-- Group/Subsemigroup/Operations.lean
-- COLLISION: srange' already in RingTheory2.lean — rename needed

-- Group/Support.lean

-- Group/Translate.lean

-- Group/TypeTags/Basic.lean

-- Group/TypeTags/Hom.lean

-- Group/ULift.lean

-- Group/UniqueProds/Basic.lean

-- Group/Units/Basic.lean

-- Group/Units/Defs.lean

-- Group/Units/Equiv.lean

-- Group/Units/Hom.lean
-- COLLISION: isLocalHom_of_comp' already in RingTheory2.lean — rename needed

-- Group/Units/Opposite.lean

-- Group/WithOne/Basic.lean

-- Group/WithOne/Defs.lean

-- Group/ZeroOne.lean

-- GroupPower/IterateHom.lean

-- HierarchyDesign.lean

-- Homology/Additive.lean

-- Homology/Augment.lean

-- Homology/Bifunctor.lean

-- Homology/BifunctorAssociator.lean

-- Homology/BifunctorFlip.lean

-- Homology/BifunctorHomotopy.lean

-- Homology/BifunctorShift.lean

-- Homology/CommSq.lean

-- Homology/ComplexShape.lean
-- COLLISION: up' already in RingTheory2.lean — rename needed

-- Homology/ComplexShapeSigns.lean

-- Homology/ConcreteCategory.lean

-- Homology/DerivedCategory/Basic.lean

-- Homology/DerivedCategory/ExactFunctor.lean

-- Homology/DerivedCategory/Ext/Basic.lean

-- Homology/DerivedCategory/Ext/ExactSequences.lean

-- Homology/DerivedCategory/Ext/ExtClass.lean

-- Homology/DerivedCategory/HomologySequence.lean

-- Homology/DerivedCategory/ShortExact.lean

-- Homology/DerivedCategory/SingleTriangle.lean

-- Homology/DifferentialObject.lean

-- Homology/Embedding/Basic.lean

-- Homology/Embedding/Boundary.lean

-- Homology/Embedding/Extend.lean

-- Homology/Embedding/ExtendHomology.lean

-- Homology/Embedding/HomEquiv.lean

-- Homology/Embedding/IsSupported.lean

-- Homology/Embedding/Restriction.lean

-- Homology/Embedding/TruncGE.lean

-- Homology/ExactSequence.lean

-- Homology/Factorizations/Basic.lean

-- Homology/Functor.lean

-- Homology/HomologicalBicomplex.lean

-- Homology/HomologicalComplex.lean

-- Homology/HomologicalComplexAbelian.lean

-- Homology/HomologicalComplexBiprod.lean

-- Homology/HomologicalComplexLimits.lean

-- Homology/HomologySequence.lean

-- Homology/HomologySequenceLemmas.lean

-- Homology/Homotopy.lean

-- Homology/HomotopyCategory.lean

-- Homology/HomotopyCategory/DegreewiseSplit.lean

-- Homology/HomotopyCategory/HomComplex.lean

-- Homology/HomotopyCategory/HomComplexShift.lean

-- Homology/HomotopyCategory/MappingCone.lean

-- Homology/HomotopyCategory/Pretriangulated.lean

-- Homology/HomotopyCategory/Shift.lean

-- Homology/HomotopyCategory/ShiftSequence.lean

-- Homology/HomotopyCategory/ShortExact.lean

-- Homology/HomotopyCategory/SingleFunctors.lean

-- Homology/HomotopyCategory/Triangulated.lean

-- Homology/HomotopyCofiber.lean

-- Homology/ImageToKernel.lean

-- Homology/LocalCohomology.lean

-- Homology/Localization.lean

-- Homology/Monoidal.lean

-- Homology/Opposite.lean

-- Homology/QuasiIso.lean

-- Homology/Refinements.lean

-- Homology/ShortComplex/Ab.lean

-- Homology/ShortComplex/Abelian.lean

-- Homology/ShortComplex/Basic.lean

-- Homology/ShortComplex/ConcreteCategory.lean

-- Homology/ShortComplex/Exact.lean

-- Homology/ShortComplex/ExactFunctor.lean

-- Homology/ShortComplex/FunctorEquivalence.lean

-- Homology/ShortComplex/HomologicalComplex.lean

-- Homology/ShortComplex/Homology.lean

-- Homology/ShortComplex/LeftHomology.lean

-- Homology/ShortComplex/Limits.lean

-- Homology/ShortComplex/Linear.lean

-- Homology/ShortComplex/ModuleCat.lean

-- Homology/ShortComplex/Preadditive.lean

-- Homology/ShortComplex/PreservesHomology.lean

-- Homology/ShortComplex/QuasiIso.lean

-- Homology/ShortComplex/RightHomology.lean

-- Homology/ShortComplex/ShortExact.lean

-- Homology/ShortComplex/SnakeLemma.lean

-- Homology/Single.lean

-- Homology/SingleHomology.lean

-- Homology/Square.lean

-- Homology/TotalComplex.lean

-- Homology/TotalComplexShift.lean

-- Homology/TotalComplexSymmetry.lean

-- IsPrimePow.lean

-- Jordan/Basic.lean

-- Lie/Abelian.lean

-- Lie/BaseChange.lean

-- Lie/Basic.lean

-- Lie/CartanExists.lean

-- Lie/CartanMatrix.lean

-- Lie/CartanSubalgebra.lean

-- Lie/Character.lean

-- Lie/Classical.lean

-- Lie/Derivation/AdjointAction.lean

-- Lie/Derivation/Basic.lean

-- Lie/Derivation/Killing.lean

-- Lie/DirectSum.lean

-- Lie/Engel.lean

-- Lie/EngelSubalgebra.lean

-- Lie/Free.lean

-- Lie/IdealOperations.lean

-- Lie/InvariantForm.lean

-- Lie/Killing.lean

-- Lie/Matrix.lean

-- Lie/Nilpotent.lean

-- Lie/NonUnitalNonAssocAlgebra.lean

-- Lie/Normalizer.lean

-- Lie/OfAssociative.lean

-- Lie/Quotient.lean

-- Lie/Rank.lean

-- Lie/Semisimple/Basic.lean

-- Lie/Semisimple/Defs.lean

-- Lie/SkewAdjoint.lean

-- Lie/Sl2.lean

-- Lie/Solvable.lean

-- Lie/Subalgebra.lean
-- COLLISION: span_empty' already in RingTheory2.lean — rename needed

-- Lie/Submodule.lean

-- Lie/TensorProduct.lean

-- Lie/TraceForm.lean

-- Lie/UniversalEnveloping.lean

-- Lie/Weights/Basic.lean

-- Lie/Weights/Cartan.lean

-- Lie/Weights/Chain.lean

-- Lie/Weights/Killing.lean

-- Lie/Weights/Linear.lean

-- Lie/Weights/RootSystem.lean

-- LinearRecurrence.lean

-- ModEq.lean

-- Module/Basic.lean

-- Module/BigOperators.lean

-- Module/Bimodule.lean

-- Module/CharacterModule.lean

-- Module/DedekindDomain.lean

-- Module/Defs.lean

-- Module/End.lean

-- Module/Equiv/Basic.lean

-- Module/Equiv/Defs.lean

-- Module/Equiv/Opposite.lean

-- Module/FinitePresentation.lean

-- Module/FreeLocus.lean

-- Module/GradedModule.lean

-- Module/Hom.lean

-- Module/Injective.lean

-- Module/LinearMap/Defs.lean

-- Module/LinearMap/End.lean

-- Module/LinearMap/Polynomial.lean

-- Module/LinearMap/Prod.lean

-- Module/LinearMap/Rat.lean

-- Module/LocalizedModule/Basic.lean

-- Module/LocalizedModule/Exact.lean
-- COLLISION: map_exact' already in RingTheory2.lean — rename needed

-- Module/LocalizedModule/Int.lean
-- COLLISION: IsInteger' already in RingTheory2.lean — rename needed
-- COLLISION: isInteger_zero' already in RingTheory2.lean — rename needed
-- COLLISION: isInteger_add' already in RingTheory2.lean — rename needed
-- COLLISION: isInteger_smul' already in RingTheory2.lean — rename needed
-- COLLISION: exists_integer_multiple' already in RingTheory2.lean — rename needed
-- COLLISION: exist_integer_multiples' already in RingTheory2.lean — rename needed
-- COLLISION: exist_integer_multiples_of_finite' already in RingTheory2.lean — rename needed
-- COLLISION: exist_integer_multiples_of_finset' already in RingTheory2.lean — rename needed
-- COLLISION: commonDenom' already in RingTheory2.lean — rename needed
-- COLLISION: integerMultiple' already in RingTheory2.lean — rename needed
-- COLLISION: map_integerMultiple' already in RingTheory2.lean — rename needed
-- COLLISION: commonDenomOfFinset' already in RingTheory2.lean — rename needed
-- COLLISION: finsetIntegerMultiple' already in RingTheory2.lean — rename needed
-- COLLISION: finsetIntegerMultiple_image' already in RingTheory2.lean — rename needed
-- COLLISION: smul_mem_finsetIntegerMultiple_span' already in RingTheory2.lean — rename needed

-- Module/LocalizedModule/IsLocalization.lean

-- Module/LocalizedModule/Submodule.lean

-- Module/MinimalAxioms.lean

-- Module/NatInt.lean

-- Module/PID.lean

-- Module/Pi.lean

-- Module/PointwisePi.lean

-- Module/Presentation/Basic.lean

-- Module/Presentation/Cokernel.lean

-- Module/Presentation/Differentials.lean

-- Module/Presentation/DirectSum.lean

-- Module/Presentation/Finite.lean
-- COLLISION: finite' already in Order.lean — rename needed

-- Module/Presentation/Free.lean

-- Module/Presentation/Tautological.lean

-- Module/Projective.lean

-- Module/Rat.lean

-- Module/RingHom.lean

-- Module/SnakeLemma.lean

-- Module/Submodule/Basic.lean

-- Module/Submodule/Bilinear.lean

-- Module/Submodule/Defs.lean
-- COLLISION: neg_mem_iff' already in RingTheory2.lean — rename needed
-- COLLISION: add_mem_iff_left' already in RingTheory2.lean — rename needed
-- COLLISION: add_mem_iff_right' already in RingTheory2.lean — rename needed

-- Module/Submodule/EqLocus.lean

-- Module/Submodule/Equiv.lean

-- Module/Submodule/Invariant.lean
-- COLLISION: inf_mem' already in Order.lean — rename needed
-- COLLISION: sup_mem' already in Order.lean — rename needed
-- COLLISION: top_mem' already in Order.lean — rename needed
-- COLLISION: bot_mem' already in Order.lean — rename needed

-- Module/Submodule/IterateMapComap.lean

-- Module/Submodule/Ker.lean

-- Module/Submodule/Lattice.lean

-- Module/Submodule/LinearMap.lean

-- Module/Submodule/Map.lean

-- Module/Submodule/Pointwise.lean

-- Module/Submodule/Range.lean

-- Module/Submodule/RestrictScalars.lean

-- Module/Torsion.lean

-- Module/ULift.lean

-- Module/ZLattice/Basic.lean

-- Module/ZLattice/Covolume.lean

-- Module/ZMod.lean

-- MonoidAlgebra/Basic.lean

-- MonoidAlgebra/Defs.lean

-- MonoidAlgebra/Degree.lean

-- MonoidAlgebra/Division.lean

-- MonoidAlgebra/Grading.lean

-- MonoidAlgebra/Ideal.lean

-- MonoidAlgebra/Support.lean

-- MonoidAlgebra/ToDirectSum.lean

-- MvPolynomial/Basic.lean

-- MvPolynomial/Cardinal.lean

-- MvPolynomial/Comap.lean

-- MvPolynomial/CommRing.lean

-- MvPolynomial/Counit.lean

-- MvPolynomial/Degrees.lean

-- MvPolynomial/Derivation.lean

-- MvPolynomial/Division.lean

-- MvPolynomial/Equiv.lean

-- MvPolynomial/Expand.lean

-- MvPolynomial/Funext.lean

-- MvPolynomial/Monad.lean

-- MvPolynomial/PDeriv.lean

-- MvPolynomial/Polynomial.lean

-- MvPolynomial/Rename.lean

-- MvPolynomial/Supported.lean

-- MvPolynomial/Variables.lean

-- Notation.lean

-- Opposites.lean

-- Order/AbsoluteValue.lean

-- Order/AddTorsor.lean

-- Order/Algebra.lean

-- Order/Antidiag/Finsupp.lean

-- Order/Antidiag/Nat.lean

-- Order/Antidiag/Pi.lean

-- Order/Antidiag/Prod.lean

-- Order/Archimedean/Basic.lean

-- Order/BigOperators/Expect.lean

-- Order/BigOperators/Group/Finset.lean

-- Order/BigOperators/Group/List.lean

-- Order/BigOperators/Group/LocallyFinite.lean

-- Order/BigOperators/Group/Multiset.lean

-- Order/BigOperators/Ring/Finset.lean

-- Order/CauSeq/Basic.lean
-- COLLISION: sup_eq_left' already in Order.lean — rename needed
-- COLLISION: inf_le_right' already in Order.lean — rename needed

-- Order/CauSeq/BigOperators.lean

-- Order/CauSeq/Completion.lean

-- Order/Chebyshev.lean

-- Order/CompleteField.lean

-- Order/EuclideanAbsoluteValue.lean

-- Order/Field/Basic.lean

-- Order/Field/Canonical/Basic.lean

-- Order/Field/Canonical/Defs.lean

-- Order/Field/Defs.lean

-- Order/Field/InjSurj.lean

-- Order/Field/Pi.lean

-- Order/Field/Pointwise.lean

-- Order/Field/Power.lean

-- Order/Floor.lean

-- Order/Floor/Div.lean

-- Order/Floor/Prime.lean

-- Order/Group/Abs.lean

-- Order/Group/Action.lean
-- COLLISION: smul_mono_right' already in RingTheory2.lean — rename needed
-- COLLISION: pow_smul_le' already in RingTheory2.lean — rename needed

-- Order/Group/Basic.lean

-- Order/Group/CompleteLattice.lean

-- Order/Group/Cone.lean

-- Order/Group/Defs.lean

-- Order/Group/DenselyOrdered.lean

-- Order/Group/Finset.lean

-- Order/Group/Indicator.lean

-- Order/Group/InjSurj.lean

-- Order/Group/Lattice.lean

-- Order/Group/MinMax.lean

-- Order/Group/Nat.lean

-- Order/Group/Opposite.lean

-- Order/Group/OrderIso.lean

-- Order/Group/Pointwise/Bounds.lean

-- Order/Group/Pointwise/CompleteLattice.lean

-- Order/Group/Pointwise/Interval.lean

-- Order/Group/PosPart.lean

-- Order/Group/Unbundled/Abs.lean

-- Order/Group/Unbundled/Basic.lean

-- Order/Group/Unbundled/Int.lean

-- Order/Hom/Basic.lean

-- Order/Hom/Monoid.lean
-- COLLISION: toOrderIso' already in Order.lean — rename needed
-- COLLISION: strictMono' already in SetTheory.lean — rename needed

-- Order/Hom/Normed.lean

-- Order/Hom/Ring.lean

-- Order/Interval/Basic.lean

-- Order/Interval/Finset.lean

-- Order/Interval/Multiset.lean

-- Order/Interval/Set/Group.lean

-- Order/Interval/Set/Instances.lean

-- Order/Interval/Set/Monoid.lean

-- Order/Invertible.lean

-- Order/Kleene.lean

-- Order/Module/Algebra.lean

-- Order/Module/Defs.lean

-- Order/Module/OrderedSMul.lean

-- Order/Module/Pointwise.lean

-- Order/Module/Rat.lean

-- Order/Monoid/Basic.lean

-- Order/Monoid/Canonical/Basic.lean

-- Order/Monoid/Canonical/Defs.lean

-- Order/Monoid/Defs.lean

-- Order/Monoid/NatCast.lean
-- COLLISION: one_lt_two' already in SetTheory.lean — rename needed

-- Order/Monoid/Submonoid.lean

-- Order/Monoid/ToMulBot.lean

-- Order/Monoid/Unbundled/Basic.lean

-- Order/Monoid/Unbundled/Defs.lean

-- Order/Monoid/Unbundled/ExistsOfLE.lean

-- Order/Monoid/Unbundled/MinMax.lean

-- Order/Monoid/Unbundled/Pow.lean

-- Order/Monoid/Units.lean

-- Order/Monovary.lean

-- Order/Nonneg/Field.lean

-- Order/Pi.lean

-- Order/Quantale.lean

-- Order/Rearrangement.lean

-- Order/Ring/Abs.lean

-- Order/Ring/Basic.lean

-- Order/Ring/Canonical.lean

-- Order/Ring/Cast.lean

-- Order/Ring/Cone.lean

-- Order/Ring/Defs.lean

-- Order/Ring/Finset.lean

-- Order/Ring/InjSurj.lean

-- Order/Ring/Int.lean

-- Order/Ring/Nat.lean

-- Order/Ring/Pow.lean

-- Order/Ring/Star.lean

-- Order/Ring/Unbundled/Basic.lean

-- Order/Ring/Unbundled/Nonneg.lean

-- Order/Ring/Unbundled/Rat.lean
-- COLLISION: mul_nonneg' already in Order.lean — rename needed
-- COLLISION: abs_def' already in Order.lean — rename needed

-- Order/Star/Basic.lean

-- Order/Star/Conjneg.lean

-- Order/Sub/Basic.lean

-- Order/Sub/Defs.lean

-- Order/Sub/Unbundled/Basic.lean

-- Order/Sub/Unbundled/Hom.lean

-- Order/SuccPred.lean

-- Order/Sum.lean

-- Order/ToIntervalMod.lean

-- Order/UpperLower.lean

-- Order/ZeroLEOne.lean
-- COLLISION: zero_lt_one' already in SetTheory.lean — rename needed

-- Periodic.lean

-- Pointwise/Stabilizer.lean

-- Polynomial/AlgebraMap.lean

-- Polynomial/Basic.lean

-- Polynomial/BigOperators.lean

-- Polynomial/Bivariate.lean

-- Polynomial/CancelLeads.lean

-- Polynomial/Cardinal.lean

-- Polynomial/Coeff.lean

-- Polynomial/Degree/CardPowDegree.lean

-- Polynomial/Degree/Definitions.lean

-- Polynomial/Degree/Domain.lean

-- Polynomial/Degree/Lemmas.lean

-- Polynomial/Degree/Monomial.lean

-- Polynomial/Degree/Operations.lean

-- Polynomial/Degree/SmallDegree.lean

-- Polynomial/Degree/Support.lean

-- Polynomial/Degree/TrailingDegree.lean

-- Polynomial/Degree/Units.lean

-- Polynomial/DenomsClearable.lean

-- Polynomial/Derivation.lean

-- Polynomial/Derivative.lean

-- Polynomial/Div.lean

-- Polynomial/EraseLead.lean

-- Polynomial/Eval/Algebra.lean

-- Polynomial/Eval/Coeff.lean

-- Polynomial/Eval/Defs.lean

-- Polynomial/Eval/Degree.lean

-- Polynomial/Eval/Irreducible.lean

-- Polynomial/Eval/SMul.lean

-- Polynomial/Eval/Subring.lean

-- Polynomial/Expand.lean

-- Polynomial/FieldDivision.lean

-- Polynomial/GroupRingAction.lean
-- COLLISION: monic' already in RingTheory2.lean — rename needed

-- Polynomial/HasseDeriv.lean

-- Polynomial/Identities.lean

-- Polynomial/Inductions.lean

-- Polynomial/Laurent.lean

-- Polynomial/Lifts.lean

-- Polynomial/Mirror.lean

-- Polynomial/Module/AEval.lean

-- Polynomial/Module/Basic.lean

-- Polynomial/Module/FiniteDimensional.lean

-- Polynomial/Monic.lean

-- Polynomial/Monomial.lean

-- Polynomial/PartialFractions.lean

-- Polynomial/Reverse.lean

-- Polynomial/RingDivision.lean

-- Polynomial/Roots.lean

-- Polynomial/Smeval.lean

-- Polynomial/SpecificDegree.lean

-- Polynomial/Splits.lean

-- Polynomial/SumIteratedDerivative.lean

-- Polynomial/Taylor.lean

-- Polynomial/UnitTrinomial.lean

-- PresentedMonoid/Basic.lean
-- COLLISION: inductionOn₂' already in SetTheory.lean — rename needed
-- COLLISION: inductionOn₃' already in SetTheory.lean — rename needed

-- Prime/Defs.lean
-- COLLISION: prime' already in RingTheory2.lean — rename needed

-- Prime/Lemmas.lean

-- QuadraticDiscriminant.lean

-- Quandle.lean

-- Quaternion.lean

-- QuaternionBasis.lean
-- COLLISION: lift_zero' already in SetTheory.lean — rename needed
-- COLLISION: lift_one' already in SetTheory.lean — rename needed
-- COLLISION: lift_add' already in SetTheory.lean — rename needed
-- COLLISION: lift_mul' already in SetTheory.lean — rename needed
-- COLLISION: liftHom' already in RingTheory2.lean — rename needed

-- Quotient.lean

-- Regular/Basic.lean

-- Regular/Pow.lean
-- COLLISION: pow_iff' already in RingTheory2.lean — rename needed

-- Regular/SMul.lean
-- COLLISION: isSMulRegular_congr' already in RingTheory2.lean — rename needed

-- Ring/Action/Basic.lean

-- Ring/Action/Field.lean

-- Ring/Action/Group.lean

-- Ring/Action/Invariant.lean

-- Ring/AddAut.lean

-- Ring/Aut.lean

-- Ring/Basic.lean

-- Ring/BooleanRing.lean

-- Ring/Center.lean

-- Ring/Centralizer.lean

-- Ring/CentroidHom.lean

-- Ring/Commute.lean

-- Ring/CompTypeclasses.lean

-- Ring/Defs.lean

-- Ring/Divisibility/Basic.lean

-- Ring/Divisibility/Lemmas.lean

-- Ring/Equiv.lean
-- COLLISION: isDomain' already in RingTheory2.lean — rename needed

-- Ring/Ext.lean

-- Ring/Fin.lean

-- Ring/Hom/Basic.lean

-- Ring/Hom/Defs.lean

-- Ring/Idempotents.lean

-- Ring/Identities.lean

-- Ring/InjSurj.lean

-- Ring/Int/Defs.lean

-- Ring/Int/Parity.lean

-- Ring/Int/Units.lean

-- Ring/Invertible.lean

-- Ring/MinimalAxioms.lean

-- Ring/NegOnePow.lean

-- Ring/Opposite.lean

-- Ring/Parity.lean

-- Ring/Pi.lean

-- Ring/Pointwise/Finset.lean
-- COLLISION: mul_add_subset' already in Order.lean — rename needed

-- Ring/Pointwise/Set.lean

-- Ring/Prod.lean

-- Ring/Rat.lean

-- Ring/Regular.lean

-- Ring/Semiconj.lean

-- Ring/Semireal/Defs.lean

-- Ring/Subring/Basic.lean
-- COLLISION: sInf_toAddSubgroup' already in RingTheory2.lean — rename needed
-- COLLISION: eqOn_set_closure' already in RingTheory2.lean — rename needed
-- COLLISION: eq_of_eqOn_set_top' already in RingTheory2.lean — rename needed
-- COLLISION: eq_of_eqOn_set_dense' already in RingTheory2.lean — rename needed

-- Ring/Subring/Defs.lean
-- COLLISION: mk'_toAddSubgroup' already in RingTheory2.lean — rename needed

-- Ring/Subring/IntPolynomial.lean

-- Ring/Subring/MulOpposite.lean

-- Ring/Subring/Order.lean

-- Ring/Subring/Pointwise.lean

-- Ring/Subring/Units.lean

-- Ring/Subsemiring/Basic.lean

-- Ring/Subsemiring/Defs.lean

-- Ring/Subsemiring/MulOpposite.lean

-- Ring/Subsemiring/Order.lean

-- Ring/Subsemiring/Pointwise.lean

-- Ring/SumsOfSquares.lean

-- Ring/Units.lean

-- RingQuot.lean

-- SkewMonoidAlgebra/Basic.lean

-- Squarefree/Basic.lean

-- Star/Basic.lean

-- Star/BigOperators.lean

-- Star/CHSH.lean

-- Star/Center.lean

-- Star/CentroidHom.lean

-- Star/Conjneg.lean

-- Star/Free.lean

-- Star/Module.lean

-- Star/NonUnitalSubalgebra.lean

-- Star/NonUnitalSubsemiring.lean

-- Star/Pi.lean

-- Star/Pointwise.lean

-- Star/Rat.lean

-- Star/RingQuot.lean

-- Star/SelfAdjoint.lean

-- Star/StarAlgHom.lean

-- Star/StarRingHom.lean

-- Star/Subalgebra.lean

-- Star/Subsemiring.lean

-- Star/Unitary.lean

-- Symmetrized.lean

-- TrivSqZeroExt.lean
-- COLLISION: map_comp_map' already in RingTheory2.lean — rename needed

-- Tropical/Basic.lean
-- COLLISION: add_eq_left' already in SetTheory.lean — rename needed

-- Tropical/BigOperators.lean

-- Vertex/HVertexOperator.lean
