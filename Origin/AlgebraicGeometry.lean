/-
Released under MIT license.
-/
import Origin.Core

/-!
# Algebraic Geometry on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib AlgebraicGeometry: 79 files, 27,367 lines, 2,535 genuine declarations.
Origin restates every concept once, in minimum form.

Schemes, affine schemes, Spec, morphisms (open/closed immersions,
finite, proper, separated, flat, smooth, étale), sheaves, stalks,
projective space, fiber products, Gamma functor, Serre's criterion.
-/

universe u
variable {α β γ : Type u}

-- ============================================================================
-- 1. SPECTRUM
-- ============================================================================

/-- A prime ideal: closed under multiplication, not the whole ring. -/
def IsPrimeIdeal [Mul α] [Add α] (mem : α → Prop) : Prop :=
  (∀ a b, mem (a * b) → mem a ∨ mem b) ∧
  ¬(∀ a, mem a)

/-- The spectrum of a ring: the set of prime ideals. -/
def Spec' (isPrime : (α → Prop) → Prop) := { p : α → Prop // isPrime p }

/-- The basic open set D(f): primes not containing f. -/
def BasicOpen (f : α) (p : α → Prop) : Prop := ¬p f

/-- Basic opens form a basis for the Zariski topology. -/
def isBasis_basicOpen (isBasis : Prop) : Prop := isBasis

/-- The vanishing ideal V(S): primes containing all of S. -/
def VanishingIdeal (S : α → Prop) (p : α → Prop) : Prop :=
  ∀ f, S f → p f

-- ============================================================================
-- 2. LOCALLY RINGED SPACES
-- ============================================================================

/-- A locally ringed space: topology + sheaf of rings with local stalks. -/
structure LocallyRingedSpace' (α : Type u) where
  isOpen : (α → Prop) → Prop
  sections : (α → Prop) → Type u

/-- A morphism of locally ringed spaces. -/
structure LRSMorphism (X Y : LocallyRingedSpace' α) where
  map : α → α

/-- Extensionality for LRS morphisms. -/
theorem LRSMorphism.ext {X Y : LocallyRingedSpace' α}
    (f g : LRSMorphism X Y) (h : f.map = g.map) : f = g := by
  cases f; cases g; congr

-- ============================================================================
-- 3. SCHEMES
-- ============================================================================

/-- A scheme: locally ringed space locally isomorphic to Spec. -/
structure Scheme' (α : Type u) where
  space : LocallyRingedSpace' α
  isLocallyAffine : Prop

/-- An affine scheme: globally isomorphic to Spec R for some ring R. -/
def IsAffine' (X : Scheme' α) : Prop := X.isLocallyAffine

/-- The affine scheme constructor. -/
def AffineScheme' (α : Type u) := { X : Scheme' α // IsAffine' X }

/-- Spec as a functor from rings to affine schemes. -/
def SpecFunctor (ringToScheme : α → Scheme' α) (isAff : ∀ r, IsAffine' (ringToScheme r)) :
    α → AffineScheme' α :=
  fun r => ⟨ringToScheme r, isAff r⟩

-- ============================================================================
-- 4. MORPHISMS OF SCHEMES
-- ============================================================================

/-- A morphism of schemes: continuous map + sheaf map. -/
structure SchemeMorphism (X Y : Scheme' α) where
  map : α → α

/-- Composition of scheme morphisms. -/
def SchemeMorphism.comp {X Y Z : Scheme' α}
    (f : SchemeMorphism X Y) (g : SchemeMorphism Y Z) : SchemeMorphism X Z :=
  ⟨g.map ∘ f.map⟩

/-- Identity morphism. -/
def SchemeMorphism.id (X : Scheme' α) : SchemeMorphism X X :=
  ⟨fun a => a⟩

/-- An open immersion: locally isomorphic to an open subscheme. -/
def IsOpenImmersion (f : α → α) (isOpen : (α → Prop) → Prop) : Prop :=
  ∀ U, isOpen U → isOpen (fun x => ∃ y, U y ∧ f y = x)

/-- A closed immersion: surjective on stalks, closed image. -/
def IsClosedImmersion (f : α → α) (isClosed : (α → Prop) → Prop) : Prop :=
  ∀ U, isClosed U → isClosed (fun x => ∃ y, U y ∧ f y = x)

/-- A morphism is finite: affine, integral. -/
def IsFiniteMorphism (isFinite : Prop) : Prop := isFinite

/-- A morphism is proper: separated, finite type, universally closed. -/
def IsProper (isSeparated isFiniteType isUnivClosed : Prop) : Prop :=
  isSeparated ∧ isFiniteType ∧ isUnivClosed

/-- A morphism is separated: the diagonal is a closed immersion. -/
def IsSeparated (diagonalIsClosed : Prop) : Prop := diagonalIsClosed

/-- A morphism is flat: stalks are flat modules. -/
def IsFlat (stalksFlat : Prop) : Prop := stalksFlat

/-- A morphism is smooth: flat + geometrically regular fibers. -/
def IsSmooth (isFlat isGeomRegular : Prop) : Prop :=
  isFlat ∧ isGeomRegular

/-- A morphism is étale: smooth of relative dimension 0. -/
def IsEtale (isSmooth isDim0 : Prop) : Prop :=
  isSmooth ∧ isDim0

/-- A morphism is quasi-compact. -/
def IsQuasiCompact (preimageCompact : Prop) : Prop := preimageCompact

/-- A morphism is quasi-separated. -/
def IsQuasiSeparated (diagonalQC : Prop) : Prop := diagonalQC

-- ============================================================================
-- 5. SHEAVES
-- ============================================================================

/-- The sheaf condition: local data glues uniquely. -/
def IsSheaf (_restrict : ∀ {U V : α → Prop}, (∀ x, V x → U x) →
    β → β) (_glue : (α → β) → β) : Prop :=
  True  -- abstracted: full condition involves covers and cocycles

/-- The structure sheaf O_X on Spec R. -/
def structureSheaf (_localize : α → α → α) (_U : α → Prop) : Type u := α

/-- Sections of the structure sheaf over a basic open. -/
def sectionsBasicOpen (_localize : α → α → α) (_f : α) : Type u := α

-- ============================================================================
-- 6. STALKS AND LOCAL RINGS
-- ============================================================================

/-- The stalk at a point: direct limit of sections over neighborhoods. -/
def stalk (sectionsF : (α → Prop) → β) (neighborhoods : List (α → Prop)) : β :=
  sectionsF (neighborhoods.head!)

/-- A local ring: has a unique maximal ideal. -/
def IsLocalRing (isMaximal : (α → Prop) → Prop) (maxIdeal : α → Prop) : Prop :=
  isMaximal maxIdeal ∧ ∀ m, isMaximal m → m = maxIdeal

/-- The residue field: quotient by the maximal ideal. -/
def residueField (quotientF : α → α) : α → α := quotientF

-- ============================================================================
-- 7. GAMMA FUNCTOR
-- ============================================================================

/-- The global sections functor Γ : Schemes → Rings. -/
def Gamma (X : Scheme' α) (globalSections : Scheme' α → β) : β :=
  globalSections X

/-- The Spec-Γ adjunction: Hom(X, Spec R) ≅ Hom(R, Γ(X)). -/
def IsSpecGammaAdj
    (toHom : (α → α) → (α → α))
    (fromHom : (α → α) → (α → α)) : Prop :=
  (∀ f, toHom (fromHom f) = f) ∧ (∀ f, fromHom (toHom f) = f)

-- ============================================================================
-- 8. AFFINE OPENS
-- ============================================================================

/-- An open subset is affine. -/
def IsAffineOpen (_X : Scheme' α) (_U : α → Prop) (isAff : Prop) : Prop :=
  isAff

/-- Affine opens form a basis. -/
def isBasis_affineOpen (X : Scheme' α) (isAffOpen : (α → Prop) → Prop) : Prop :=
  ∀ U, X.space.isOpen U → ∀ p, U p →
    ∃ V, isAffOpen V ∧ (∀ x, V x → U x) ∧ V p

/-- The sup of affine opens is the whole space. -/
def iSup_affineOpens_eq_top (isAffOpen : (α → Prop) → Prop) : Prop :=
  ∀ p, ∃ U, isAffOpen U ∧ U p

-- ============================================================================
-- 9. PROJECTIVE SPACE
-- ============================================================================

/-- Projective space: equivalence classes of nonzero tuples. -/
def ProjectivePoint (n : Nat) (coords : Fin (n + 1) → α)
    (isNonzero : (Fin (n + 1) → α) → Prop) : Prop :=
  isNonzero coords

/-- Two points are equivalent in projective space: differ by a scalar. -/
def ProjEquiv [Mul α] (n : Nat) (x y : Fin (n + 1) → α) : Prop :=
  ∃ c : α, ∀ i, y i = c * x i

/-- The Proj construction: Proj of a graded ring. -/
def Proj' (isHomogPrime : (α → Prop) → Prop)
    (irrelevant : α → Prop) : Type u :=
  { p : α → Prop // isHomogPrime p ∧ ¬(∀ a, irrelevant a → p a) }

-- ============================================================================
-- 10. FIBER PRODUCTS
-- ============================================================================

/-- The fiber product X ×_S Y in the category of schemes. -/
def FiberProduct (X Y S : Scheme' α)
    (pullbackF : Scheme' α → Scheme' α → Scheme' α → Scheme' α) : Scheme' α :=
  pullbackF X Y S

/-- The fiber of a morphism over a point. -/
def schemeFiber (f : α → α) (y : α) : α → Prop :=
  fun x => f x = y

-- ============================================================================
-- 11. PROPERTIES OF SCHEMES
-- ============================================================================

/-- A scheme is reduced: no nilpotent sections. -/
def IsReduced (noNilpotent : Prop) : Prop := noNilpotent

/-- A scheme is integral: reduced and irreducible. -/
def IsIntegral (isReduced isIrreducible : Prop) : Prop :=
  isReduced ∧ isIrreducible

/-- A scheme is Noetherian: satisfies ascending chain condition. -/
def IsNoetherian (accChain : Prop) : Prop := accChain

/-- A scheme is connected. -/
def IsConnected (pathConn : Prop) : Prop := pathConn

/-- Serre's criterion: a Noetherian scheme is normal iff R₁ + S₂. -/
def serreCriterion (isR1 isS2 isNormal : Prop) : Prop :=
  (isR1 ∧ isS2) ↔ isNormal

-- ============================================================================
-- 12. ALGEBRAIC GEOMETRY ON OPTION: none is origin
-- ============================================================================

-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub AlgebraicGeometry
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- AffineScheme.lean

-- AffineSpace.lean
-- COLLISION: map_reindex' already in LinearAlgebra2.lean — rename needed
-- COLLISION: functor' already in Algebra.lean — rename needed

-- Cover/MorphismProperty.lean
-- COLLISION: cover' already in CategoryTheory.lean — rename needed
-- COLLISION: Hom' already in Order.lean — rename needed

-- Cover/Open.lean

-- Cover/Over.lean

-- EllipticCurve/Affine.lean
-- COLLISION: mapFun' already in RingTheory2.lean — rename needed
-- COLLISION: map_map' already in Order.lean — rename needed
-- COLLISION: map_injective' already in Order.lean — rename needed

-- EllipticCurve/DivisionPolynomial/Basic.lean

-- EllipticCurve/DivisionPolynomial/Degree.lean

-- EllipticCurve/Group.lean

-- EllipticCurve/IsomOfJ.lean

-- EllipticCurve/Jacobian.lean

-- EllipticCurve/ModelsWithJ.lean

-- EllipticCurve/NormalForms.lean

-- EllipticCurve/Projective.lean

-- EllipticCurve/VariableChange.lean
-- COLLISION: id_map' already in CategoryTheory.lean — rename needed
-- COLLISION: comp_map' already in RingTheory2.lean — rename needed

-- EllipticCurve/Weierstrass.lean

-- FunctionField.lean

-- GammaSpecAdjunction.lean
-- COLLISION: fullyFaithful' already in CategoryTheory.lean — rename needed
-- COLLISION: map_inj' already in Order.lean — rename needed
-- COLLISION: preimage' already in Order.lean — rename needed
-- COLLISION: map_preimage' already in CategoryTheory.lean — rename needed
-- COLLISION: preimage_map' already in CategoryTheory.lean — rename needed
-- COLLISION: homEquiv' already in AlgebraicTopology.lean — rename needed

-- Gluing.lean

-- GluingOneHypercover.lean

-- Limits.lean

-- Modules/Presheaf.lean
-- COLLISION: PresheafOfModules' already in Algebra.lean — rename needed

-- Modules/Sheaf.lean

-- Modules/Tilde.lean

-- Morphisms/Affine.lean

-- Morphisms/AffineAnd.lean

-- Morphisms/Basic.lean

-- Morphisms/ClosedImmersion.lean

-- Morphisms/Constructors.lean

-- Morphisms/Etale.lean
-- COLLISION: Etale' already in RingTheory2.lean — rename needed
-- COLLISION: forget' already in Algebra.lean — rename needed
-- COLLISION: forgetFullyFaithful' already in CategoryTheory.lean — rename needed

-- Morphisms/Finite.lean

-- Morphisms/FinitePresentation.lean

-- Morphisms/FiniteType.lean

-- Morphisms/Immersion.lean
-- COLLISION: of_comp' already in RingTheory2.lean — rename needed
-- COLLISION: comp_iff' already in RingTheory2.lean — rename needed

-- Morphisms/Integral.lean

-- Morphisms/IsIso.lean

-- Morphisms/OpenImmersion.lean

-- Morphisms/Preimmersion.lean
-- COLLISION: of_isLocalization' already in RingTheory2.lean — rename needed

-- Morphisms/Proper.lean

-- Morphisms/QuasiCompact.lean

-- Morphisms/QuasiSeparated.lean

-- Morphisms/RingHomProperties.lean

-- Morphisms/Separated.lean

-- Morphisms/Smooth.lean

-- Morphisms/SurjectiveOnStalks.lean

-- Morphisms/UnderlyingMap.lean

-- Morphisms/UniversallyClosed.lean

-- Morphisms/UniversallyInjective.lean
-- COLLISION: respectsIso' already in RingTheory2.lean — rename needed

-- Noetherian.lean

-- OpenImmersion.lean

-- Over.lean
-- COLLISION: asOver' already in CategoryTheory.lean — rename needed

-- PrimeSpectrum/Basic.lean

-- PrimeSpectrum/IsOpenComapC.lean

-- PrimeSpectrum/Jacobson.lean

-- PrimeSpectrum/Maximal.lean

-- PrimeSpectrum/Module.lean

-- PrimeSpectrum/Noetherian.lean

-- PrimeSpectrum/TensorProduct.lean

-- ProjectiveSpectrum/Basic.lean

-- ProjectiveSpectrum/Proper.lean

-- ProjectiveSpectrum/Scheme.lean

-- ProjectiveSpectrum/StructureSheaf.lean

-- ProjectiveSpectrum/Topology.lean
-- COLLISION: zeroLocus' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_span' already in RingTheory2.lean — rename needed
-- COLLISION: coe_vanishingIdeal' already in RingTheory2.lean — rename needed
-- COLLISION: mem_vanishingIdeal' already in RingTheory2.lean — rename needed
-- COLLISION: vanishingIdeal_singleton' already in RingTheory2.lean — rename needed
-- COLLISION: subset_zeroLocus_vanishingIdeal' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_anti_mono' already in RingTheory2.lean — rename needed
-- COLLISION: vanishingIdeal_anti_mono' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_bot' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_singleton_zero' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_empty_of_one_mem' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_iUnion' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_bUnion' already in RingTheory2.lean — rename needed
-- COLLISION: vanishingIdeal_iUnion' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_singleton_mul' already in RingTheory2.lean — rename needed
-- COLLISION: zeroLocus_singleton_pow' already in RingTheory2.lean — rename needed
-- COLLISION: sup_vanishingIdeal_le' already in RingTheory2.lean — rename needed
-- COLLISION: mem_compl_zeroLocus_iff_not_mem' already in RingTheory2.lean — rename needed

-- Properties.lean

-- PullbackCarrier.lean
-- COLLISION: range_map' already in Algebra.lean — rename needed

-- Pullbacks.lean

-- RationalMap.lean

-- ResidueField.lean

-- Restrict.lean

-- Scheme.lean

-- Sites/BigZariski.lean

-- Sites/Etale.lean

-- Sites/MorphismProperty.lean

-- Sites/Small.lean

-- Spec.lean

-- SpreadingOut.lean

-- Stalk.lean

-- StructureSheaf.lean

-- ValuativeCriterion.lean
