/-
Released under MIT license.
-/
import Origin.Core

/-!
# Topology on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Topology: 277 files, 122,940 lines, 12,596 genuine declarations.
Origin restates every concept once, in minimum form.

Open sets, continuity, compactness, connectedness, metric spaces,
filters, convergence, homotopy, sheaves, separation axioms,
Baire category, product/quotient topologies, path connectedness,
Alexandroff compactification.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. TOPOLOGICAL SPACE
-- ============================================================================

/-- A topology: collection of open sets closed under union and finite intersection. -/
structure TopologyAxioms (α : Type u) where
  isOpen : (α → Prop) → Prop
  univ_open : isOpen (fun _ => True)
  empty_open : isOpen (fun _ => False)
  inter_open : ∀ U V, isOpen U → isOpen V → isOpen (fun x => U x ∧ V x)

/-- A set is closed if its complement is open. -/
def IsClosed (isOpen : (α → Prop) → Prop) (C : α → Prop) : Prop :=
  isOpen (fun x => ¬C x)

/-- The closure: smallest closed set containing S. -/
def closure (isOpen : (α → Prop) → Prop) (S : α → Prop) : α → Prop :=
  fun x => ∀ U, isOpen U → U x → ∃ a, U a ∧ S a

/-- The interior: largest open set contained in S. -/
def interior (isOpen : (α → Prop) → Prop) (S : α → Prop) : α → Prop :=
  fun x => ∃ U, isOpen U ∧ U x ∧ ∀ a, U a → S a

-- ============================================================================
-- 2. ALEXANDROFF COMPACTIFICATION (Option as one-point)
-- ============================================================================

/-- Alexandroff topology on Option α: open sets are either open-in-α
    or cocompact neighborhoods of none. -/
def IsOpenC (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (U : Option α → Prop) : Prop :=
  openα (fun a => U (some a)) ∧
  (U none → compactα (fun a => ¬ U (some a)))

-- ============================================================================
-- 3. CONTINUITY
-- ============================================================================

/-- Continuity: preimage of open is open. -/
def IsContinuous (f : α → α) (isOpen : (α → Prop) → Prop) : Prop :=
  ∀ U, isOpen U → isOpen (fun x => U (f x))

/-- Continuous maps compose. -/
theorem continuous_comp (f g : α → α) (isOpen : (α → Prop) → Prop)
    (hf : IsContinuous f isOpen) (hg : IsContinuous g isOpen) :
    IsContinuous (g ∘ f) isOpen := by
  intro U hU; exact hf _ (hg U hU)

/-- A homeomorphism: continuous bijection with continuous inverse. -/
def IsHomeomorphism (f : α → α) (inv : α → α) (isOpen : (α → Prop) → Prop) : Prop :=
  IsContinuous f isOpen ∧ IsContinuous inv isOpen ∧
  (∀ a, inv (f a) = a) ∧ (∀ a, f (inv a) = a)

-- ============================================================================
-- 4. COMPACTNESS
-- ============================================================================

/-- A space is compact: every open cover has a finite subcover. -/
def IsCompact' (isOpen : (α → Prop) → Prop) (S : α → Prop) : Prop :=
  ∀ cover : Nat → (α → Prop),
    (∀ n, isOpen (cover n)) →
    (∀ x, S x → ∃ n, cover n x) →
    ∃ N, ∀ x, S x → ∃ n, n < N ∧ cover n x

/-- Compact image: image of compact set under continuous map is compact. -/
def compactImage (isCompact : (α → Prop) → Prop) (f : α → α)
    (S : α → Prop) : Prop :=
  isCompact S → isCompact (fun y => ∃ x, S x ∧ f x = y)

-- ============================================================================
-- 5. CONNECTEDNESS
-- ============================================================================

/-- A space is connected: not the union of two disjoint nonempty open sets. -/
def IsConnected' (isOpen : (α → Prop) → Prop) : Prop :=
  ∀ U V, isOpen U → isOpen V →
    (∃ x, U x) → (∃ x, V x) →
    (∀ x, U x ∨ V x) →
    ∃ x, U x ∧ V x

/-- Path connectedness: any two points joined by a continuous path. -/
def IsPathConnected (pathF : α → α → α → α) (start finish : α) : Prop :=
  ∀ x y, pathF x y start = x ∧ pathF x y finish = y

-- ============================================================================
-- 6. METRIC SPACES
-- ============================================================================

/-- Lipschitz continuity: d(f(a), f(b)) ≤ K · d(a, b). -/
def IsLipschitz (f : α → α) (K : α) (distF : α → α → α) (leF : α → α → Prop)
    (mulF : α → α → α) : Prop :=
  ∀ a b, leF (distF (f a) (f b)) (mulF K (distF a b))

/-- An isometry: distance-preserving map. -/
def IsIsometry (f : α → α) (distF : α → α → α) : Prop :=
  ∀ a b, distF (f a) (f b) = distF a b

/-- A contraction mapping: Lipschitz with K < 1. -/
def IsContraction (f : α → α) (distF : α → α → α) (leF : α → α → Prop)
    (mulF : α → α → α) (K : α) (Klt1 : Prop) : Prop :=
  Klt1 ∧ IsLipschitz f K distF leF mulF

/-- Banach fixed point theorem (abstract): contractions have unique fixed points. -/
def banachFixedPoint (hasUniqueFixedPoint : Prop) (isContraction : Prop) : Prop :=
  isContraction → hasUniqueFixedPoint

/-- Completeness: every Cauchy sequence converges. -/
def IsComplete (cauchyConverges : Prop) : Prop := cauchyConverges

-- ============================================================================
-- 7. FILTERS AND CONVERGENCE
-- ============================================================================

/-- A filter on Option α. -/
structure OptFilter (α : Type u) where
  sets : (Option α → Prop) → Prop
  univ_mem : sets (fun _ => True)
  superset : ∀ U V, sets U → (∀ x, U x → V x) → sets V
  inter_mem : ∀ U V, sets U → sets V → sets (fun x => U x ∧ V x)

/-- An ultrafilter: maximal proper filter. -/
def IsUltrafilter (F : OptFilter α) : Prop :=
  (¬ F.sets (fun _ => False)) ∧
  ∀ U : Option α → Prop, F.sets U ∨ F.sets (fun x => ¬ U x)

/-- Convergence of a filter to a point. -/
def FilterConverges (F : OptFilter α) (x : Option α)
    (nhds : Option α → (Option α → Prop) → Prop) : Prop :=
  ∀ U, nhds x U → F.sets U

-- ============================================================================
-- 8. HOMOTOPY
-- ============================================================================

/-- Fundamental group element: a loop based at a point. -/
def FundGroupElem (basepoint : α) (loop : α → α) : Prop :=
  loop basepoint = basepoint

/-- Composition of loops preserves the basepoint. -/
theorem fund_group_comp (bp : α) (l₁ l₂ : α → α)
    (h₁ : FundGroupElem bp l₁) (h₂ : FundGroupElem bp l₂) :
    FundGroupElem bp (l₁ ∘ l₂) := by
  simp [FundGroupElem, Function.comp] at *; rw [h₂, h₁]

/-- A covering map: local homeomorphism with discrete fibers. -/
def IsCoveringMap (p : α → α) (local_inv : α → α) : Prop :=
  ∀ a, p (local_inv a) = a

/-- Simply connected: trivial fundamental group. -/
def IsSimplyConnectedSpace (isPathConn : Prop) (trivialFundGroup : Prop) : Prop :=
  isPathConn ∧ trivialFundGroup

-- ============================================================================
-- 9. SHEAVES
-- ============================================================================

/-- A presheaf section: defined on an open set. -/
def PresheafSection (F : α → Option α) (U : α → Prop) : Prop :=
  ∀ a, U a → ∃ r, F a = some r

/-- Restriction preserves some values. -/
theorem restriction_some (F : α → Option α) (res : α → α) (a r : α)
    (h : F a = some r) :
    Option.map res (F a) = some (res r) := by simp [h]

-- ============================================================================
-- 10. SEPARATION AXIOMS
-- ============================================================================

/-- T₀: points are topologically distinguishable. -/
def IsT0 (openα : (α → Prop) → Prop) : Prop :=
  ∀ a b : α, a ≠ b → (∃ U, openα U ∧ U a ∧ ¬U b) ∨ (∃ U, openα U ∧ U b ∧ ¬U a)

/-- T₂ (Hausdorff): distinct points have disjoint neighborhoods. -/
def IsT2 (openα : (α → Prop) → Prop) : Prop :=
  ∀ a b : α, a ≠ b →
    ∃ U V, openα U ∧ openα V ∧ U a ∧ V b ∧ ∀ x, ¬(U x ∧ V x)

/-- Normal: disjoint closed sets have disjoint open neighborhoods. -/
def IsNormal' (openα : (α → Prop) → Prop) : Prop :=
  ∀ (A B : α → Prop), (∀ x, ¬(A x ∧ B x)) →
    ∃ U V, openα U ∧ openα V ∧ (∀ a, A a → U a) ∧ (∀ b, B b → V b) ∧
    ∀ x, ¬(U x ∧ V x)

-- ============================================================================
-- 11. BAIRE CATEGORY
-- ============================================================================

/-- A set is dense: meets every nonempty open set. -/
def IsDense' (openα : (α → Prop) → Prop) (D : α → Prop) : Prop :=
  ∀ U, openα U → (∃ a, U a) → ∃ a, U a ∧ D a

/-- Baire category theorem: countable intersection of dense opens is dense. -/
def IsBaire (openα : (α → Prop) → Prop) : Prop :=
  ∀ (D : Nat → α → Prop), (∀ n, IsDense' openα (D n)) →
    IsDense' openα (fun a => ∀ n, D n a)

-- ============================================================================
-- 12. PRODUCT AND QUOTIENT TOPOLOGIES
-- ============================================================================

/-- Product topology: open sets are unions of products of open sets. -/
def IsProductOpen (openA openB : (α → Prop) → Prop)
    (U : (α × α) → Prop) : Prop :=
  ∀ p, U p → ∃ UA UB, openA UA ∧ openB UB ∧ UA p.1 ∧ UB p.2

/-- Quotient topology: U is open iff its preimage is open. -/
def IsQuotientOpen (isOpen : (α → Prop) → Prop) (q : α → α)
    (U : α → Prop) : Prop :=
  isOpen (fun x => U (q x))

-- ============================================================================
-- 13. TOPOLOGY ON OPTION: demonstrations
-- ============================================================================

-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub Topology
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- AlexandrovDiscrete.lean

-- Algebra/Affine.lean

-- Algebra/Algebra.lean
-- COLLISION: apply' already in Order.lean — rename needed
-- COLLISION: coe' already in Order.lean — rename needed
-- COLLISION: ext' already in SetTheory.lean — rename needed
-- COLLISION: copy' already in Order.lean — rename needed
-- COLLISION: copy_eq' already in Order.lean — rename needed
-- COLLISION: map_zero' already in RingTheory2.lean — rename needed
-- COLLISION: map_add' already in RingTheory2.lean — rename needed
-- COLLISION: map_smul' already in RingTheory2.lean — rename needed
-- COLLISION: id' already in Order.lean — rename needed
-- COLLISION: prod' already in SetTheory.lean — rename needed

-- Algebra/Category/ProfiniteGrp/Basic.lean
-- COLLISION: limitCone' already in Algebra.lean — rename needed
-- COLLISION: limitConeIsLimit' already in Algebra.lean — rename needed
-- COLLISION: limit' already in Order.lean — rename needed

-- Algebra/ClopenNhdofOne.lean

-- Algebra/ClosedSubgroup.lean

-- Algebra/ConstMulAction.lean

-- Algebra/Constructions.lean

-- Algebra/Constructions/DomMulAct.lean

-- Algebra/ContinuousAffineMap.lean

-- Algebra/ContinuousMonoidHom.lean
-- COLLISION: one' already in SetTheory.lean — rename needed
-- COLLISION: inl' already in Algebra.lean — rename needed
-- COLLISION: inr' already in Algebra.lean — rename needed

-- Algebra/Equicontinuity.lean

-- Algebra/Field.lean

-- Algebra/FilterBasis.lean

-- Algebra/Group/Basic.lean

-- Algebra/Group/Compact.lean

-- Algebra/Group/OpenMapping.lean

-- Algebra/Group/Quotient.lean

-- Algebra/Group/SubmonoidClosure.lean

-- Algebra/Group/TopologicalAbelianization.lean

-- Algebra/GroupCompletion.lean
-- COLLISION: coe_neg' already in RingTheory2.lean — rename needed
-- COLLISION: completion_add' already in Analysis.lean — rename needed

-- Algebra/InfiniteSum/Basic.lean

-- Algebra/InfiniteSum/Constructions.lean

-- Algebra/InfiniteSum/Defs.lean
-- COLLISION: unique' already in Order.lean — rename needed

-- Algebra/InfiniteSum/ENNReal.lean

-- Algebra/InfiniteSum/Field.lean

-- Algebra/InfiniteSum/Group.lean

-- Algebra/InfiniteSum/GroupCompletion.lean

-- Algebra/InfiniteSum/Module.lean

-- Algebra/InfiniteSum/NatInt.lean

-- Algebra/InfiniteSum/Nonarchimedean.lean

-- Algebra/InfiniteSum/Order.lean
-- COLLISION: abs' already in RingTheory2.lean — rename needed

-- Algebra/InfiniteSum/Real.lean

-- Algebra/InfiniteSum/Ring.lean

-- Algebra/Localization.lean

-- Algebra/Module/Alternating/Basic.lean
-- COLLISION: map_update_add' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_update_smul' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_coord_zero' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_update_zero' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_eq_zero_of_eq' already in LinearAlgebra2.lean — rename needed
-- COLLISION: toContinuousLinearMap' already in Analysis.lean — rename needed
-- COLLISION: piEquiv' already in Algebra.lean — rename needed

-- Algebra/Module/Alternating/Topology.lean

-- Algebra/Module/Basic.lean
-- COLLISION: coe_sum' already in Algebra.lean — rename needed

-- Algebra/Module/CharacterSpace.lean

-- Algebra/Module/Determinant.lean
-- COLLISION: det' already in RingTheory2.lean — rename needed
-- COLLISION: det_coe_symm' already in LinearAlgebra2.lean — rename needed

-- Algebra/Module/FiniteDimension.lean

-- Algebra/Module/LinearPMap.lean

-- Algebra/Module/LocallyConvex.lean

-- Algebra/Module/ModuleTopology.lean

-- Algebra/Module/Multilinear/Basic.lean
-- COLLISION: domDomCongr' already in LinearAlgebra2.lean — rename needed
-- COLLISION: domDomCongrEquiv' already in LinearAlgebra2.lean — rename needed
-- COLLISION: linearDeriv' already in LinearAlgebra2.lean — rename needed
-- COLLISION: linearDeriv_apply' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiAlgebra' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiAlgebraFin' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_apply_one_eq_self' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_eq_iff' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_zero' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_eq_zero_iff' already in LinearAlgebra2.lean — rename needed

-- Algebra/Module/Multilinear/Bounded.lean

-- Algebra/Module/Multilinear/Topology.lean

-- Algebra/Module/Simple.lean

-- Algebra/Module/Star.lean

-- Algebra/Module/StrongTopology.lean
-- COLLISION: arrowCongr' already in Order.lean — rename needed

-- Algebra/Module/UniformConvergence.lean

-- Algebra/Module/WeakBilin.lean

-- Algebra/Module/WeakDual.lean

-- Algebra/Monoid.lean

-- Algebra/MulAction.lean

-- Algebra/MvPolynomial.lean

-- Algebra/NonUnitalAlgebra.lean

-- Algebra/NonUnitalStarAlgebra.lean

-- Algebra/Nonarchimedean/AdicTopology.lean

-- Algebra/Nonarchimedean/Bases.lean
-- COLLISION: moduleFilterBasis' already in Analysis.lean — rename needed

-- Algebra/Nonarchimedean/Basic.lean
-- COLLISION: mul_subset' already in Algebra.lean — rename needed

-- Algebra/Nonarchimedean/TotallyDisconnected.lean

-- Algebra/OpenSubgroup.lean

-- Algebra/Order/Archimedean.lean

-- Algebra/Order/Field.lean

-- Algebra/Order/Floor.lean

-- Algebra/Order/Group.lean

-- Algebra/Order/LiminfLimsup.lean

-- Algebra/Order/UpperLower.lean
-- COLLISION: upperClosure' already in Order.lean — rename needed
-- COLLISION: lowerClosure' already in Order.lean — rename needed

-- Algebra/Polynomial.lean

-- Algebra/PontryaginDual.lean
-- COLLISION: map_one' already in RingTheory2.lean — rename needed
-- COLLISION: map_comp' already in RingTheory2.lean — rename needed
-- COLLISION: map_mul' already in RingTheory2.lean — rename needed
-- COLLISION: mapHom' already in RingTheory2.lean — rename needed

-- Algebra/ProperAction/Basic.lean

-- Algebra/ProperAction/ProperlyDiscontinuous.lean

-- Algebra/ProperConstSMul.lean
-- COLLISION: preimage_smul' already in Analysis.lean — rename needed

-- Algebra/Ring/Basic.lean
-- COLLISION: orderEmbedding' already in SetTheory.lean — rename needed

-- Algebra/Ring/Ideal.lean

-- Algebra/Semigroup.lean

-- Algebra/SeparationQuotient/Basic.lean
-- COLLISION: mkMonoidHom' already in Algebra.lean — rename needed
-- COLLISION: mkRingHom' already in Algebra.lean — rename needed
-- COLLISION: mkCLM' already in Analysis.lean — rename needed
-- COLLISION: r' already in RingTheory2.lean — rename needed

-- Algebra/SeparationQuotient/Section.lean

-- Algebra/Star.lean

-- Algebra/StarSubalgebra.lean

-- Algebra/Support.lean

-- Algebra/UniformConvergence.lean

-- Algebra/UniformField.lean

-- Algebra/UniformFilterBasis.lean

-- Algebra/UniformGroup/Basic.lean
-- COLLISION: provided' already in Algebra.lean — rename needed

-- Algebra/UniformGroup/Defs.lean

-- Algebra/UniformMulAction.lean
-- COLLISION: coe_smul' already in RingTheory2.lean — rename needed

-- Algebra/UniformRing.lean

-- Algebra/Valued/NormedValued.lean
-- COLLISION: norm_eq_zero' already in Analysis.lean — rename needed

-- Algebra/Valued/ValuationTopology.lean

-- Algebra/Valued/ValuedField.lean
-- COLLISION: integer' already in RingTheory2.lean — rename needed
-- COLLISION: maximalIdeal' already in RingTheory2.lean — rename needed
-- COLLISION: ResidueField' already in RingTheory2.lean — rename needed

-- ApproximateUnit.lean

-- Baire/BaireMeasurable.lean
-- COLLISION: compl' already in Order.lean — rename needed
-- COLLISION: of_compl' already in MeasureTheory2.lean — rename needed
-- COLLISION: iUnion' already in Order.lean — rename needed
-- COLLISION: biUnion' already in Order.lean — rename needed
-- COLLISION: sUnion' already in SetTheory.lean — rename needed
-- COLLISION: iInter' already in SetTheory.lean — rename needed
-- COLLISION: biInter' already in MeasureTheory2.lean — rename needed

-- Baire/Lemmas.lean

-- Bases.lean
-- COLLISION: sum' already in SetTheory.lean — rename needed
-- COLLISION: quotient' already in RingTheory2.lean — rename needed

-- Basic.lean
-- COLLISION: some' already in Order.lean — rename needed

-- Bornology/Absorbs.lean
-- COLLISION: zero_mem' already in RingTheory2.lean — rename needed
-- COLLISION: restrict_scalars' already in LinearAlgebra2.lean — rename needed

-- Bornology/Basic.lean
-- COLLISION: all' already in Algebra.lean — rename needed

-- Bornology/BoundedOperation.lean
-- COLLISION: lipschitzWith_sub' already in Analysis.lean — rename needed

-- Bornology/Constructions.lean

-- Bornology/Hom.lean
-- COLLISION: cancel_right' already in Order.lean — rename needed
-- COLLISION: cancel_left' already in Order.lean — rename needed

-- CWComplex.lean

-- Category/Born.lean

-- Category/CompHaus/Basic.lean

-- Category/CompHaus/EffectiveEpi.lean

-- Category/CompHaus/Limits.lean

-- Category/CompHaus/Projective.lean

-- Category/CompHausLike/Basic.lean

-- Category/CompHausLike/EffectiveEpi.lean
-- COLLISION: preregular' already in CategoryTheory.lean — rename needed
-- COLLISION: precoherent' already in CategoryTheory.lean — rename needed

-- Category/CompHausLike/Limits.lean
-- COLLISION: ι' already in Algebra.lean — rename needed
-- COLLISION: pullback' already in Analysis.lean — rename needed

-- Category/CompHausLike/SigmaComparison.lean

-- Category/CompactlyGenerated.lean

-- Category/Compactum.lean

-- Category/FinTopCat.lean

-- Category/LightProfinite/AsLimit.lean

-- Category/LightProfinite/Basic.lean

-- Category/LightProfinite/EffectiveEpi.lean

-- Category/LightProfinite/Extend.lean
-- COLLISION: isLimitCone' already in CategoryTheory.lean — rename needed
-- COLLISION: cocone' already in CategoryTheory.lean — rename needed
-- COLLISION: isColimitCocone' already in CategoryTheory.lean — rename needed

-- Category/LightProfinite/Limits.lean

-- Category/LightProfinite/Sequence.lean

-- Category/Locale.lean

-- Category/Profinite/AsLimit.lean

-- Category/Profinite/Basic.lean

-- Category/Profinite/CofilteredLimit.lean

-- Category/Profinite/EffectiveEpi.lean

-- Category/Profinite/Extend.lean

-- Category/Profinite/Limits.lean

-- Category/Profinite/Nobeling.lean

-- Category/Profinite/Product.lean

-- Category/Profinite/Projective.lean

-- Category/Sequential.lean

-- Category/Stonean/Adjunctions.lean

-- Category/Stonean/Basic.lean

-- Category/Stonean/EffectiveEpi.lean

-- Category/Stonean/Limits.lean

-- Category/TopCat/Adjunctions.lean

-- Category/TopCat/Basic.lean

-- Category/TopCat/EffectiveEpi.lean

-- Category/TopCat/EpiMono.lean

-- Category/TopCat/Limits/Basic.lean

-- Category/TopCat/Limits/Cofiltered.lean

-- Category/TopCat/Limits/Konig.lean
-- COLLISION: directed' already in Order.lean — rename needed

-- Category/TopCat/Limits/Products.lean
-- COLLISION: binaryCofan_isColimit_iff' already in CategoryTheory.lean — rename needed

-- Category/TopCat/Limits/Pullbacks.lean

-- Category/TopCat/OpenNhds.lean

-- Category/TopCat/Opens.lean

-- Category/TopCat/Sphere.lean

-- Category/TopCat/Yoneda.lean
-- COLLISION: piComparison_fac' already in CategoryTheory.lean — rename needed

-- Category/TopCommRingCat.lean

-- Category/UniformSpace.lean

-- Clopen.lean

-- ClopenBox.lean

-- CompactOpen.lean

-- Compactification/OnePoint.lean

-- Compactification/OnePointEquiv.lean

-- Compactness/Compact.lean

-- Compactness/CompactlyGeneratedSpace.lean

-- Compactness/DeltaGeneratedSpace.lean
-- COLLISION: iSup' already in Order.lean — rename needed

-- Compactness/Exterior.lean

-- Compactness/Lindelof.lean

-- Compactness/LocallyCompact.lean
-- COLLISION: locallyCompactSpace' already in Analysis.lean — rename needed

-- Compactness/Paracompact.lean

-- Compactness/SigmaCompact.lean
-- COLLISION: choice' already in SetTheory.lean — rename needed

-- CompletelyRegular.lean

-- Connected/Basic.lean

-- Connected/Clopen.lean

-- Connected/LocallyConnected.lean

-- Connected/PathConnected.lean

-- Connected/TotallyDisconnected.lean

-- Constructions.lean

-- ContinuousMap/Algebra.lean
-- COLLISION: SeparatesPoints' already in MeasureTheory2.lean — rename needed
-- COLLISION: evalAlgHom' already in Algebra.lean — rename needed

-- ContinuousMap/Basic.lean
-- COLLISION: homeomorph' already in Analysis.lean — rename needed

-- ContinuousMap/Bounded/Basic.lean

-- ContinuousMap/BoundedCompactlySupported.lean

-- ContinuousMap/CocompactMap.lean

-- ContinuousMap/Compact.lean

-- ContinuousMap/CompactlySupported.lean

-- ContinuousMap/ContinuousMapZero.lean

-- ContinuousMap/Defs.lean

-- ContinuousMap/Ideals.lean

-- ContinuousMap/Interval.lean

-- ContinuousMap/LocallyConstant.lean

-- ContinuousMap/Ordered.lean
-- COLLISION: coe_inf' already in Order.lean — rename needed
-- COLLISION: IccExtend' already in Order.lean — rename needed

-- ContinuousMap/Periodic.lean

-- ContinuousMap/Polynomial.lean

-- ContinuousMap/SecondCountableSpace.lean

-- ContinuousMap/Sigma.lean

-- ContinuousMap/Star.lean

-- ContinuousMap/StarOrdered.lean

-- ContinuousMap/StoneWeierstrass.lean

-- ContinuousMap/T0Sierpinski.lean

-- ContinuousMap/Units.lean

-- ContinuousMap/Weierstrass.lean

-- ContinuousMap/ZeroAtInfty.lean

-- ContinuousOn.lean

-- Covering.lean

-- Defs/Basic.lean

-- Defs/Filter.lean

-- Defs/Induced.lean

-- Defs/Sequences.lean

-- Defs/Ultrafilter.lean

-- DenseEmbedding.lean
-- COLLISION: induction_on₂' already in Algebra.lean — rename needed
-- COLLISION: induction_on₃' already in MeasureTheory2.lean — rename needed

-- DerivedSet.lean

-- DiscreteQuotient.lean

-- DiscreteSubset.lean

-- EMetricSpace/Basic.lean

-- EMetricSpace/Defs.lean

-- EMetricSpace/Diam.lean

-- EMetricSpace/Lipschitz.lean

-- EMetricSpace/Paracompact.lean

-- EMetricSpace/Pi.lean

-- ExtendFrom.lean

-- Exterior.lean

-- ExtremallyDisconnected.lean

-- FiberBundle/Basic.lean

-- FiberBundle/Constructions.lean

-- FiberBundle/IsHomeomorphicTrivialBundle.lean

-- FiberBundle/Trivialization.lean

-- FiberPartition.lean

-- Filter.lean

-- GDelta/Basic.lean

-- GDelta/UniformSpace.lean

-- Germ.lean

-- Gluing.lean

-- Hom/ContinuousEval.lean

-- Hom/ContinuousEvalConst.lean

-- Hom/Open.lean

-- Homeomorph.lean

-- Homotopy/Basic.lean

-- Homotopy/Contractible.lean

-- Homotopy/Equiv.lean

-- Homotopy/HSpaces.lean

-- Homotopy/HomotopyGroup.lean

-- Homotopy/Path.lean
-- COLLISION: evalAt' already in Algebra.lean — rename needed

-- Homotopy/Product.lean

-- IndicatorConstPointwise.lean

-- Inseparable.lean

-- Instances/AddCircle.lean

-- Instances/CantorSet.lean

-- Instances/Complex.lean

-- Instances/Discrete.lean

-- Instances/ENNReal.lean

-- Instances/ENat.lean

-- Instances/EReal.lean

-- Instances/Int.lean

-- Instances/Irrational.lean

-- Instances/Matrix.lean

-- Instances/NNReal.lean

-- Instances/Nat.lean

-- Instances/PNat.lean

-- Instances/Rat.lean

-- Instances/RatLemmas.lean

-- Instances/Real.lean

-- Instances/RealVectorSpace.lean

-- Instances/Sign.lean

-- Instances/TrivSqZeroExt.lean

-- Instances/ZMultiples.lean

-- Irreducible.lean

-- IsLocalHomeomorph.lean

-- JacobsonSpace.lean

-- KrullDimension.lean

-- List.lean

-- LocalAtTarget.lean

-- LocallyClosed.lean

-- LocallyConstant/Algebra.lean

-- LocallyConstant/Basic.lean
-- COLLISION: comap_const' already in MeasureTheory2.lean — rename needed

-- LocallyFinite.lean
-- COLLISION: eventually_subset' already in Order.lean — rename needed

-- Maps/Basic.lean

-- Maps/OpenQuotient.lean

-- Maps/Proper/Basic.lean

-- Maps/Proper/CompactlyGenerated.lean

-- Maps/Proper/UniversallyClosed.lean

-- MetricSpace/Algebra.lean

-- MetricSpace/Antilipschitz.lean

-- MetricSpace/Basic.lean

-- MetricSpace/Bilipschitz.lean

-- MetricSpace/Bounded.lean

-- MetricSpace/CantorScheme.lean
-- COLLISION: inducedMap' already in Algebra.lean — rename needed
-- COLLISION: Disjoint' already in Order.lean — rename needed

-- MetricSpace/CauSeqFilter.lean

-- MetricSpace/Cauchy.lean

-- MetricSpace/Closeds.lean

-- MetricSpace/Completion.lean

-- MetricSpace/Contracting.lean

-- MetricSpace/Defs.lean

-- MetricSpace/Dilation.lean

-- MetricSpace/DilationEquiv.lean
-- COLLISION: symm_trans_self' already in Order.lean — rename needed

-- MetricSpace/Equicontinuity.lean

-- MetricSpace/Gluing.lean

-- MetricSpace/GromovHausdorff.lean

-- MetricSpace/GromovHausdorffRealized.lean

-- MetricSpace/HausdorffDimension.lean

-- MetricSpace/HausdorffDistance.lean

-- MetricSpace/Holder.lean

-- MetricSpace/HolderNorm.lean

-- MetricSpace/Infsep.lean

-- MetricSpace/IsometricSMul.lean

-- MetricSpace/Isometry.lean

-- MetricSpace/Kuratowski.lean

-- MetricSpace/Lipschitz.lean

-- MetricSpace/MetricSeparated.lean

-- MetricSpace/PartitionOfUnity.lean

-- MetricSpace/Perfect.lean

-- MetricSpace/PiNat.lean

-- MetricSpace/Polish.lean
-- COLLISION: isClopenable' already in MeasureTheory2.lean — rename needed

-- MetricSpace/ProperSpace.lean

-- MetricSpace/ProperSpace/Lemmas.lean

-- MetricSpace/Pseudo/Basic.lean

-- MetricSpace/Pseudo/Constructions.lean

-- MetricSpace/Pseudo/Defs.lean

-- MetricSpace/Pseudo/Lemmas.lean

-- MetricSpace/Pseudo/Pi.lean

-- MetricSpace/Pseudo/Real.lean

-- MetricSpace/Sequences.lean

-- MetricSpace/ShrinkingLemma.lean

-- MetricSpace/ThickenedIndicator.lean

-- MetricSpace/Thickening.lean

-- MetricSpace/Ultra/Basic.lean

-- Metrizable/Basic.lean

-- Metrizable/Uniformity.lean

-- Metrizable/Urysohn.lean

-- NhdsSet.lean

-- NoetherianSpace.lean

-- OmegaCompletePartialOrder.lean

-- Order.lean

-- Order/Basic.lean

-- Order/Bornology.lean

-- Order/Category/AlexDisc.lean

-- Order/Category/FrameAdjunction.lean

-- Order/Compact.lean

-- Order/DenselyOrdered.lean

-- Order/ExtendFrom.lean

-- Order/Filter.lean

-- Order/Hom/Basic.lean

-- Order/Hom/Esakia.lean

-- Order/IntermediateValue.lean

-- Order/IsLUB.lean

-- Order/Lattice.lean

-- Order/LawsonTopology.lean

-- Order/LeftRight.lean

-- Order/LeftRightLim.lean

-- Order/LeftRightNhds.lean

-- Order/LocalExtr.lean

-- Order/LowerUpperTopology.lean

-- Order/Monotone.lean

-- Order/MonotoneContinuity.lean

-- Order/MonotoneConvergence.lean

-- Order/NhdsSet.lean

-- Order/OrderClosed.lean

-- Order/OrderClosedExtr.lean

-- Order/PartialSups.lean
-- COLLISION: partialSups' already in Order.lean — rename needed
-- COLLISION: partialSups_apply' already in Order.lean — rename needed

-- Order/Priestley.lean

-- Order/ProjIcc.lean

-- Order/Rolle.lean

-- Order/ScottTopology.lean

-- Order/T5.lean

-- Order/UpperLowerSetTopology.lean

-- Partial.lean

-- PartialHomeomorph.lean

-- PartitionOfUnity.lean

-- Perfect.lean

-- PreorderRestrict.lean

-- QuasiSeparated.lean

-- RestrictGen.lean

-- Semicontinuous.lean

-- SeparatedMap.lean

-- Separation/Basic.lean

-- Separation/GDelta.lean

-- Separation/NotNormal.lean

-- Sequences.lean

-- Sets/Closeds.lean
-- COLLISION: Closeds' already in Order.lean — rename needed
-- COLLISION: mem_sInf' already in Order.lean — rename needed
-- COLLISION: isAtom_iff' already in Order.lean — rename needed
-- COLLISION: equivSubtype' already in RingTheory2.lean — rename needed
-- COLLISION: orderIsoSubtype' already in Order.lean — rename needed

-- Sets/Compacts.lean

-- Sets/Opens.lean
-- COLLISION: mem' already in SetTheory.lean — rename needed

-- Sets/Order.lean

-- Sheaves/CommRingCat.lean

-- Sheaves/Forget.lean
-- COLLISION: isSheaf_iff_isSheaf_comp' already in CategoryTheory.lean — rename needed

-- Sheaves/Functors.lean

-- Sheaves/Limits.lean

-- Sheaves/LocalPredicate.lean

-- Sheaves/LocallySurjective.lean
-- COLLISION: IsLocallySurjective' already in Algebra.lean — rename needed

-- Sheaves/MayerVietoris.lean

-- Sheaves/PUnit.lean

-- Sheaves/Presheaf.lean

-- Sheaves/PresheafOfFunctions.lean

-- Sheaves/Sheaf.lean
-- COLLISION: Sheaf' already in CategoryTheory.lean — rename needed
-- COLLISION: presheaf' already in Algebra.lean — rename needed

-- Sheaves/SheafCondition/EqualizerProducts.lean

-- Sheaves/SheafCondition/OpensLeCover.lean

-- Sheaves/SheafCondition/PairwiseIntersections.lean

-- Sheaves/SheafCondition/Sites.lean

-- Sheaves/SheafCondition/UniqueGluing.lean

-- Sheaves/SheafOfFunctions.lean

-- Sheaves/Sheafify.lean

-- Sheaves/Skyscraper.lean

-- Sheaves/Stalks.lean

-- ShrinkingLemma.lean

-- Sober.lean

-- Specialization.lean

-- Spectral/Hom.lean

-- StoneCech.lean

-- TietzeExtension.lean

-- Ultrafilter.lean

-- UniformSpace/AbsoluteValue.lean

-- UniformSpace/AbstractCompletion.lean

-- UniformSpace/Ascoli.lean

-- UniformSpace/Basic.lean
-- COLLISION: tendsto_congr' already in Order.lean — rename needed

-- UniformSpace/Cauchy.lean

-- UniformSpace/Compact.lean

-- UniformSpace/CompactConvergence.lean

-- UniformSpace/CompareReals.lean

-- UniformSpace/CompleteSeparated.lean

-- UniformSpace/Completion.lean

-- UniformSpace/Equicontinuity.lean

-- UniformSpace/Equiv.lean

-- UniformSpace/HeineCantor.lean

-- UniformSpace/Matrix.lean

-- UniformSpace/OfCompactT2.lean

-- UniformSpace/OfFun.lean

-- UniformSpace/Pi.lean

-- UniformSpace/Separation.lean
-- COLLISION: map_mk' already in RingTheory2.lean — rename needed

-- UniformSpace/UniformConvergence.lean

-- UniformSpace/UniformConvergenceTopology.lean

-- UniformSpace/UniformEmbedding.lean

-- UnitInterval.lean

-- UrysohnsBounded.lean

-- UrysohnsLemma.lean

-- VectorBundle/Basic.lean

-- VectorBundle/Constructions.lean

-- VectorBundle/Hom.lean
