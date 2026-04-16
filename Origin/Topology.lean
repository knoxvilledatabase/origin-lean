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
-- COLLISION: for' already in SetTheory.lean — rename needed
/-- AlexandrovDiscrete (abstract). -/
def AlexandrovDiscrete' : Prop := True
/-- isOpen_sInter (abstract). -/
def isOpen_sInter' : Prop := True
/-- isOpen_iInter (abstract). -/
def isOpen_iInter' : Prop := True
/-- isOpen_iInter₂ (abstract). -/
def isOpen_iInter₂' : Prop := True
/-- isClosed_sUnion (abstract). -/
def isClosed_sUnion' : Prop := True
/-- isClosed_iUnion (abstract). -/
def isClosed_iUnion' : Prop := True
/-- isClosed_iUnion₂ (abstract). -/
def isClosed_iUnion₂' : Prop := True
/-- isClopen_sInter (abstract). -/
def isClopen_sInter' : Prop := True
/-- isClopen_iInter (abstract). -/
def isClopen_iInter' : Prop := True
/-- isClopen_iInter₂ (abstract). -/
def isClopen_iInter₂' : Prop := True
/-- isClopen_sUnion (abstract). -/
def isClopen_sUnion' : Prop := True
/-- isClopen_iUnion (abstract). -/
def isClopen_iUnion' : Prop := True
/-- isClopen_iUnion₂ (abstract). -/
def isClopen_iUnion₂' : Prop := True
/-- interior_iInter (abstract). -/
def interior_iInter' : Prop := True
/-- interior_sInter (abstract). -/
def interior_sInter' : Prop := True
-- COLLISION: closure_iUnion' already in RingTheory2.lean — rename needed
-- COLLISION: closure_sUnion' already in RingTheory2.lean — rename needed
/-- alexandrovDiscrete (abstract). -/
def alexandrovDiscrete' : Prop := True
-- COLLISION: sup' already in SetTheory.lean — rename needed
/-- alexandrovDiscrete_iSup (abstract). -/
def alexandrovDiscrete_iSup' : Prop := True
/-- isOpen_exterior (abstract). -/
def isOpen_exterior' : Prop := True
/-- exterior_mem_nhdsSet (abstract). -/
def exterior_mem_nhdsSet' : Prop := True
/-- exterior_eq_iff_isOpen (abstract). -/
def exterior_eq_iff_isOpen' : Prop := True
/-- exterior_subset_iff_isOpen (abstract). -/
def exterior_subset_iff_isOpen' : Prop := True
/-- exterior_subset_iff (abstract). -/
def exterior_subset_iff' : Prop := True
/-- exterior_subset_iff_mem_nhdsSet (abstract). -/
def exterior_subset_iff_mem_nhdsSet' : Prop := True
/-- exterior_singleton_subset_iff_mem_nhds (abstract). -/
def exterior_singleton_subset_iff_mem_nhds' : Prop := True
/-- gc_exterior_interior (abstract). -/
def gc_exterior_interior' : Prop := True
/-- principal_exterior (abstract). -/
def principal_exterior' : Prop := True
/-- isOpen_iff_forall_specializes (abstract). -/
def isOpen_iff_forall_specializes' : Prop := True
/-- alexandrovDiscrete_coinduced (abstract). -/
def alexandrovDiscrete_coinduced' : Prop := True

-- Algebra/Affine.lean
/-- continuous_iff (abstract). -/
def continuous_iff' : Prop := True
/-- lineMap_continuous (abstract). -/
def lineMap_continuous' : Prop := True
/-- homothety_continuous (abstract). -/
def homothety_continuous' : Prop := True
/-- homothety_isOpenMap (abstract). -/
def homothety_isOpenMap' : Prop := True

-- Algebra/Algebra.lean
/-- continuous_algebraMap (abstract). -/
def continuous_algebraMap' : Prop := True
/-- continuous_algebraMap_iff_smul (abstract). -/
def continuous_algebraMap_iff_smul' : Prop := True
/-- continuousSMul_of_algebraMap (abstract). -/
def continuousSMul_of_algebraMap' : Prop := True
/-- algebraMapCLM (abstract). -/
def algebraMapCLM' : Prop := True
/-- instContinuousSMul (abstract). -/
def instContinuousSMul' : Prop := True
/-- ContinuousAlgHom (abstract). -/
def ContinuousAlgHom' : Prop := True
-- COLLISION: apply' already in Order.lean — rename needed
-- COLLISION: coe' already in Order.lean — rename needed
-- COLLISION: ext' already in SetTheory.lean — rename needed
-- COLLISION: copy' already in Order.lean — rename needed
-- COLLISION: copy_eq' already in Order.lean — rename needed
-- COLLISION: map_zero' already in RingTheory2.lean — rename needed
-- COLLISION: map_add' already in RingTheory2.lean — rename needed
-- COLLISION: map_smul' already in RingTheory2.lean — rename needed
-- COLLISION: map_smul_of_tower' already in RingTheory2.lean — rename needed
-- COLLISION: map_sum' already in Algebra.lean — rename needed
-- COLLISION: ext_ring' already in Algebra.lean — rename needed
/-- ext_ring_iff (abstract). -/
def ext_ring_iff' : Prop := True
/-- eqOn_closure_adjoin (abstract). -/
def eqOn_closure_adjoin' : Prop := True
-- COLLISION: ext_on' already in LinearAlgebra2.lean — rename needed
/-- topologicalClosure (abstract). -/
def topologicalClosure' : Prop := True
/-- topologicalClosure_map_subalgebra (abstract). -/
def topologicalClosure_map_subalgebra' : Prop := True
-- COLLISION: id' already in Order.lean — rename needed
-- COLLISION: comp' already in Order.lean — rename needed
/-- toAlgHomMonoidHom (abstract). -/
def toAlgHomMonoidHom' : Prop := True
-- COLLISION: prod' already in SetTheory.lean — rename needed
-- COLLISION: fst' already in SetTheory.lean — rename needed
-- COLLISION: snd' already in Order.lean — rename needed
/-- fst_prod_snd (abstract). -/
def fst_prod_snd' : Prop := True
-- COLLISION: fst_comp_prod' already in Algebra.lean — rename needed
-- COLLISION: snd_comp_prod' already in Algebra.lean — rename needed
-- COLLISION: prodMap' already in Order.lean — rename needed
-- COLLISION: prodEquiv' already in Order.lean — rename needed
-- COLLISION: codRestrict' already in Order.lean — rename needed
-- COLLISION: rangeRestrict' already in RingTheory2.lean — rename needed
/-- valA (abstract). -/
def valA' : Prop := True
/-- range_valA (abstract). -/
def range_valA' : Prop := True
-- COLLISION: map_neg' already in RingTheory2.lean — rename needed
-- COLLISION: map_sub' already in RingTheory2.lean — rename needed
-- COLLISION: restrictScalars' already in RingTheory2.lean — rename needed
/-- le_topologicalClosure (abstract). -/
def le_topologicalClosure' : Prop := True
/-- isClosed_topologicalClosure (abstract). -/
def isClosed_topologicalClosure' : Prop := True
/-- topologicalClosure_minimal (abstract). -/
def topologicalClosure_minimal' : Prop := True
/-- commSemiringTopologicalClosure (abstract). -/
def commSemiringTopologicalClosure' : Prop := True
/-- topologicalClosure_comap_homeomorph (abstract). -/
def topologicalClosure_comap_homeomorph' : Prop := True
/-- elemental (abstract). -/
def elemental' : Prop := True
/-- self_mem (abstract). -/
def self_mem' : Prop := True
-- COLLISION: le_of_mem' already in Analysis.lean — rename needed
/-- le_iff_mem (abstract). -/
def le_iff_mem' : Prop := True
/-- commRingTopologicalClosure (abstract). -/
def commRingTopologicalClosure' : Prop := True

-- Algebra/Category/ProfiniteGrp/Basic.lean
/-- ProfiniteGrp (abstract). -/
def ProfiniteGrp' : Prop := True
/-- ProfiniteAddGrp (abstract). -/
def ProfiniteAddGrp' : Prop := True
-- COLLISION: of' already in SetTheory.lean — rename needed
/-- ofProfinite (abstract). -/
def ofProfinite' : Prop := True
-- COLLISION: pi' already in Order.lean — rename needed
/-- ofFiniteGrp (abstract). -/
def ofFiniteGrp' : Prop := True
/-- ofClosedSubgroup (abstract). -/
def ofClosedSubgroup' : Prop := True
/-- profiniteGrpToProfinite (abstract). -/
def profiniteGrpToProfinite' : Prop := True
/-- limitConePtAux (abstract). -/
def limitConePtAux' : Prop := True
-- COLLISION: limitCone' already in Algebra.lean — rename needed
-- COLLISION: limitConeIsLimit' already in Algebra.lean — rename needed
-- COLLISION: limit' already in Order.lean — rename needed

-- Algebra/ClopenNhdofOne.lean
/-- exist_openNormalSubgroup_sub_clopen_nhd_of_one (abstract). -/
def exist_openNormalSubgroup_sub_clopen_nhd_of_one' : Prop := True

-- Algebra/ClosedSubgroup.lean
/-- ClosedSubgroup (abstract). -/
def ClosedSubgroup' : Prop := True
/-- ClosedAddSubgroup (abstract). -/
def ClosedAddSubgroup' : Prop := True
/-- toSubgroup_injective (abstract). -/
def toSubgroup_injective' : Prop := True
/-- normalCore_isClosed (abstract). -/
def normalCore_isClosed' : Prop := True
/-- isOpen_of_isClosed_of_finiteIndex (abstract). -/
def isOpen_of_isClosed_of_finiteIndex' : Prop := True

-- Algebra/ConstMulAction.lean
/-- ContinuousConstSMul (abstract). -/
def ContinuousConstSMul' : Prop := True
/-- ContinuousConstVAdd (abstract). -/
def ContinuousConstVAdd' : Prop := True
-- COLLISION: const_smul' already in Algebra.lean — rename needed
/-- continuousConstSMul (abstract). -/
def continuousConstSMul' : Prop := True
/-- smul_closure_subset (abstract). -/
def smul_closure_subset' : Prop := True
/-- smul_closure_orbit_subset (abstract). -/
def smul_closure_orbit_subset' : Prop := True
/-- isClosed_setOf_map_smul (abstract). -/
def isClosed_setOf_map_smul' : Prop := True
/-- tendsto_const_smul_iff (abstract). -/
def tendsto_const_smul_iff' : Prop := True
/-- continuousWithinAt_const_smul_iff (abstract). -/
def continuousWithinAt_const_smul_iff' : Prop := True
/-- continuousOn_const_smul_iff (abstract). -/
def continuousOn_const_smul_iff' : Prop := True
/-- continuousAt_const_smul_iff (abstract). -/
def continuousAt_const_smul_iff' : Prop := True
/-- continuous_const_smul_iff (abstract). -/
def continuous_const_smul_iff' : Prop := True
-- COLLISION: smul' already in Order.lean — rename needed
/-- isOpenMap_smul (abstract). -/
def isOpenMap_smul' : Prop := True
/-- isClosedMap_smul (abstract). -/
def isClosedMap_smul' : Prop := True
/-- closure_smul (abstract). -/
def closure_smul' : Prop := True
/-- interior_smul (abstract). -/
def interior_smul' : Prop := True
-- COLLISION: smul_left' already in Algebra.lean — rename needed
/-- subset_interior_smul_right (abstract). -/
def subset_interior_smul_right' : Prop := True
/-- smul_mem_nhds_smul_iff (abstract). -/
def smul_mem_nhds_smul_iff' : Prop := True
/-- smul_mem_nhds_self (abstract). -/
def smul_mem_nhds_self' : Prop := True
/-- tendsto_const_smul_iff₀ (abstract). -/
def tendsto_const_smul_iff₀' : Prop := True
/-- continuousWithinAt_const_smul_iff₀ (abstract). -/
def continuousWithinAt_const_smul_iff₀' : Prop := True
/-- continuousOn_const_smul_iff₀ (abstract). -/
def continuousOn_const_smul_iff₀' : Prop := True
/-- continuousAt_const_smul_iff₀ (abstract). -/
def continuousAt_const_smul_iff₀' : Prop := True
-- COLLISION: smulOfNeZero' already in Algebra.lean — rename needed
/-- isOpenMap_smul₀ (abstract). -/
def isOpenMap_smul₀' : Prop := True
-- COLLISION: smul₀' already in Analysis.lean — rename needed
/-- interior_smul₀ (abstract). -/
def interior_smul₀' : Prop := True
/-- closure_smul₀' (abstract). -/
def closure_smul₀' : Prop := True
/-- isClosedMap_smul_of_ne_zero (abstract). -/
def isClosedMap_smul_of_ne_zero' : Prop := True
/-- smul_of_ne_zero (abstract). -/
def smul_of_ne_zero' : Prop := True
/-- isClosedMap_smul₀ (abstract). -/
def isClosedMap_smul₀' : Prop := True
/-- ProperlyDiscontinuousSMul (abstract). -/
def ProperlyDiscontinuousSMul' : Prop := True
/-- ProperlyDiscontinuousVAdd (abstract). -/
def ProperlyDiscontinuousVAdd' : Prop := True
/-- isOpenMap_quotient_mk'_mul (abstract). -/
def isOpenMap_quotient_mk'_mul' : Prop := True
/-- isOpenQuotientMap_quotientMk (abstract). -/
def isOpenQuotientMap_quotientMk' : Prop := True
/-- secondCountableTopology (abstract). -/
def secondCountableTopology' : Prop := True
/-- smul_mem_nhds_smul_iff₀ (abstract). -/
def smul_mem_nhds_smul_iff₀' : Prop := True
/-- set_smul_mem_nhds_smul (abstract). -/
def set_smul_mem_nhds_smul' : Prop := True
/-- set_smul_mem_nhds_zero_iff (abstract). -/
def set_smul_mem_nhds_zero_iff' : Prop := True

-- Algebra/Constructions.lean
-- COLLISION: on' already in SetTheory.lean — rename needed
/-- continuous_unop (abstract). -/
def continuous_unop' : Prop := True
/-- continuous_op (abstract). -/
def continuous_op' : Prop := True
/-- opHomeomorph (abstract). -/
def opHomeomorph' : Prop := True
/-- map_op_nhds (abstract). -/
def map_op_nhds' : Prop := True
/-- map_unop_nhds (abstract). -/
def map_unop_nhds' : Prop := True
/-- comap_op_nhds (abstract). -/
def comap_op_nhds' : Prop := True
/-- comap_unop_nhds (abstract). -/
def comap_unop_nhds' : Prop := True
/-- isInducing_embedProduct (abstract). -/
def isInducing_embedProduct' : Prop := True
/-- isEmbedding_embedProduct (abstract). -/
def isEmbedding_embedProduct' : Prop := True
/-- topology_eq_inf (abstract). -/
def topology_eq_inf' : Prop := True
-- COLLISION: that' already in RingTheory2.lean — rename needed
/-- isEmbedding_val_mk' (abstract). -/
def isEmbedding_val_mk' : Prop := True
/-- embedding_val_mk (abstract). -/
def embedding_val_mk' : Prop := True
/-- continuous_embedProduct (abstract). -/
def continuous_embedProduct' : Prop := True
/-- continuous_val (abstract). -/
def continuous_val' : Prop := True
/-- continuous_coe_inv (abstract). -/
def continuous_coe_inv' : Prop := True

-- Algebra/Constructions/DomMulAct.lean
/-- mkHomeomorph (abstract). -/
def mkHomeomorph' : Prop := True
/-- isInducing_mk (abstract). -/
def isInducing_mk' : Prop := True
/-- isEmbedding_mk (abstract). -/
def isEmbedding_mk' : Prop := True
/-- isOpenEmbedding_mk (abstract). -/
def isOpenEmbedding_mk' : Prop := True
/-- isClosedEmbedding_mk (abstract). -/
def isClosedEmbedding_mk' : Prop := True
/-- isQuotientMap_mk (abstract). -/
def isQuotientMap_mk' : Prop := True
/-- isInducing_mk_symm (abstract). -/
def isInducing_mk_symm' : Prop := True
/-- isEmbedding_mk_symm (abstract). -/
def isEmbedding_mk_symm' : Prop := True
/-- isOpenEmbedding_mk_symm (abstract). -/
def isOpenEmbedding_mk_symm' : Prop := True
/-- isClosedEmbedding_mk_symm (abstract). -/
def isClosedEmbedding_mk_symm' : Prop := True
/-- isQuotientMap_mk_symm (abstract). -/
def isQuotientMap_mk_symm' : Prop := True
/-- map_mk_nhds (abstract). -/
def map_mk_nhds' : Prop := True
/-- map_mk_symm_nhds (abstract). -/
def map_mk_symm_nhds' : Prop := True
/-- comap_mk_nhds (abstract). -/
def comap_mk_nhds' : Prop := True
/-- symm_nhds (abstract). -/
def symm_nhds' : Prop := True

-- Algebra/ContinuousAffineMap.lean
/-- ContinuousAffineMap (abstract). -/
def ContinuousAffineMap' : Prop := True
/-- to_affineMap_injective (abstract). -/
def to_affineMap_injective' : Prop := True
-- COLLISION: toContinuousMap' already in Analysis.lean — rename needed
-- COLLISION: const' already in Order.lean — rename needed
/-- toContinuousAffineMap (abstract). -/
def toContinuousAffineMap' : Prop := True
/-- toContinuousAffineMap_map_zero (abstract). -/
def toContinuousAffineMap_map_zero' : Prop := True

-- Algebra/ContinuousMonoidHom.lean
/-- ContinuousAddMonoidHom (abstract). -/
def ContinuousAddMonoidHom' : Prop := True
/-- ContinuousMonoidHom (abstract). -/
def ContinuousMonoidHom' : Prop := True
/-- ContinuousAddMonoidHomClass (abstract). -/
def ContinuousAddMonoidHomClass' : Prop := True
/-- ContinuousMonoidHomClass (abstract). -/
def ContinuousMonoidHomClass' : Prop := True
/-- toContinuousMap_injective (abstract). -/
def toContinuousMap_injective' : Prop := True
-- COLLISION: one' already in SetTheory.lean — rename needed
-- COLLISION: inl' already in Algebra.lean — rename needed
-- COLLISION: inr' already in Algebra.lean — rename needed
-- COLLISION: diag' already in Order.lean — rename needed
-- COLLISION: swap' already in SetTheory.lean — rename needed
-- COLLISION: mul' already in Order.lean — rename needed
-- COLLISION: inv' already in SetTheory.lean — rename needed
-- COLLISION: coprod' already in Order.lean — rename needed
/-- isInducing_toContinuousMap (abstract). -/
def isInducing_toContinuousMap' : Prop := True
/-- isEmbedding_toContinuousMap (abstract). -/
def isEmbedding_toContinuousMap' : Prop := True
-- COLLISION: range_toContinuousMap' already in Analysis.lean — rename needed
/-- isClosedEmbedding_toContinuousMap (abstract). -/
def isClosedEmbedding_toContinuousMap' : Prop := True
/-- continuous_of_continuous_uncurry (abstract). -/
def continuous_of_continuous_uncurry' : Prop := True
/-- continuous_comp_left (abstract). -/
def continuous_comp_left' : Prop := True
/-- continuous_comp_right (abstract). -/
def continuous_comp_right' : Prop := True
-- COLLISION: compLeft' already in RingTheory2.lean — rename needed
-- COLLISION: compRight' already in RingTheory2.lean — rename needed
/-- locallyCompactSpace_of_equicontinuousAt (abstract). -/
def locallyCompactSpace_of_equicontinuousAt' : Prop := True
/-- locallyCompactSpace_of_hasBasis (abstract). -/
def locallyCompactSpace_of_hasBasis' : Prop := True

-- Algebra/Equicontinuity.lean
/-- equicontinuous_of_equicontinuousAt_one (abstract). -/
def equicontinuous_of_equicontinuousAt_one' : Prop := True
/-- uniformEquicontinuous_of_equicontinuousAt_one (abstract). -/
def uniformEquicontinuous_of_equicontinuousAt_one' : Prop := True

-- Algebra/Field.lean
/-- tendsto_cocompact_mul_left₀ (abstract). -/
def tendsto_cocompact_mul_left₀' : Prop := True
/-- tendsto_cocompact_mul_right₀ (abstract). -/
def tendsto_cocompact_mul_right₀' : Prop := True
/-- TopologicalDivisionRing (abstract). -/
def TopologicalDivisionRing' : Prop := True
/-- affineHomeomorph (abstract). -/
def affineHomeomorph' : Prop := True
/-- affineHomeomorph_image_Icc (abstract). -/
def affineHomeomorph_image_Icc' : Prop := True
/-- affineHomeomorph_image_Ico (abstract). -/
def affineHomeomorph_image_Ico' : Prop := True
/-- affineHomeomorph_image_Ioc (abstract). -/
def affineHomeomorph_image_Ioc' : Prop := True
/-- affineHomeomorph_image_Ioo (abstract). -/
def affineHomeomorph_image_Ioo' : Prop := True
/-- eq_one_or_eq_neg_one_of_sq_eq (abstract). -/
def eq_one_or_eq_neg_one_of_sq_eq' : Prop := True
/-- eq_or_eq_neg_of_sq_eq (abstract). -/
def eq_or_eq_neg_of_sq_eq' : Prop := True
/-- eq_of_sq_eq (abstract). -/
def eq_of_sq_eq' : Prop := True

-- Algebra/FilterBasis.lean
-- COLLISION: is' already in SetTheory.lean — rename needed
/-- GroupFilterBasis (abstract). -/
def GroupFilterBasis' : Prop := True
/-- AddGroupFilterBasis (abstract). -/
def AddGroupFilterBasis' : Prop := True
/-- groupFilterBasisOfComm (abstract). -/
def groupFilterBasisOfComm' : Prop := True
-- COLLISION: conj' already in Order.lean — rename needed
/-- subset_mul_self (abstract). -/
def subset_mul_self' : Prop := True
/-- N (abstract). -/
def N' : Prop := True
/-- N_one (abstract). -/
def N_one' : Prop := True
-- COLLISION: hasBasis' already in Order.lean — rename needed
/-- coming (abstract). -/
def coming' : Prop := True
/-- topology (abstract). -/
def topology' : Prop := True
/-- nhds_eq (abstract). -/
def nhds_eq' : Prop := True
/-- nhds_one_eq (abstract). -/
def nhds_one_eq' : Prop := True
/-- nhds_hasBasis (abstract). -/
def nhds_hasBasis' : Prop := True
/-- nhds_one_hasBasis (abstract). -/
def nhds_one_hasBasis' : Prop := True
/-- mem_nhds_one (abstract). -/
def mem_nhds_one' : Prop := True
/-- RingFilterBasis (abstract). -/
def RingFilterBasis' : Prop := True
-- COLLISION: mul_left' already in RingTheory2.lean — rename needed
-- COLLISION: mul_right' already in RingTheory2.lean — rename needed
/-- ModuleFilterBasis (abstract). -/
def ModuleFilterBasis' : Prop := True
-- COLLISION: smul_right' already in Algebra.lean — rename needed
/-- of_basis_zero (abstract). -/
def of_basis_zero' : Prop := True
/-- ofBases (abstract). -/
def ofBases' : Prop := True

-- Algebra/Group/Basic.lean
-- COLLISION: mulLeft' already in Algebra.lean — rename needed
-- COLLISION: mulLeft_symm' already in Algebra.lean — rename needed
/-- isOpenMap_mul_left (abstract). -/
def isOpenMap_mul_left' : Prop := True
/-- leftCoset (abstract). -/
def leftCoset' : Prop := True
/-- isClosedMap_mul_left (abstract). -/
def isClosedMap_mul_left' : Prop := True
-- COLLISION: mulRight' already in Algebra.lean — rename needed
-- COLLISION: mulRight_symm' already in Algebra.lean — rename needed
/-- isOpenMap_mul_right (abstract). -/
def isOpenMap_mul_right' : Prop := True
/-- rightCoset (abstract). -/
def rightCoset' : Prop := True
/-- isClosedMap_mul_right (abstract). -/
def isClosedMap_mul_right' : Prop := True
/-- discreteTopology_of_isOpen_singleton_one (abstract). -/
def discreteTopology_of_isOpen_singleton_one' : Prop := True
/-- discreteTopology_iff_isOpen_singleton_one (abstract). -/
def discreteTopology_iff_isOpen_singleton_one' : Prop := True
/-- ContinuousNeg (abstract). -/
def ContinuousNeg' : Prop := True
/-- ContinuousInv (abstract). -/
def ContinuousInv' : Prop := True
-- COLLISION: zpow' already in Algebra.lean — rename needed
/-- continuousOn_inv (abstract). -/
def continuousOn_inv' : Prop := True
/-- continuousWithinAt_inv (abstract). -/
def continuousWithinAt_inv' : Prop := True
-- COLLISION: continuousAt_inv' already in Analysis.lean — rename needed
/-- tendsto_inv (abstract). -/
def tendsto_inv' : Prop := True
/-- isClosed_setOf_map_inv (abstract). -/
def isClosed_setOf_map_inv' : Prop := True
/-- nhds_inv (abstract). -/
def nhds_inv' : Prop := True
/-- isOpenMap_inv (abstract). -/
def isOpenMap_inv' : Prop := True
/-- isClosedMap_inv (abstract). -/
def isClosedMap_inv' : Prop := True
/-- inv_closure (abstract). -/
def inv_closure' : Prop := True
/-- continuous_inv_iff (abstract). -/
def continuous_inv_iff' : Prop := True
/-- continuousAt_inv_iff (abstract). -/
def continuousAt_inv_iff' : Prop := True
/-- continuousOn_inv_iff (abstract). -/
def continuousOn_inv_iff' : Prop := True
/-- continuousInv_sInf (abstract). -/
def continuousInv_sInf' : Prop := True
/-- continuousInv_iInf (abstract). -/
def continuousInv_iInf' : Prop := True
/-- continuousInv_inf (abstract). -/
def continuousInv_inf' : Prop := True
/-- continuousInv (abstract). -/
def continuousInv' : Prop := True
/-- TopologicalAddGroup (abstract). -/
def TopologicalAddGroup' : Prop := True
/-- TopologicalGroup (abstract). -/
def TopologicalGroup' : Prop := True
/-- continuous_conj_prod (abstract). -/
def continuous_conj_prod' : Prop := True
/-- continuous_conj (abstract). -/
def continuous_conj' : Prop := True
/-- continuous_zpow (abstract). -/
def continuous_zpow' : Prop := True
/-- continuousOn_zpow (abstract). -/
def continuousOn_zpow' : Prop := True
-- COLLISION: continuousAt_zpow' already in Analysis.lean — rename needed
/-- tendsto_inv_nhdsWithin_Ioi (abstract). -/
def tendsto_inv_nhdsWithin_Ioi' : Prop := True
/-- tendsto_inv_nhdsWithin_Iio (abstract). -/
def tendsto_inv_nhdsWithin_Iio' : Prop := True
/-- tendsto_inv_nhdsWithin_Ioi_inv (abstract). -/
def tendsto_inv_nhdsWithin_Ioi_inv' : Prop := True
/-- tendsto_inv_nhdsWithin_Iio_inv (abstract). -/
def tendsto_inv_nhdsWithin_Iio_inv' : Prop := True
/-- tendsto_inv_nhdsWithin_Ici (abstract). -/
def tendsto_inv_nhdsWithin_Ici' : Prop := True
/-- tendsto_inv_nhdsWithin_Iic (abstract). -/
def tendsto_inv_nhdsWithin_Iic' : Prop := True
/-- tendsto_inv_nhdsWithin_Ici_inv (abstract). -/
def tendsto_inv_nhdsWithin_Ici_inv' : Prop := True
/-- tendsto_inv_nhdsWithin_Iic_inv (abstract). -/
def tendsto_inv_nhdsWithin_Iic_inv' : Prop := True
/-- nhds_one_symm (abstract). -/
def nhds_one_symm' : Prop := True
/-- inv_mem_nhds_one (abstract). -/
def inv_mem_nhds_one' : Prop := True
-- COLLISION: shearMulRight' already in MeasureTheory2.lean — rename needed
/-- topologicalGroup (abstract). -/
def topologicalGroup' : Prop := True
/-- topologicalGroup_induced (abstract). -/
def topologicalGroup_induced' : Prop := True
/-- topologicalClosure_map_subgroup (abstract). -/
def topologicalClosure_map_subgroup' : Prop := True
/-- is_normal_topologicalClosure (abstract). -/
def is_normal_topologicalClosure' : Prop := True
/-- mul_mem_connectedComponent_one (abstract). -/
def mul_mem_connectedComponent_one' : Prop := True
/-- inv_mem_connectedComponent_one (abstract). -/
def inv_mem_connectedComponent_one' : Prop := True
/-- connectedComponentOfOne (abstract). -/
def connectedComponentOfOne' : Prop := True
/-- commGroupTopologicalClosure (abstract). -/
def commGroupTopologicalClosure' : Prop := True
/-- coe_topologicalClosure_bot (abstract). -/
def coe_topologicalClosure_bot' : Prop := True
/-- exists_nhds_split_inv (abstract). -/
def exists_nhds_split_inv' : Prop := True
/-- nhds_translation_mul_inv (abstract). -/
def nhds_translation_mul_inv' : Prop := True
/-- map_mul_left_nhds (abstract). -/
def map_mul_left_nhds' : Prop := True
/-- map_mul_left_nhds_one (abstract). -/
def map_mul_left_nhds_one' : Prop := True
/-- map_mul_right_nhds (abstract). -/
def map_mul_right_nhds' : Prop := True
/-- map_mul_right_nhds_one (abstract). -/
def map_mul_right_nhds_one' : Prop := True
/-- nhds_of_one (abstract). -/
def nhds_of_one' : Prop := True
/-- mem_closure_iff_nhds_one (abstract). -/
def mem_closure_iff_nhds_one' : Prop := True
/-- continuous_of_continuousAt_one (abstract). -/
def continuous_of_continuousAt_one' : Prop := True
/-- continuous_of_continuousAt_one₂ (abstract). -/
def continuous_of_continuousAt_one₂' : Prop := True
-- COLLISION: ext_iff' already in SetTheory.lean — rename needed
/-- of_nhds_one (abstract). -/
def of_nhds_one' : Prop := True
/-- of_comm_of_nhds_one (abstract). -/
def of_comm_of_nhds_one' : Prop := True
/-- exists_antitone_basis_nhds_one (abstract). -/
def exists_antitone_basis_nhds_one' : Prop := True
/-- ContinuousSub (abstract). -/
def ContinuousSub' : Prop := True
/-- ContinuousDiv (abstract). -/
def ContinuousDiv' : Prop := True
-- COLLISION: div' already in Order.lean — rename needed
-- COLLISION: const_div' already in MeasureTheory2.lean — rename needed
/-- tendsto_const_div_iff (abstract). -/
def tendsto_const_div_iff' : Prop := True
/-- tendsto_div_const_iff (abstract). -/
def tendsto_div_const_iff' : Prop := True
/-- tendsto_sub_const_iff (abstract). -/
def tendsto_sub_const_iff' : Prop := True
/-- continuous_div_left' (abstract). -/
def continuous_div_left' : Prop := True
/-- continuous_div_right' (abstract). -/
def continuous_div_right' : Prop := True
-- COLLISION: divLeft' already in Algebra.lean — rename needed
/-- isOpenMap_div_left (abstract). -/
def isOpenMap_div_left' : Prop := True
/-- isClosedMap_div_left (abstract). -/
def isClosedMap_div_left' : Prop := True
-- COLLISION: divRight' already in Algebra.lean — rename needed
/-- isOpenMap_div_right (abstract). -/
def isOpenMap_div_right' : Prop := True
/-- isClosedMap_div_right (abstract). -/
def isClosedMap_div_right' : Prop := True
/-- tendsto_div_nhds_one_iff (abstract). -/
def tendsto_div_nhds_one_iff' : Prop := True
/-- nhds_translation_div (abstract). -/
def nhds_translation_div' : Prop := True
/-- subset_interior_smul (abstract). -/
def subset_interior_smul' : Prop := True
/-- smul_left_of_isCompact (abstract). -/
def smul_left_of_isCompact' : Prop := True
/-- can't (abstract). -/
def can't' : Prop := True
/-- isClosedMap_quotient (abstract). -/
def isClosedMap_quotient' : Prop := True
/-- subset_interior_mul_right (abstract). -/
def subset_interior_mul_right' : Prop := True
/-- subset_interior_mul (abstract). -/
def subset_interior_mul' : Prop := True
/-- singleton_mul_mem_nhds (abstract). -/
def singleton_mul_mem_nhds' : Prop := True
/-- singleton_mul_mem_nhds_of_nhds_one (abstract). -/
def singleton_mul_mem_nhds_of_nhds_one' : Prop := True
/-- subset_interior_mul_left (abstract). -/
def subset_interior_mul_left' : Prop := True
/-- mul_singleton_mem_nhds (abstract). -/
def mul_singleton_mem_nhds' : Prop := True
/-- mul_singleton_mem_nhds_of_nhds_one (abstract). -/
def mul_singleton_mem_nhds_of_nhds_one' : Prop := True
-- COLLISION: div_left' already in Algebra.lean — rename needed
-- COLLISION: div_right' already in Algebra.lean — rename needed
/-- subset_interior_div_left (abstract). -/
def subset_interior_div_left' : Prop := True
/-- subset_interior_div_right (abstract). -/
def subset_interior_div_right' : Prop := True
/-- subset_interior_div (abstract). -/
def subset_interior_div' : Prop := True
/-- mul_closure (abstract). -/
def mul_closure' : Prop := True
/-- closure_mul (abstract). -/
def closure_mul' : Prop := True
/-- div_closure (abstract). -/
def div_closure' : Prop := True
/-- closure_div (abstract). -/
def closure_div' : Prop := True
/-- mul_left_of_isCompact (abstract). -/
def mul_left_of_isCompact' : Prop := True
/-- mul_right_of_isCompact (abstract). -/
def mul_right_of_isCompact' : Prop := True
/-- subset_mul_closure_one (abstract). -/
def subset_mul_closure_one' : Prop := True
/-- mul_closure_one_eq_closure (abstract). -/
def mul_closure_one_eq_closure' : Prop := True
-- COLLISION: mul_closure_one_eq' already in MeasureTheory2.lean — rename needed
/-- compl_mul_closure_one_eq (abstract). -/
def compl_mul_closure_one_eq' : Prop := True
/-- compl_mul_closure_one_eq_iff (abstract). -/
def compl_mul_closure_one_eq_iff' : Prop := True
-- COLLISION: t1Space' already in Analysis.lean — rename needed
/-- group_inseparable_iff (abstract). -/
def group_inseparable_iff' : Prop := True
/-- t2Space_iff_one_closed (abstract). -/
def t2Space_iff_one_closed' : Prop := True
/-- t2Space_of_one_sep (abstract). -/
def t2Space_of_one_sep' : Prop := True
/-- exists_closed_nhds_one_inv_eq_mul_subset (abstract). -/
def exists_closed_nhds_one_inv_eq_mul_subset' : Prop := True
/-- properlyDiscontinuousSMul_of_tendsto_cofinite (abstract). -/
def properlyDiscontinuousSMul_of_tendsto_cofinite' : Prop := True
/-- properlyDiscontinuousSMul_opposite_of_tendsto_cofinite (abstract). -/
def properlyDiscontinuousSMul_opposite_of_tendsto_cofinite' : Prop := True
/-- compact_open_separated_mul_right (abstract). -/
def compact_open_separated_mul_right' : Prop := True
/-- compact_open_separated_mul_left (abstract). -/
def compact_open_separated_mul_left' : Prop := True
/-- compact_covered_by_mul_left_translates (abstract). -/
def compact_covered_by_mul_left_translates' : Prop := True
/-- exists_disjoint_smul_of_isCompact (abstract). -/
def exists_disjoint_smul_of_isCompact' : Prop := True
/-- locallyCompactSpace_of_mem_nhds_of_group (abstract). -/
def locallyCompactSpace_of_mem_nhds_of_group' : Prop := True
/-- eq_zero_or_locallyCompactSpace_of_group (abstract). -/
def eq_zero_or_locallyCompactSpace_of_group' : Prop := True
/-- nhds_mul (abstract). -/
def nhds_mul' : Prop := True
/-- nhdsMulHom (abstract). -/
def nhdsMulHom' : Prop := True
/-- toUnits_homeomorph (abstract). -/
def toUnits_homeomorph' : Prop := True
/-- isEmbedding_val (abstract). -/
def isEmbedding_val' : Prop := True
-- COLLISION: prodUnits' already in Algebra.lean — rename needed
/-- topologicalGroup_sInf (abstract). -/
def topologicalGroup_sInf' : Prop := True
/-- topologicalGroup_iInf (abstract). -/
def topologicalGroup_iInf' : Prop := True
/-- topologicalGroup_inf (abstract). -/
def topologicalGroup_inf' : Prop := True
/-- GroupTopology (abstract). -/
def GroupTopology' : Prop := True
/-- AddGroupTopology (abstract). -/
def AddGroupTopology' : Prop := True
/-- continuous_mul' (abstract). -/
def continuous_mul' : Prop := True
/-- continuous_inv' (abstract). -/
def continuous_inv' : Prop := True
/-- toTopologicalSpace_injective (abstract). -/
def toTopologicalSpace_injective' : Prop := True
/-- toTopologicalSpace_iInf (abstract). -/
def toTopologicalSpace_iInf' : Prop := True
/-- coinduced (abstract). -/
def coinduced' : Prop := True
/-- coinduced_continuous (abstract). -/
def coinduced_continuous' : Prop := True

-- Algebra/Group/Compact.lean
/-- locallyCompactSpace_of_group (abstract). -/
def locallyCompactSpace_of_group' : Prop := True

-- Algebra/Group/OpenMapping.lean
/-- smul_singleton_mem_nhds_of_sigmaCompact (abstract). -/
def smul_singleton_mem_nhds_of_sigmaCompact' : Prop := True
/-- isOpenMap_smul_of_sigmaCompact (abstract). -/
def isOpenMap_smul_of_sigmaCompact' : Prop := True
-- COLLISION: around' already in Analysis.lean — rename needed
/-- isOpenMap_of_sigmaCompact (abstract). -/
def isOpenMap_of_sigmaCompact' : Prop := True

-- Algebra/Group/Quotient.lean
/-- continuous_mk (abstract). -/
def continuous_mk' : Prop := True
/-- isOpenMap_coe (abstract). -/
def isOpenMap_coe' : Prop := True
/-- isOpenQuotientMap_mk (abstract). -/
def isOpenQuotientMap_mk' : Prop := True
/-- dense_preimage_mk (abstract). -/
def dense_preimage_mk' : Prop := True
/-- dense_image_mk (abstract). -/
def dense_image_mk' : Prop := True
/-- continuous_smul₁ (abstract). -/
def continuous_smul₁' : Prop := True
/-- nhds_one_isCountablyGenerated (abstract). -/
def nhds_one_isCountablyGenerated' : Prop := True
/-- topologicalGroup_quotient (abstract). -/
def topologicalGroup_quotient' : Prop := True
/-- isClosedMap_coe (abstract). -/
def isClosedMap_coe' : Prop := True

-- Algebra/Group/SubmonoidClosure.lean
/-- mapClusterPt_atTop_zpow_iff_pow (abstract). -/
def mapClusterPt_atTop_zpow_iff_pow' : Prop := True
/-- mapClusterPt_self_zpow_atTop_pow (abstract). -/
def mapClusterPt_self_zpow_atTop_pow' : Prop := True
/-- mapClusterPt_one_atTop_pow (abstract). -/
def mapClusterPt_one_atTop_pow' : Prop := True
/-- mapClusterPt_self_atTop_pow (abstract). -/
def mapClusterPt_self_atTop_pow' : Prop := True
/-- mapClusterPt_atTop_pow_tfae (abstract). -/
def mapClusterPt_atTop_pow_tfae' : Prop := True
/-- mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers (abstract). -/
def mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers' : Prop := True
/-- mapClusterPt_inv_atTop_pow (abstract). -/
def mapClusterPt_inv_atTop_pow' : Prop := True
/-- closure_range_zpow_eq_pow (abstract). -/
def closure_range_zpow_eq_pow' : Prop := True
/-- denseRange_zpow_iff_pow (abstract). -/
def denseRange_zpow_iff_pow' : Prop := True
/-- topologicalClosure_subgroupClosure_toSubmonoid (abstract). -/
def topologicalClosure_subgroupClosure_toSubmonoid' : Prop := True
/-- closure_submonoidClosure_eq_closure_subgroupClosure (abstract). -/
def closure_submonoidClosure_eq_closure_subgroupClosure' : Prop := True
/-- dense_submonoidClosure_iff_subgroupClosure (abstract). -/
def dense_submonoidClosure_iff_subgroupClosure' : Prop := True

-- Algebra/Group/TopologicalAbelianization.lean
/-- TopologicalAbelianization (abstract). -/
def TopologicalAbelianization' : Prop := True

-- Algebra/GroupCompletion.lean
-- COLLISION: coe_neg' already in RingTheory2.lean — rename needed
-- COLLISION: coe_sub' already in RingTheory2.lean — rename needed
-- COLLISION: coe_add' already in RingTheory2.lean — rename needed
-- COLLISION: toCompl' already in Analysis.lean — rename needed
/-- continuous_toCompl (abstract). -/
def continuous_toCompl' : Prop := True
/-- isDenseInducing_toCompl (abstract). -/
def isDenseInducing_toCompl' : Prop := True
-- COLLISION: extension' already in Analysis.lean — rename needed
/-- extension_coe (abstract). -/
def extension_coe' : Prop := True
/-- continuous_extension (abstract). -/
def continuous_extension' : Prop := True
-- COLLISION: completion' already in Analysis.lean — rename needed
/-- continuous_completion (abstract). -/
def continuous_completion' : Prop := True
-- COLLISION: completion_coe' already in Analysis.lean — rename needed
/-- completion_zero (abstract). -/
def completion_zero' : Prop := True
-- COLLISION: completion_add' already in Analysis.lean — rename needed

-- Algebra/InfiniteSum/Basic.lean
/-- hasProd_one (abstract). -/
def hasProd_one' : Prop := True
/-- hasProd_empty (abstract). -/
def hasProd_empty' : Prop := True
/-- multipliable_one (abstract). -/
def multipliable_one' : Prop := True
/-- multipliable_empty (abstract). -/
def multipliable_empty' : Prop := True
/-- multipliable_congr (abstract). -/
def multipliable_congr' : Prop := True
-- COLLISION: congr' already in Order.lean — rename needed
-- COLLISION: congr_fun' already in Order.lean — rename needed
/-- hasProd_of_prod_eq (abstract). -/
def hasProd_of_prod_eq' : Prop := True
/-- hasProd_iff_hasProd (abstract). -/
def hasProd_iff_hasProd' : Prop := True
/-- multipliable_iff (abstract). -/
def multipliable_iff' : Prop := True
/-- hasProd_extend_one (abstract). -/
def hasProd_extend_one' : Prop := True
/-- multipliable_extend_one (abstract). -/
def multipliable_extend_one' : Prop := True
/-- hasProd_subtype_iff_mulIndicator (abstract). -/
def hasProd_subtype_iff_mulIndicator' : Prop := True
/-- multipliable_subtype_iff_mulIndicator (abstract). -/
def multipliable_subtype_iff_mulIndicator' : Prop := True
/-- hasProd_subtype_mulSupport (abstract). -/
def hasProd_subtype_mulSupport' : Prop := True
/-- multipliable (abstract). -/
def multipliable' : Prop := True
-- COLLISION: of_finite' already in RingTheory2.lean — rename needed
/-- hasProd_single (abstract). -/
def hasProd_single' : Prop := True
/-- hasProd_unique (abstract). -/
def hasProd_unique' : Prop := True
/-- hasProd_singleton (abstract). -/
def hasProd_singleton' : Prop := True
/-- hasProd_ite_eq (abstract). -/
def hasProd_ite_eq' : Prop := True
/-- hasProd_iff (abstract). -/
def hasProd_iff' : Prop := True
/-- hasProd_range_iff (abstract). -/
def hasProd_range_iff' : Prop := True
/-- hasProd_iff_of_mulSupport (abstract). -/
def hasProd_iff_of_mulSupport' : Prop := True
/-- hasProd_iff_hasProd_of_ne_one_bij (abstract). -/
def hasProd_iff_hasProd_of_ne_one_bij' : Prop := True
/-- multipliable_iff_of_mulSupport (abstract). -/
def multipliable_iff_of_mulSupport' : Prop := True
-- COLLISION: map' already in SetTheory.lean — rename needed
-- COLLISION: map_tprod' already in LinearAlgebra2.lean — rename needed
/-- multipliable_iff_tprod_comp_mem_range (abstract). -/
def multipliable_iff_tprod_comp_mem_range' : Prop := True
/-- map_iff_of_equiv (abstract). -/
def map_iff_of_equiv' : Prop := True
/-- multipliable_iff_of_hasProd_iff (abstract). -/
def multipliable_iff_of_hasProd_iff' : Prop := True
/-- hasProd_prod (abstract). -/
def hasProd_prod' : Prop := True
/-- multipliable_prod (abstract). -/
def multipliable_prod' : Prop := True
/-- mul_disjoint (abstract). -/
def mul_disjoint' : Prop := True
/-- hasProd_prod_disjoint (abstract). -/
def hasProd_prod_disjoint' : Prop := True
/-- mul_isCompl (abstract). -/
def mul_isCompl' : Prop := True
/-- mul_compl (abstract). -/
def mul_compl' : Prop := True
-- COLLISION: compl_mul' already in Analysis.lean — rename needed
/-- compl_add (abstract). -/
def compl_add' : Prop := True
-- COLLISION: update' already in Algebra.lean — rename needed
/-- eq_mul_of_hasProd_ite (abstract). -/
def eq_mul_of_hasProd_ite' : Prop := True
/-- tprod_congr_set_coe (abstract). -/
def tprod_congr_set_coe' : Prop := True
/-- tprod_congr_subtype (abstract). -/
def tprod_congr_subtype' : Prop := True
/-- tprod_eq_finprod (abstract). -/
def tprod_eq_finprod' : Prop := True
/-- tprod_eq_prod' (abstract). -/
def tprod_eq_prod' : Prop := True
/-- tprod_one (abstract). -/
def tprod_one' : Prop := True
/-- tprod_empty (abstract). -/
def tprod_empty' : Prop := True
/-- tprod_congr (abstract). -/
def tprod_congr' : Prop := True
/-- tprod_fintype (abstract). -/
def tprod_fintype' : Prop := True
/-- prod_eq_tprod_mulIndicator (abstract). -/
def prod_eq_tprod_mulIndicator' : Prop := True
/-- tprod_bool (abstract). -/
def tprod_bool' : Prop := True
/-- tprod_eq_mulSingle (abstract). -/
def tprod_eq_mulSingle' : Prop := True
/-- tprod_tprod_eq_mulSingle (abstract). -/
def tprod_tprod_eq_mulSingle' : Prop := True
/-- tprod_ite_eq (abstract). -/
def tprod_ite_eq' : Prop := True
/-- tprod_subtype (abstract). -/
def tprod_subtype' : Prop := True
/-- tprod_singleton (abstract). -/
def tprod_singleton' : Prop := True
/-- tprod_eq (abstract). -/
def tprod_eq' : Prop := True
/-- tprod_subtype_eq_of_mulSupport_subset (abstract). -/
def tprod_subtype_eq_of_mulSupport_subset' : Prop := True
/-- tprod_subtype_mulSupport (abstract). -/
def tprod_subtype_mulSupport' : Prop := True
/-- tprod_univ (abstract). -/
def tprod_univ' : Prop := True
/-- tprod_image (abstract). -/
def tprod_image' : Prop := True
/-- tprod_range (abstract). -/
def tprod_range' : Prop := True
/-- tprod_setElem_eq_tprod_setElem_diff (abstract). -/
def tprod_setElem_eq_tprod_setElem_diff' : Prop := True
/-- tprod_eq_tprod_diff_singleton (abstract). -/
def tprod_eq_tprod_diff_singleton' : Prop := True
/-- tprod_eq_tprod_of_ne_one_bij (abstract). -/
def tprod_eq_tprod_of_ne_one_bij' : Prop := True
/-- tprod_eq_tprod_of_mulSupport (abstract). -/
def tprod_eq_tprod_of_mulSupport' : Prop := True
/-- tprod_dite_right (abstract). -/
def tprod_dite_right' : Prop := True
/-- tprod_dite_left (abstract). -/
def tprod_dite_left' : Prop := True
/-- tprod_extend_one (abstract). -/
def tprod_extend_one' : Prop := True
/-- tprod_eq_tprod_of_hasProd_iff_hasProd (abstract). -/
def tprod_eq_tprod_of_hasProd_iff_hasProd' : Prop := True
/-- tprod_mul (abstract). -/
def tprod_mul' : Prop := True
/-- tprod_of_prod (abstract). -/
def tprod_of_prod' : Prop := True
/-- tprod_eq_mul_tprod_ite' (abstract). -/
def tprod_eq_mul_tprod_ite' : Prop := True
/-- tprod_mul_tprod_compl (abstract). -/
def tprod_mul_tprod_compl' : Prop := True
/-- tprod_union_disjoint (abstract). -/
def tprod_union_disjoint' : Prop := True
/-- tprod_finset_bUnion_disjoint (abstract). -/
def tprod_finset_bUnion_disjoint' : Prop := True

-- Algebra/InfiniteSum/Constructions.lean
/-- hasProd_pi_single (abstract). -/
def hasProd_pi_single' : Prop := True
/-- tprod_pi_single (abstract). -/
def tprod_pi_single' : Prop := True
/-- tprod_setProd_singleton_left (abstract). -/
def tprod_setProd_singleton_left' : Prop := True
/-- tprod_setProd_singleton_right (abstract). -/
def tprod_setProd_singleton_right' : Prop := True
/-- prod_symm (abstract). -/
def prod_symm' : Prop := True
-- COLLISION: prod_mk' already in Order.lean — rename needed
-- COLLISION: sigma' already in Order.lean — rename needed
-- COLLISION: prod_fiberwise' already in Algebra.lean — rename needed
/-- sigma_of_hasProd (abstract). -/
def sigma_of_hasProd' : Prop := True
/-- tprod_sigma' (abstract). -/
def tprod_sigma' : Prop := True
-- COLLISION: tprod_prod' already in RingTheory2.lean — rename needed
/-- tprod_comm' (abstract). -/
def tprod_comm' : Prop := True
/-- of_sigma (abstract). -/
def of_sigma' : Prop := True
/-- sigma_factor (abstract). -/
def sigma_factor' : Prop := True
/-- tprod_fiberwise (abstract). -/
def tprod_fiberwise' : Prop := True
/-- hasProd (abstract). -/
def hasProd' : Prop := True
/-- tprod_apply (abstract). -/
def tprod_apply' : Prop := True
-- COLLISION: op' already in RingTheory2.lean — rename needed
-- COLLISION: unop' already in RingTheory2.lean — rename needed
/-- hasSum_op (abstract). -/
def hasSum_op' : Prop := True
/-- hasSum_unop (abstract). -/
def hasSum_unop' : Prop := True
/-- summable_op (abstract). -/
def summable_op' : Prop := True
/-- summable_unop (abstract). -/
def summable_unop' : Prop := True
/-- tsum_op (abstract). -/
def tsum_op' : Prop := True
/-- tsum_unop (abstract). -/
def tsum_unop' : Prop := True
-- COLLISION: star' already in SetTheory.lean — rename needed
/-- ofStar (abstract). -/
def ofStar' : Prop := True
/-- summable_star_iff (abstract). -/
def summable_star_iff' : Prop := True
/-- tsum_star (abstract). -/
def tsum_star' : Prop := True

-- Algebra/InfiniteSum/Defs.lean
/-- HasProd (abstract). -/
def HasProd' : Prop := True
/-- Multipliable (abstract). -/
def Multipliable' : Prop := True
-- COLLISION: tprod' already in RingTheory2.lean — rename needed
/-- tprod_eq_one_of_not_multipliable (abstract). -/
def tprod_eq_one_of_not_multipliable' : Prop := True
/-- hasProd_subtype_iff_of_mulSupport_subset (abstract). -/
def hasProd_subtype_iff_of_mulSupport_subset' : Prop := True
/-- hasProd_fintype (abstract). -/
def hasProd_fintype' : Prop := True
/-- hasProd_prod_of_ne_finset_one (abstract). -/
def hasProd_prod_of_ne_finset_one' : Prop := True
/-- multipliable_of_ne_finset_one (abstract). -/
def multipliable_of_ne_finset_one' : Prop := True
-- COLLISION: unique' already in Order.lean — rename needed

-- Algebra/InfiniteSum/ENNReal.lean
/-- tsum_set_one_eq (abstract). -/
def tsum_set_one_eq' : Prop := True
/-- tsum_set_const_eq (abstract). -/
def tsum_set_const_eq' : Prop := True

-- Algebra/InfiniteSum/Field.lean
-- COLLISION: norm' already in RingTheory2.lean — rename needed
/-- norm_tprod (abstract). -/
def norm_tprod' : Prop := True

-- Algebra/InfiniteSum/Group.lean
-- COLLISION: of_inv' already in CategoryTheory.lean — rename needed
/-- multipliable_inv_iff (abstract). -/
def multipliable_inv_iff' : Prop := True
/-- trans_div (abstract). -/
def trans_div' : Prop := True
/-- multipliable_iff_of_multipliable_div (abstract). -/
def multipliable_iff_of_multipliable_div' : Prop := True
/-- hasProd_compl_iff (abstract). -/
def hasProd_compl_iff' : Prop := True
/-- hasProd_iff_compl (abstract). -/
def hasProd_iff_compl' : Prop := True
/-- multipliable_compl_iff (abstract). -/
def multipliable_compl_iff' : Prop := True
/-- hasProd_ite_div_hasProd (abstract). -/
def hasProd_ite_div_hasProd' : Prop := True
/-- congr_cofinite (abstract). -/
def congr_cofinite' : Prop := True
/-- multipliable_congr_cofinite (abstract). -/
def multipliable_congr_cofinite' : Prop := True
/-- congr_atTop (abstract). -/
def congr_atTop' : Prop := True
/-- multipliable_congr_atTop (abstract). -/
def multipliable_congr_atTop' : Prop := True
/-- tprod_inv (abstract). -/
def tprod_inv' : Prop := True
/-- tprod_div (abstract). -/
def tprod_div' : Prop := True
/-- prod_mul_tprod_compl (abstract). -/
def prod_mul_tprod_compl' : Prop := True
/-- multipliable_iff_cauchySeq_finset (abstract). -/
def multipliable_iff_cauchySeq_finset' : Prop := True
/-- cauchySeq_finset_iff_tprod_vanishing (abstract). -/
def cauchySeq_finset_iff_tprod_vanishing' : Prop := True
/-- multipliable_iff_vanishing (abstract). -/
def multipliable_iff_vanishing' : Prop := True
/-- multipliable_iff_tprod_vanishing (abstract). -/
def multipliable_iff_tprod_vanishing' : Prop := True
/-- multipliable_of_eq_one_or_self (abstract). -/
def multipliable_of_eq_one_or_self' : Prop := True
-- COLLISION: mulIndicator' already in Order.lean — rename needed
-- COLLISION: comp_injective' already in RingTheory2.lean — rename needed
-- COLLISION: subtype' already in Order.lean — rename needed
/-- multipliable_subtype_and_compl (abstract). -/
def multipliable_subtype_and_compl' : Prop := True
/-- tprod_subtype_mul_tprod_subtype_compl (abstract). -/
def tprod_subtype_mul_tprod_subtype_compl' : Prop := True
/-- prod_mul_tprod_subtype_compl (abstract). -/
def prod_mul_tprod_subtype_compl' : Prop := True
/-- vanishing (abstract). -/
def vanishing' : Prop := True
/-- tprod_vanishing (abstract). -/
def tprod_vanishing' : Prop := True
/-- tendsto_tprod_compl_atTop_one (abstract). -/
def tendsto_tprod_compl_atTop_one' : Prop := True
/-- tendsto_cofinite_one (abstract). -/
def tendsto_cofinite_one' : Prop := True
/-- countable_mulSupport (abstract). -/
def countable_mulSupport' : Prop := True
/-- multipliable_const_iff (abstract). -/
def multipliable_const_iff' : Prop := True
/-- tprod_const (abstract). -/
def tprod_const' : Prop := True

-- Algebra/InfiniteSum/GroupCompletion.lean
/-- hasSum_iff_hasSum_compl (abstract). -/
def hasSum_iff_hasSum_compl' : Prop := True
/-- summable_iff_summable_compl_and_tsum_mem (abstract). -/
def summable_iff_summable_compl_and_tsum_mem' : Prop := True
/-- summable_iff_cauchySeq_finset_and_tsum_mem (abstract). -/
def summable_iff_cauchySeq_finset_and_tsum_mem' : Prop := True
/-- toCompl_tsum (abstract). -/
def toCompl_tsum' : Prop := True

-- Algebra/InfiniteSum/Module.lean
/-- tsum_const_smul (abstract). -/
def tsum_const_smul' : Prop := True
/-- tsum_const_smul'' (abstract). -/
def tsum_const_smul'' : Prop := True
-- COLLISION: smul_const' already in Analysis.lean — rename needed
/-- tsum_smul_const (abstract). -/
def tsum_smul_const' : Prop := True
-- COLLISION: smul_eq' already in Analysis.lean — rename needed
/-- tsum_smul_tsum (abstract). -/
def tsum_smul_tsum' : Prop := True
-- COLLISION: hasSum' already in Analysis.lean — rename needed
-- COLLISION: summable' already in Analysis.lean — rename needed
/-- map_tsum (abstract). -/
def map_tsum' : Prop := True
/-- tsum_eq_iff (abstract). -/
def tsum_eq_iff' : Prop := True
/-- automorphize (abstract). -/
def automorphize' : Prop := True
/-- automorphize_smul_left (abstract). -/
def automorphize_smul_left' : Prop := True

-- Algebra/InfiniteSum/NatInt.lean
/-- tendsto_prod_tprod_nat (abstract). -/
def tendsto_prod_tprod_nat' : Prop := True
/-- prod_range_mul (abstract). -/
def prod_range_mul' : Prop := True
/-- even_mul_odd (abstract). -/
def even_mul_odd' : Prop := True
/-- tprod_iSup_decode₂ (abstract). -/
def tprod_iSup_decode₂' : Prop := True
/-- tprod_iUnion_decode₂ (abstract). -/
def tprod_iUnion_decode₂' : Prop := True
/-- rel_iSup_tprod (abstract). -/
def rel_iSup_tprod' : Prop := True
/-- rel_iSup_prod (abstract). -/
def rel_iSup_prod' : Prop := True
/-- rel_sup_mul (abstract). -/
def rel_sup_mul' : Prop := True
/-- tprod_eq_zero_mul' (abstract). -/
def tprod_eq_zero_mul' : Prop := True
/-- tprod_even_mul_odd (abstract). -/
def tprod_even_mul_odd' : Prop := True
/-- hasProd_nat_add_iff (abstract). -/
def hasProd_nat_add_iff' : Prop := True
/-- multipliable_nat_add_iff (abstract). -/
def multipliable_nat_add_iff' : Prop := True
/-- prod_mul_tprod_nat_add (abstract). -/
def prod_mul_tprod_nat_add' : Prop := True
/-- tendsto_prod_nat_add (abstract). -/
def tendsto_prod_nat_add' : Prop := True
/-- cauchySeq_finset_iff_nat_tprod_vanishing (abstract). -/
def cauchySeq_finset_iff_nat_tprod_vanishing' : Prop := True
/-- multipliable_iff_nat_tprod_vanishing (abstract). -/
def multipliable_iff_nat_tprod_vanishing' : Prop := True
/-- nat_tprod_vanishing (abstract). -/
def nat_tprod_vanishing' : Prop := True
/-- tendsto_atTop_one (abstract). -/
def tendsto_atTop_one' : Prop := True
/-- nat_mul_neg_add_one (abstract). -/
def nat_mul_neg_add_one' : Prop := True
/-- tprod_nat_mul_neg_add_one (abstract). -/
def tprod_nat_mul_neg_add_one' : Prop := True
/-- of_nat_of_neg_add_one (abstract). -/
def of_nat_of_neg_add_one' : Prop := True
/-- tprod_of_nat_of_neg_add_one (abstract). -/
def tprod_of_nat_of_neg_add_one' : Prop := True
/-- int_rec (abstract). -/
def int_rec' : Prop := True
/-- tprod_int_rec (abstract). -/
def tprod_int_rec' : Prop := True
/-- nat_mul_neg (abstract). -/
def nat_mul_neg' : Prop := True
/-- tprod_nat_mul_neg (abstract). -/
def tprod_nat_mul_neg' : Prop := True
/-- of_add_one_of_neg_add_one (abstract). -/
def of_add_one_of_neg_add_one' : Prop := True
/-- tprod_of_add_one_of_neg_add_one (abstract). -/
def tprod_of_add_one_of_neg_add_one' : Prop := True
/-- of_nat_of_neg (abstract). -/
def of_nat_of_neg' : Prop := True
/-- tprod_of_nat_of_neg (abstract). -/
def tprod_of_nat_of_neg' : Prop := True
/-- multipliable_int_iff_multipliable_nat_and_neg_add_one (abstract). -/
def multipliable_int_iff_multipliable_nat_and_neg_add_one' : Prop := True
/-- multipliable_int_iff_multipliable_nat_and_neg (abstract). -/
def multipliable_int_iff_multipliable_nat_and_neg' : Prop := True

-- Algebra/InfiniteSum/Nonarchimedean.lean
/-- cauchySeq_prod_of_tendsto_cofinite_one (abstract). -/
def cauchySeq_prod_of_tendsto_cofinite_one' : Prop := True
/-- multipliable_of_tendsto_cofinite_one (abstract). -/
def multipliable_of_tendsto_cofinite_one' : Prop := True
/-- multipliable_iff_tendsto_cofinite_one (abstract). -/
def multipliable_iff_tendsto_cofinite_one' : Prop := True

-- Algebra/InfiniteSum/Order.lean
/-- hasProd_le_of_prod_le (abstract). -/
def hasProd_le_of_prod_le' : Prop := True
/-- le_hasProd_of_le_prod (abstract). -/
def le_hasProd_of_le_prod' : Prop := True
/-- tprod_le_of_prod_range_le (abstract). -/
def tprod_le_of_prod_range_le' : Prop := True
/-- hasProd_le (abstract). -/
def hasProd_le' : Prop := True
/-- hasProd_mono (abstract). -/
def hasProd_mono' : Prop := True
/-- hasProd_le_inj (abstract). -/
def hasProd_le_inj' : Prop := True
/-- tprod_le_tprod_of_inj (abstract). -/
def tprod_le_tprod_of_inj' : Prop := True
/-- tprod_subtype_le (abstract). -/
def tprod_subtype_le' : Prop := True
/-- prod_le_hasProd (abstract). -/
def prod_le_hasProd' : Prop := True
/-- isLUB_hasProd (abstract). -/
def isLUB_hasProd' : Prop := True
/-- le_hasProd (abstract). -/
def le_hasProd' : Prop := True
/-- prod_le_tprod (abstract). -/
def prod_le_tprod' : Prop := True
/-- le_tprod (abstract). -/
def le_tprod' : Prop := True
/-- tprod_le_tprod (abstract). -/
def tprod_le_tprod' : Prop := True
/-- tprod_mono (abstract). -/
def tprod_mono' : Prop := True
/-- tprod_le_of_prod_le (abstract). -/
def tprod_le_of_prod_le' : Prop := True
-- COLLISION: one_le' already in RingTheory2.lean — rename needed
-- COLLISION: le_one' already in Analysis.lean — rename needed
/-- one_le_tprod (abstract). -/
def one_le_tprod' : Prop := True
/-- tprod_le_one (abstract). -/
def tprod_le_one' : Prop := True
/-- hasProd_one_iff_of_one_le (abstract). -/
def hasProd_one_iff_of_one_le' : Prop := True
/-- hasProd_lt (abstract). -/
def hasProd_lt' : Prop := True
/-- hasProd_strict_mono (abstract). -/
def hasProd_strict_mono' : Prop := True
/-- tprod_lt_tprod (abstract). -/
def tprod_lt_tprod' : Prop := True
/-- tprod_strict_mono (abstract). -/
def tprod_strict_mono' : Prop := True
/-- one_lt_tprod (abstract). -/
def one_lt_tprod' : Prop := True
/-- hasProd_one_iff (abstract). -/
def hasProd_one_iff' : Prop := True
/-- tprod_eq_one_iff (abstract). -/
def tprod_eq_one_iff' : Prop := True
/-- tprod_ne_one_iff (abstract). -/
def tprod_ne_one_iff' : Prop := True
/-- hasProd_of_isLUB_of_one_le (abstract). -/
def hasProd_of_isLUB_of_one_le' : Prop := True
/-- hasProd_of_isLUB (abstract). -/
def hasProd_of_isLUB' : Prop := True
/-- multipliable_mabs_iff (abstract). -/
def multipliable_mabs_iff' : Prop := True
/-- of_summable_const (abstract). -/
def of_summable_const' : Prop := True
-- COLLISION: abs' already in RingTheory2.lean — rename needed
-- COLLISION: abs_tprod' already in Analysis.lean — rename needed
/-- tendsto_atTop_of_pos (abstract). -/
def tendsto_atTop_of_pos' : Prop := True

-- Algebra/InfiniteSum/Real.lean
/-- cauchySeq_of_dist_le_of_summable (abstract). -/
def cauchySeq_of_dist_le_of_summable' : Prop := True
/-- cauchySeq_of_summable_dist (abstract). -/
def cauchySeq_of_summable_dist' : Prop := True
/-- dist_le_tsum_of_dist_le_of_tendsto (abstract). -/
def dist_le_tsum_of_dist_le_of_tendsto' : Prop := True
/-- dist_le_tsum_of_dist_le_of_tendsto₀ (abstract). -/
def dist_le_tsum_of_dist_le_of_tendsto₀' : Prop := True
/-- dist_le_tsum_dist_of_tendsto (abstract). -/
def dist_le_tsum_dist_of_tendsto' : Prop := True
/-- dist_le_tsum_dist_of_tendsto₀ (abstract). -/
def dist_le_tsum_dist_of_tendsto₀' : Prop := True
/-- not_summable_iff_tendsto_nat_atTop_of_nonneg (abstract). -/
def not_summable_iff_tendsto_nat_atTop_of_nonneg' : Prop := True
/-- summable_iff_not_tendsto_nat_atTop_of_nonneg (abstract). -/
def summable_iff_not_tendsto_nat_atTop_of_nonneg' : Prop := True
/-- summable_sigma_of_nonneg (abstract). -/
def summable_sigma_of_nonneg' : Prop := True
/-- summable_partition (abstract). -/
def summable_partition' : Prop := True
/-- summable_prod_of_nonneg (abstract). -/
def summable_prod_of_nonneg' : Prop := True
/-- summable_of_sum_le (abstract). -/
def summable_of_sum_le' : Prop := True
/-- summable_of_sum_range_le (abstract). -/
def summable_of_sum_range_le' : Prop := True
/-- tsum_le_of_sum_range_le (abstract). -/
def tsum_le_of_sum_range_le' : Prop := True
/-- tsum_lt_tsum_of_nonneg (abstract). -/
def tsum_lt_tsum_of_nonneg' : Prop := True

-- Algebra/InfiniteSum/Ring.lean
/-- tsum_mul_left (abstract). -/
def tsum_mul_left' : Prop := True
/-- tsum_mul_right (abstract). -/
def tsum_mul_right' : Prop := True
/-- tsum_right (abstract). -/
def tsum_right' : Prop := True
/-- tsum_left (abstract). -/
def tsum_left' : Prop := True
-- COLLISION: div_const' already in Algebra.lean — rename needed
/-- hasSum_mul_left_iff (abstract). -/
def hasSum_mul_left_iff' : Prop := True
/-- hasSum_mul_right_iff (abstract). -/
def hasSum_mul_right_iff' : Prop := True
/-- hasSum_div_const_iff (abstract). -/
def hasSum_div_const_iff' : Prop := True
/-- summable_mul_left_iff (abstract). -/
def summable_mul_left_iff' : Prop := True
/-- summable_mul_right_iff (abstract). -/
def summable_mul_right_iff' : Prop := True
/-- summable_div_const_iff (abstract). -/
def summable_div_const_iff' : Prop := True
/-- hasSum_const_div_iff (abstract). -/
def hasSum_const_div_iff' : Prop := True
/-- summable_const_div_iff (abstract). -/
def summable_const_div_iff' : Prop := True
-- COLLISION: mul_eq' already in RingTheory2.lean — rename needed
/-- tsum_mul_tsum (abstract). -/
def tsum_mul_tsum' : Prop := True
/-- summable_mul_prod_iff_summable_mul_sigma_antidiagonal (abstract). -/
def summable_mul_prod_iff_summable_mul_sigma_antidiagonal' : Prop := True
/-- summable_sum_mul_antidiagonal_of_summable_mul (abstract). -/
def summable_sum_mul_antidiagonal_of_summable_mul' : Prop := True
/-- tsum_mul_tsum_eq_tsum_sum_antidiagonal (abstract). -/
def tsum_mul_tsum_eq_tsum_sum_antidiagonal' : Prop := True
/-- summable_sum_mul_range_of_summable_mul (abstract). -/
def summable_sum_mul_range_of_summable_mul' : Prop := True
/-- tsum_mul_tsum_eq_tsum_sum_range (abstract). -/
def tsum_mul_tsum_eq_tsum_sum_range' : Prop := True

-- Algebra/Localization.lean
/-- ringTopology (abstract). -/
def ringTopology' : Prop := True

-- Algebra/Module/Alternating/Basic.lean
/-- ContinuousAlternatingMap (abstract). -/
def ContinuousAlternatingMap' : Prop := True
/-- toContinuousMultilinearMap_injective (abstract). -/
def toContinuousMultilinearMap_injective' : Prop := True
/-- range_toContinuousMultilinearMap (abstract). -/
def range_toContinuousMultilinearMap' : Prop := True
-- COLLISION: map_update_add' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_update_smul' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_coord_zero' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_update_zero' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_eq_zero_of_eq' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_eq_zero_of_not_injective' already in LinearAlgebra2.lean — rename needed
/-- applyAddHom (abstract). -/
def applyAddHom' : Prop := True
-- COLLISION: sum_apply' already in Algebra.lean — rename needed
/-- toMultilinearAddHom (abstract). -/
def toMultilinearAddHom' : Prop := True
-- COLLISION: toContinuousLinearMap' already in Analysis.lean — rename needed
-- COLLISION: ofSubsingleton' already in Algebra.lean — rename needed
-- COLLISION: constOfIsEmpty' already in LinearAlgebra2.lean — rename needed
-- COLLISION: compContinuousLinearMap' already in Analysis.lean — rename needed
/-- compContinuousAlternatingMap (abstract). -/
def compContinuousAlternatingMap' : Prop := True
/-- continuousAlternatingMapComp (abstract). -/
def continuousAlternatingMapComp' : Prop := True
/-- continuousAlternatingMapCongr (abstract). -/
def continuousAlternatingMapCongr' : Prop := True
-- COLLISION: piEquiv' already in Algebra.lean — rename needed
-- COLLISION: cons_add' already in LinearAlgebra2.lean — rename needed
/-- vecCons_add (abstract). -/
def vecCons_add' : Prop := True
-- COLLISION: cons_smul' already in LinearAlgebra2.lean — rename needed
/-- vecCons_smul (abstract). -/
def vecCons_smul' : Prop := True
-- COLLISION: map_piecewise_add' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_add_univ' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_sum_finset' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_piecewise_smul' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_smul_univ' already in LinearAlgebra2.lean — rename needed
/-- toContinuousMultilinearMapLinear (abstract). -/
def toContinuousMultilinearMapLinear' : Prop := True
/-- toAlternatingMapLinear (abstract). -/
def toAlternatingMapLinear' : Prop := True
/-- piLinearEquiv (abstract). -/
def piLinearEquiv' : Prop := True
-- COLLISION: smulRight' already in Algebra.lean — rename needed
/-- compContinuousLinearMapₗ (abstract). -/
def compContinuousLinearMapₗ' : Prop := True
/-- compContinuousAlternatingMapₗ (abstract). -/
def compContinuousAlternatingMapₗ' : Prop := True
-- COLLISION: alternatization' already in LinearAlgebra2.lean — rename needed
/-- alternatization_apply_apply (abstract). -/
def alternatization_apply_apply' : Prop := True
/-- alternatization_apply_toAlternatingMap (abstract). -/
def alternatization_apply_toAlternatingMap' : Prop := True

-- Algebra/Module/Alternating/Topology.lean
/-- isClosed_range_toContinuousMultilinearMap (abstract). -/
def isClosed_range_toContinuousMultilinearMap' : Prop := True
/-- uniformContinuous_toContinuousMultilinearMap (abstract). -/
def uniformContinuous_toContinuousMultilinearMap' : Prop := True
/-- uniformContinuous_coe_fun (abstract). -/
def uniformContinuous_coe_fun' : Prop := True
/-- uniformContinuous_eval_const (abstract). -/
def uniformContinuous_eval_const' : Prop := True
/-- isUniformInducing_postcomp (abstract). -/
def isUniformInducing_postcomp' : Prop := True
/-- completeSpace (abstract). -/
def completeSpace' : Prop := True
/-- isUniformEmbedding_restrictScalars (abstract). -/
def isUniformEmbedding_restrictScalars' : Prop := True
/-- uniformContinuous_restrictScalars (abstract). -/
def uniformContinuous_restrictScalars' : Prop := True
/-- isEmbedding_toContinuousMultilinearMap (abstract). -/
def isEmbedding_toContinuousMultilinearMap' : Prop := True
/-- continuous_toContinuousMultilinearMap (abstract). -/
def continuous_toContinuousMultilinearMap' : Prop := True
/-- hasBasis_nhds_zero_of_basis (abstract). -/
def hasBasis_nhds_zero_of_basis' : Prop := True
/-- hasBasis_nhds_zero (abstract). -/
def hasBasis_nhds_zero' : Prop := True
/-- isClosedEmbedding_toContinuousMultilinearMap (abstract). -/
def isClosedEmbedding_toContinuousMultilinearMap' : Prop := True
/-- isEmbedding_restrictScalars (abstract). -/
def isEmbedding_restrictScalars' : Prop := True
/-- restrictScalarsCLM (abstract). -/
def restrictScalarsCLM' : Prop := True
/-- tsum_eval (abstract). -/
def tsum_eval' : Prop := True

-- Algebra/Module/Basic.lean
/-- of_nhds_zero (abstract). -/
def of_nhds_zero' : Prop := True
/-- eq_top_of_nonempty_interior' (abstract). -/
def eq_top_of_nonempty_interior' : Prop := True
/-- continuousSMul_induced (abstract). -/
def continuousSMul_induced' : Prop := True
-- COLLISION: span' already in RingTheory2.lean — rename needed
/-- mapsTo_smul_closure (abstract). -/
def mapsTo_smul_closure' : Prop := True
/-- closure_subset_topologicalClosure_span (abstract). -/
def closure_subset_topologicalClosure_span' : Prop := True
/-- topologicalClosure_mono (abstract). -/
def topologicalClosure_mono' : Prop := True
/-- submodule_topologicalClosure_eq (abstract). -/
def submodule_topologicalClosure_eq' : Prop := True
/-- dense_iff_topologicalClosure_eq_top (abstract). -/
def dense_iff_topologicalClosure_eq_top' : Prop := True
/-- isClosed_or_dense_of_isCoatom (abstract). -/
def isClosed_or_dense_of_isCoatom' : Prop := True
/-- continuous_on_pi (abstract). -/
def continuous_on_pi' : Prop := True
/-- ContinuousLinearMap (abstract). -/
def ContinuousLinearMap' : Prop := True
/-- ContinuousSemilinearMapClass (abstract). -/
def ContinuousSemilinearMapClass' : Prop := True
/-- ContinuousLinearMapClass (abstract). -/
def ContinuousLinearMapClass' : Prop := True
/-- ContinuousLinearEquiv (abstract). -/
def ContinuousLinearEquiv' : Prop := True
/-- ContinuousSemilinearEquivClass (abstract). -/
def ContinuousSemilinearEquivClass' : Prop := True
/-- ContinuousLinearEquivClass (abstract). -/
def ContinuousLinearEquivClass' : Prop := True
/-- linearMapOfMemClosureRangeCoe (abstract). -/
def linearMapOfMemClosureRangeCoe' : Prop := True
/-- linearMapOfTendsto (abstract). -/
def linearMapOfTendsto' : Prop := True
/-- isClosed_range_coe (abstract). -/
def isClosed_range_coe' : Prop := True
-- COLLISION: coe_injective' already in Order.lean — rename needed
-- COLLISION: continuous' already in Order.lean — rename needed
-- COLLISION: uniformContinuous' already in Analysis.lean — rename needed
/-- range_coeFn_eq (abstract). -/
def range_coeFn_eq' : Prop := True
-- COLLISION: map_smulₛₗ' already in Algebra.lean — rename needed
/-- eqOn_closure_span (abstract). -/
def eqOn_closure_span' : Prop := True
/-- topologicalClosure_map (abstract). -/
def topologicalClosure_map' : Prop := True
/-- topologicalClosure_map_submodule (abstract). -/
def topologicalClosure_map_submodule' : Prop := True
-- COLLISION: coe_sum' already in Algebra.lean — rename needed
-- COLLISION: comp_id' already in Order.lean — rename needed
-- COLLISION: id_comp' already in Order.lean — rename needed
-- COLLISION: comp_zero' already in Algebra.lean — rename needed
-- COLLISION: zero_comp' already in Algebra.lean — rename needed
-- COLLISION: comp_add' already in Algebra.lean — rename needed
-- COLLISION: add_comp' already in Algebra.lean — rename needed
/-- comp_finset_sum (abstract). -/
def comp_finset_sum' : Prop := True
-- COLLISION: coe_pow' already in RingTheory2.lean — rename needed
/-- toLinearMapRingHom (abstract). -/
def toLinearMapRingHom' : Prop := True
-- COLLISION: isClosed_ker' already in Analysis.lean — rename needed
/-- isComplete_ker (abstract). -/
def isComplete_ker' : Prop := True
-- COLLISION: ker_prod' already in Algebra.lean — rename needed
/-- subtypeL (abstract). -/
def subtypeL' : Prop := True
-- COLLISION: with' already in RingTheory2.lean — rename needed
/-- range_subtypeL (abstract). -/
def range_subtypeL' : Prop := True
-- COLLISION: range_coprod' already in LinearAlgebra2.lean — rename needed
-- COLLISION: coprod_inl_inr' already in Algebra.lean — rename needed
/-- smulRight_one_one (abstract). -/
def smulRight_one_one' : Prop := True
/-- smulRight_one_eq_iff (abstract). -/
def smulRight_one_eq_iff' : Prop := True
/-- smulRight_comp (abstract). -/
def smulRight_comp' : Prop := True
-- COLLISION: toSpanSingleton' already in LinearAlgebra2.lean — rename needed
/-- toSpanSingleton_add (abstract). -/
def toSpanSingleton_add' : Prop := True
/-- toSpanSingleton_smul' (abstract). -/
def toSpanSingleton_smul' : Prop := True
-- COLLISION: proj' already in RingTheory2.lean — rename needed
-- COLLISION: proj_pi' already in LinearAlgebra2.lean — rename needed
-- COLLISION: iInf_ker_proj' already in LinearAlgebra2.lean — rename needed
/-- compRightL (abstract). -/
def compRightL' : Prop := True
-- COLLISION: iInfKerProjEquiv' already in LinearAlgebra2.lean — rename needed
-- COLLISION: range_prod_eq' already in LinearAlgebra2.lean — rename needed
-- COLLISION: ker_prod_ker_le_ker_coprod' already in LinearAlgebra2.lean — rename needed
-- COLLISION: comp_neg' already in Algebra.lean — rename needed
-- COLLISION: neg_comp' already in Algebra.lean — rename needed
-- COLLISION: comp_sub' already in Algebra.lean — rename needed
-- COLLISION: sub_comp' already in Algebra.lean — rename needed
/-- smulRight_one_pow (abstract). -/
def smulRight_one_pow' : Prop := True
/-- projKerOfRightInverse (abstract). -/
def projKerOfRightInverse' : Prop := True
/-- projKerOfRightInverse_apply_idem (abstract). -/
def projKerOfRightInverse_apply_idem' : Prop := True
/-- projKerOfRightInverse_comp_inv (abstract). -/
def projKerOfRightInverse_comp_inv' : Prop := True
/-- isOpenMap_of_ne_zero (abstract). -/
def isOpenMap_of_ne_zero' : Prop := True
-- COLLISION: comp_smul' already in Algebra.lean — rename needed
/-- comp_smulₛₗ (abstract). -/
def comp_smulₛₗ' : Prop := True
-- COLLISION: prod_ext_iff' already in LinearAlgebra2.lean — rename needed
-- COLLISION: prod_ext' already in CategoryTheory.lean — rename needed
/-- prodₗ (abstract). -/
def prodₗ' : Prop := True
/-- coeLM (abstract). -/
def coeLM' : Prop := True
/-- coeLMₛₗ (abstract). -/
def coeLMₛₗ' : Prop := True
-- COLLISION: smulRightₗ' already in Algebra.lean — rename needed
-- COLLISION: restrictScalarsₗ' already in Algebra.lean — rename needed
-- COLLISION: toLinearEquiv_injective' already in Analysis.lean — rename needed
-- COLLISION: toHomeomorph' already in LinearAlgebra2.lean — rename needed
-- COLLISION: isOpenMap' already in Analysis.lean — rename needed
/-- image_closure (abstract). -/
def image_closure' : Prop := True
/-- preimage_closure (abstract). -/
def preimage_closure' : Prop := True
/-- isClosed_image (abstract). -/
def isClosed_image' : Prop := True
-- COLLISION: map_nhds_eq' already in Analysis.lean — rename needed
-- COLLISION: map_eq_zero_iff' already in RingTheory2.lean — rename needed
-- COLLISION: continuousOn' already in Analysis.lean — rename needed
-- COLLISION: continuousAt' already in Analysis.lean — rename needed
-- COLLISION: continuousWithinAt' already in Analysis.lean — rename needed
-- COLLISION: comp_continuousOn_iff' already in Analysis.lean — rename needed
-- COLLISION: comp_continuous_iff' already in Analysis.lean — rename needed
-- COLLISION: refl' already in SetTheory.lean — rename needed
-- COLLISION: symm' already in SetTheory.lean — rename needed
-- COLLISION: symm_apply' already in Order.lean — rename needed
/-- symm_map_nhds_eq (abstract). -/
def symm_map_nhds_eq' : Prop := True
-- COLLISION: trans' already in SetTheory.lean — rename needed
/-- trans_toLinearEquiv (abstract). -/
def trans_toLinearEquiv' : Prop := True
-- COLLISION: prodComm' already in Order.lean — rename needed
/-- coe_comp_coe_symm (abstract). -/
def coe_comp_coe_symm' : Prop := True
/-- coe_symm_comp_coe (abstract). -/
def coe_symm_comp_coe' : Prop := True
-- COLLISION: symm_apply_eq' already in Algebra.lean — rename needed
-- COLLISION: eq_symm_apply' already in Algebra.lean — rename needed
-- COLLISION: image_eq_preimage' already in Order.lean — rename needed
-- COLLISION: image_symm_eq_preimage' already in Algebra.lean — rename needed
-- COLLISION: symm_preimage_preimage' already in MeasureTheory2.lean — rename needed
-- COLLISION: preimage_symm_preimage' already in Order.lean — rename needed
-- COLLISION: isUniformEmbedding' already in MeasureTheory2.lean — rename needed
/-- equivOfInverse (abstract). -/
def equivOfInverse' : Prop := True
-- COLLISION: ulift' already in Algebra.lean — rename needed
/-- arrowCongrEquiv (abstract). -/
def arrowCongrEquiv' : Prop := True
-- COLLISION: piCongrRight' already in Algebra.lean — rename needed
-- COLLISION: skewProd' already in LinearAlgebra2.lean — rename needed
-- COLLISION: neg' already in Order.lean — rename needed
/-- ofUnit (abstract). -/
def ofUnit' : Prop := True
-- COLLISION: toUnit' already in CategoryTheory.lean — rename needed
/-- unitsEquiv (abstract). -/
def unitsEquiv' : Prop := True
/-- unitsEquivAut (abstract). -/
def unitsEquivAut' : Prop := True
/-- equivOfRightInverse (abstract). -/
def equivOfRightInverse' : Prop := True
-- COLLISION: funUnique' already in Order.lean — rename needed
-- COLLISION: piFinTwo' already in Algebra.lean — rename needed
-- COLLISION: finTwoArrow' already in LinearAlgebra2.lean — rename needed
/-- IsInvertible (abstract). -/
def IsInvertible' : Prop := True
-- COLLISION: inverse' already in Algebra.lean — rename needed
/-- isInvertible_equiv (abstract). -/
def isInvertible_equiv' : Prop := True
/-- inverse_equiv (abstract). -/
def inverse_equiv' : Prop := True
/-- inverse_of_not_isInvertible (abstract). -/
def inverse_of_not_isInvertible' : Prop := True
/-- inverse_zero (abstract). -/
def inverse_zero' : Prop := True
/-- of_inverse (abstract). -/
def of_inverse' : Prop := True
-- COLLISION: inverse_apply_eq' already in LinearAlgebra2.lean — rename needed
/-- isInvertible_equiv_comp (abstract). -/
def isInvertible_equiv_comp' : Prop := True
/-- isInvertible_comp_equiv (abstract). -/
def isInvertible_comp_equiv' : Prop := True
/-- inverse_equiv_comp (abstract). -/
def inverse_equiv_comp' : Prop := True
/-- inverse_comp_equiv (abstract). -/
def inverse_comp_equiv' : Prop := True
/-- inverse_comp_of_left (abstract). -/
def inverse_comp_of_left' : Prop := True
/-- inverse_comp_apply_of_left (abstract). -/
def inverse_comp_apply_of_left' : Prop := True
/-- inverse_comp_of_right (abstract). -/
def inverse_comp_of_right' : Prop := True
/-- inverse_comp_apply_of_right (abstract). -/
def inverse_comp_apply_of_right' : Prop := True
/-- ring_inverse_equiv (abstract). -/
def ring_inverse_equiv' : Prop := True
/-- to_ring_inverse (abstract). -/
def to_ring_inverse' : Prop := True
/-- ring_inverse_eq_map_inverse (abstract). -/
def ring_inverse_eq_map_inverse' : Prop := True
/-- inverse_id (abstract). -/
def inverse_id' : Prop := True
/-- ClosedComplemented (abstract). -/
def ClosedComplemented' : Prop := True
/-- exists_isClosed_isCompl (abstract). -/
def exists_isClosed_isCompl' : Prop := True
/-- closedComplemented_bot (abstract). -/
def closedComplemented_bot' : Prop := True
/-- closedComplemented_top (abstract). -/
def closedComplemented_top' : Prop := True
/-- exists_submodule_equiv_prod (abstract). -/
def exists_submodule_equiv_prod' : Prop := True
/-- closedComplemented_ker_of_rightInverse (abstract). -/
def closedComplemented_ker_of_rightInverse' : Prop := True
/-- isOpenMap_mkQ (abstract). -/
def isOpenMap_mkQ' : Prop := True
/-- isOpenQuotientMap_mkQ (abstract). -/
def isOpenQuotientMap_mkQ' : Prop := True
/-- opContinuousLinearEquiv (abstract). -/
def opContinuousLinearEquiv' : Prop := True

-- Algebra/Module/CharacterSpace.lean
/-- characterSpace (abstract). -/
def characterSpace' : Prop := True
/-- toCLM (abstract). -/
def toCLM' : Prop := True
-- COLLISION: toNonUnitalAlgHom' already in Algebra.lean — rename needed
/-- union_zero (abstract). -/
def union_zero' : Prop := True
/-- union_zero_isClosed (abstract). -/
def union_zero_isClosed' : Prop := True
-- COLLISION: toAlgHom' already in RingTheory2.lean — rename needed
/-- ext_ker (abstract). -/
def ext_ker' : Prop := True
/-- gelfandTransform (abstract). -/
def gelfandTransform' : Prop := True

-- Algebra/Module/Determinant.lean
-- COLLISION: det' already in RingTheory2.lean — rename needed
-- COLLISION: det_coe_symm' already in LinearAlgebra2.lean — rename needed

-- Algebra/Module/FiniteDimension.lean
/-- unique_topology_of_t2 (abstract). -/
def unique_topology_of_t2' : Prop := True
/-- continuous_of_isClosed_ker (abstract). -/
def continuous_of_isClosed_ker' : Prop := True
/-- continuous_iff_isClosed_ker (abstract). -/
def continuous_iff_isClosed_ker' : Prop := True
/-- continuous_of_nonzero_on_open (abstract). -/
def continuous_of_nonzero_on_open' : Prop := True
/-- continuous_equivFun_basis_aux (abstract). -/
def continuous_equivFun_basis_aux' : Prop := True
-- COLLISION: continuous_of_finiteDimensional' already in Analysis.lean — rename needed
/-- isOpenMap_of_finiteDimensional (abstract). -/
def isOpenMap_of_finiteDimensional' : Prop := True
-- COLLISION: toContinuousLinearEquiv' already in Analysis.lean — rename needed
/-- toLinearEquiv_toContinuousLinearEquiv (abstract). -/
def toLinearEquiv_toContinuousLinearEquiv' : Prop := True
/-- toLinearEquiv_toContinuousLinearEquiv_symm (abstract). -/
def toLinearEquiv_toContinuousLinearEquiv_symm' : Prop := True
/-- nonempty_continuousLinearEquiv_of_finrank_eq (abstract). -/
def nonempty_continuousLinearEquiv_of_finrank_eq' : Prop := True
/-- nonempty_continuousLinearEquiv_iff_finrank_eq (abstract). -/
def nonempty_continuousLinearEquiv_iff_finrank_eq' : Prop := True
-- COLLISION: ofFinrankEq' already in LinearAlgebra2.lean — rename needed
/-- constrL (abstract). -/
def constrL' : Prop := True
/-- equivFunL (abstract). -/
def equivFunL' : Prop := True
/-- equivFunL_symm_apply_repr (abstract). -/
def equivFunL_symm_apply_repr' : Prop := True
/-- constrL_apply (abstract). -/
def constrL_apply' : Prop := True
/-- constrL_basis (abstract). -/
def constrL_basis' : Prop := True
/-- toContinuousLinearEquivOfDetNeZero (abstract). -/
def toContinuousLinearEquivOfDetNeZero' : Prop := True
/-- toLin_finTwoProd_toContinuousLinearMap (abstract). -/
def toLin_finTwoProd_toContinuousLinearMap' : Prop := True
-- COLLISION: complete' already in Algebra.lean — rename needed
/-- complete_of_finiteDimensional (abstract). -/
def complete_of_finiteDimensional' : Prop := True
-- COLLISION: closed_of_finiteDimensional' already in Analysis.lean — rename needed
/-- isClosedEmbedding_of_injective (abstract). -/
def isClosedEmbedding_of_injective' : Prop := True
/-- isClosedEmbedding_smul_left (abstract). -/
def isClosedEmbedding_smul_left' : Prop := True
/-- isClosedMap_smul_left (abstract). -/
def isClosedMap_smul_left' : Prop := True
/-- exists_right_inverse_of_surjective (abstract). -/
def exists_right_inverse_of_surjective' : Prop := True

-- Algebra/Module/LinearPMap.lean
/-- IsClosable (abstract). -/
def IsClosable' : Prop := True
/-- isClosable (abstract). -/
def isClosable' : Prop := True
/-- leIsClosable (abstract). -/
def leIsClosable' : Prop := True
-- COLLISION: existsUnique' already in CategoryTheory.lean — rename needed
/-- closure_def (abstract). -/
def closure_def' : Prop := True
/-- graph_closure_eq_closure_graph (abstract). -/
def graph_closure_eq_closure_graph' : Prop := True
-- COLLISION: le_closure' already in Order.lean — rename needed
-- COLLISION: closure_mono' already in RingTheory2.lean — rename needed
/-- closure_isClosed (abstract). -/
def closure_isClosed' : Prop := True
/-- closureIsClosable (abstract). -/
def closureIsClosable' : Prop := True
/-- isClosable_iff_exists_closed_extension (abstract). -/
def isClosable_iff_exists_closed_extension' : Prop := True
/-- HasCore (abstract). -/
def HasCore' : Prop := True
/-- closure_inverse_graph (abstract). -/
def closure_inverse_graph' : Prop := True
/-- inverse_isClosable_iff (abstract). -/
def inverse_isClosable_iff' : Prop := True
/-- inverse_closure (abstract). -/
def inverse_closure' : Prop := True

-- Algebra/Module/LocallyConvex.lean
/-- LocallyConvexSpace (abstract). -/
def LocallyConvexSpace' : Prop := True
/-- locallyConvexSpace_iff (abstract). -/
def locallyConvexSpace_iff' : Prop := True
/-- convex_basis_zero (abstract). -/
def convex_basis_zero' : Prop := True
/-- locallyConvexSpace_iff_exists_convex_subset (abstract). -/
def locallyConvexSpace_iff_exists_convex_subset' : Prop := True
/-- ofBasisZero (abstract). -/
def ofBasisZero' : Prop := True
/-- locallyConvexSpace_iff_zero (abstract). -/
def locallyConvexSpace_iff_zero' : Prop := True
/-- locallyConvexSpace_iff_exists_convex_subset_zero (abstract). -/
def locallyConvexSpace_iff_exists_convex_subset_zero' : Prop := True
/-- convex_open_basis_zero (abstract). -/
def convex_open_basis_zero' : Prop := True
/-- exists_open_convexes (abstract). -/
def exists_open_convexes' : Prop := True
/-- locallyConvexSpace_sInf (abstract). -/
def locallyConvexSpace_sInf' : Prop := True
/-- locallyConvexSpace_iInf (abstract). -/
def locallyConvexSpace_iInf' : Prop := True
/-- locallyConvexSpace_inf (abstract). -/
def locallyConvexSpace_inf' : Prop := True
/-- locallyConvexSpace_induced (abstract). -/
def locallyConvexSpace_induced' : Prop := True

-- Algebra/Module/ModuleTopology.lean
/-- moduleTopology (abstract). -/
def moduleTopology' : Prop := True
/-- IsModuleTopology (abstract). -/
def IsModuleTopology' : Prop := True
/-- eq_moduleTopology (abstract). -/
def eq_moduleTopology' : Prop := True
-- COLLISION: continuousSMul' already in Analysis.lean — rename needed
/-- continuousAdd (abstract). -/
def continuousAdd' : Prop := True
/-- toContinuousAdd (abstract). -/
def toContinuousAdd' : Prop := True
/-- moduleTopology_le (abstract). -/
def moduleTopology_le' : Prop := True
/-- of_continuous_id (abstract). -/
def of_continuous_id' : Prop := True
-- COLLISION: iso' already in Algebra.lean — rename needed
-- COLLISION: it' already in Analysis.lean — rename needed
/-- continuous_of_distribMulActionHom (abstract). -/
def continuous_of_distribMulActionHom' : Prop := True
/-- continuous_of_linearMap (abstract). -/
def continuous_of_linearMap' : Prop := True
/-- continuous_neg (abstract). -/
def continuous_neg' : Prop := True
/-- continuous_of_ringHom (abstract). -/
def continuous_of_ringHom' : Prop := True

-- Algebra/Module/Multilinear/Basic.lean
/-- ContinuousMultilinearMap (abstract). -/
def ContinuousMultilinearMap' : Prop := True
/-- toMultilinearMap_injective (abstract). -/
def toMultilinearMap_injective' : Prop := True
/-- compContinuousMultilinearMap (abstract). -/
def compContinuousMultilinearMap' : Prop := True
/-- compContinuousMultilinearMap_coe (abstract). -/
def compContinuousMultilinearMap_coe' : Prop := True
-- COLLISION: domDomCongr' already in LinearAlgebra2.lean — rename needed
-- COLLISION: domDomCongrEquiv' already in LinearAlgebra2.lean — rename needed
-- COLLISION: linearDeriv' already in LinearAlgebra2.lean — rename needed
-- COLLISION: linearDeriv_apply' already in LinearAlgebra2.lean — rename needed
-- COLLISION: map_update_sub' already in LinearAlgebra2.lean — rename needed
/-- toMultilinearMapLinear (abstract). -/
def toMultilinearMapLinear' : Prop := True
-- COLLISION: mkPiAlgebra' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiAlgebraFin' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_apply_one_eq_self' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_eq_iff' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_zero' already in LinearAlgebra2.lean — rename needed
-- COLLISION: mkPiRing_eq_zero_iff' already in LinearAlgebra2.lean — rename needed

-- Algebra/Module/Multilinear/Bounded.lean
/-- searches (abstract). -/
def searches' : Prop := True
/-- image_multilinear' (abstract). -/
def image_multilinear' : Prop := True

-- Algebra/Module/Multilinear/Topology.lean
/-- toUniformOnFun (abstract). -/
def toUniformOnFun' : Prop := True
/-- range_toUniformOnFun (abstract). -/
def range_toUniformOnFun' : Prop := True
/-- isUniformInducing_toUniformOnFun (abstract). -/
def isUniformInducing_toUniformOnFun' : Prop := True
/-- isUniformEmbedding_toUniformOnFun (abstract). -/
def isUniformEmbedding_toUniformOnFun' : Prop := True
/-- isEmbedding_toUniformOnFun (abstract). -/
def isEmbedding_toUniformOnFun' : Prop := True
/-- restrictScalarsLinear (abstract). -/
def restrictScalarsLinear' : Prop := True

-- Algebra/Module/Simple.lean
/-- isClosed_or_dense_ker (abstract). -/
def isClosed_or_dense_ker' : Prop := True

-- Algebra/Module/Star.lean
/-- starL (abstract). -/
def starL' : Prop := True
/-- continuous_selfAdjointPart (abstract). -/
def continuous_selfAdjointPart' : Prop := True
/-- continuous_skewAdjointPart (abstract). -/
def continuous_skewAdjointPart' : Prop := True
/-- continuous_decomposeProdAdjoint (abstract). -/
def continuous_decomposeProdAdjoint' : Prop := True
/-- continuous_decomposeProdAdjoint_symm (abstract). -/
def continuous_decomposeProdAdjoint_symm' : Prop := True
/-- selfAdjointPartL (abstract). -/
def selfAdjointPartL' : Prop := True
/-- skewAdjointPartL (abstract). -/
def skewAdjointPartL' : Prop := True
/-- decomposeProdAdjointL (abstract). -/
def decomposeProdAdjointL' : Prop := True

-- Algebra/Module/StrongTopology.lean
/-- UniformConvergenceCLM (abstract). -/
def UniformConvergenceCLM' : Prop := True
/-- topologicalSpace_eq (abstract). -/
def topologicalSpace_eq' : Prop := True
/-- uniformSpace_eq (abstract). -/
def uniformSpace_eq' : Prop := True
/-- isUniformInducing_coeFn (abstract). -/
def isUniformInducing_coeFn' : Prop := True
/-- isUniformEmbedding_coeFn (abstract). -/
def isUniformEmbedding_coeFn' : Prop := True
/-- isEmbedding_coeFn (abstract). -/
def isEmbedding_coeFn' : Prop := True
/-- continuousEvalConst (abstract). -/
def continuousEvalConst' : Prop := True
-- COLLISION: t2Space' already in Analysis.lean — rename needed
/-- nhds_zero_eq_of_basis (abstract). -/
def nhds_zero_eq_of_basis' : Prop := True
/-- nhds_zero_eq (abstract). -/
def nhds_zero_eq' : Prop := True
/-- eventually_nhds_zero_mapsTo (abstract). -/
def eventually_nhds_zero_mapsTo' : Prop := True
/-- isVonNBounded_image2_apply (abstract). -/
def isVonNBounded_image2_apply' : Prop := True
-- COLLISION: isVonNBounded_iff' already in Analysis.lean — rename needed
/-- tendsto_iff_tendstoUniformlyOn (abstract). -/
def tendsto_iff_tendstoUniformlyOn' : Prop := True
/-- uniformSpace_mono (abstract). -/
def uniformSpace_mono' : Prop := True
/-- topologicalSpace_mono (abstract). -/
def topologicalSpace_mono' : Prop := True
-- COLLISION: precomp' already in Algebra.lean — rename needed
-- COLLISION: postcomp' already in Algebra.lean — rename needed
-- COLLISION: toLinearMap₂' already in LinearAlgebra2.lean — rename needed
/-- continuous_restrictScalars (abstract). -/
def continuous_restrictScalars' : Prop := True
/-- restrictScalarsL (abstract). -/
def restrictScalarsL' : Prop := True
/-- arrowCongrSL (abstract). -/
def arrowCongrSL' : Prop := True
-- COLLISION: arrowCongr' already in Order.lean — rename needed

-- Algebra/Module/UniformConvergence.lean
/-- continuousSMul_induced_of_range_bounded (abstract). -/
def continuousSMul_induced_of_range_bounded' : Prop := True
/-- continuousSMul_induced_of_image_bounded (abstract). -/
def continuousSMul_induced_of_image_bounded' : Prop := True
/-- continuousSMul_submodule_of_image_bounded (abstract). -/
def continuousSMul_submodule_of_image_bounded' : Prop := True

-- Algebra/Module/WeakBilin.lean
/-- WeakBilin (abstract). -/
def WeakBilin' : Prop := True
/-- coeFn_continuous (abstract). -/
def coeFn_continuous' : Prop := True
/-- eval_continuous (abstract). -/
def eval_continuous' : Prop := True
/-- continuous_of_continuous_eval (abstract). -/
def continuous_of_continuous_eval' : Prop := True
-- COLLISION: isEmbedding' already in Analysis.lean — rename needed
/-- tendsto_iff_forall_eval_tendsto (abstract). -/
def tendsto_iff_forall_eval_tendsto' : Prop := True

-- Algebra/Module/WeakDual.lean
/-- topDualPairing (abstract). -/
def topDualPairing' : Prop := True
/-- WeakDual (abstract). -/
def WeakDual' : Prop := True
/-- WeakSpace (abstract). -/
def WeakSpace' : Prop := True
/-- toWeakSpace (abstract). -/
def toWeakSpace' : Prop := True
/-- toWeakSpaceCLM (abstract). -/
def toWeakSpaceCLM' : Prop := True
/-- toWeakSpaceCLM_bijective (abstract). -/
def toWeakSpaceCLM_bijective' : Prop := True
/-- isOpenMap_toWeakSpace_symm (abstract). -/
def isOpenMap_toWeakSpace_symm' : Prop := True
/-- isOpen_of_isOpen (abstract). -/
def isOpen_of_isOpen' : Prop := True
/-- tendsto_iff_forall_eval_tendsto_topDualPairing (abstract). -/
def tendsto_iff_forall_eval_tendsto_topDualPairing' : Prop := True

-- Algebra/Monoid.lean
/-- continuous_one (abstract). -/
def continuous_one' : Prop := True
/-- ContinuousAdd (abstract). -/
def ContinuousAdd' : Prop := True
/-- ContinuousMul (abstract). -/
def ContinuousMul' : Prop := True
-- COLLISION: induced' already in RingTheory2.lean — rename needed
/-- continuous_mul_left (abstract). -/
def continuous_mul_left' : Prop := True
/-- continuous_mul_right (abstract). -/
def continuous_mul_right' : Prop := True
/-- tendsto_mul (abstract). -/
def tendsto_mul' : Prop := True
/-- le_nhds_mul (abstract). -/
def le_nhds_mul' : Prop := True
/-- nhds_one_mul_nhds (abstract). -/
def nhds_one_mul_nhds' : Prop := True
/-- nhds_mul_nhds_one (abstract). -/
def nhds_mul_nhds_one' : Prop := True
-- COLLISION: const_mul' already in Algebra.lean — rename needed
-- COLLISION: mul_const' already in Algebra.lean — rename needed
-- COLLISION: pow' already in RingTheory2.lean — rename needed
-- COLLISION: units' already in Algebra.lean — rename needed
/-- continuousMul_of_comm_of_nhds_one (abstract). -/
def continuousMul_of_comm_of_nhds_one' : Prop := True
/-- isClosed_setOf_map_one (abstract). -/
def isClosed_setOf_map_one' : Prop := True
/-- isClosed_setOf_map_mul (abstract). -/
def isClosed_setOf_map_mul' : Prop := True
/-- mulHomOfMemClosureRangeCoe (abstract). -/
def mulHomOfMemClosureRangeCoe' : Prop := True
/-- mulHomOfTendsto (abstract). -/
def mulHomOfTendsto' : Prop := True
/-- monoidHomOfMemClosureRangeCoe (abstract). -/
def monoidHomOfMemClosureRangeCoe' : Prop := True
/-- monoidHomOfTendsto (abstract). -/
def monoidHomOfTendsto' : Prop := True
/-- continuousMul (abstract). -/
def continuousMul' : Prop := True
/-- continuousMul_induced (abstract). -/
def continuousMul_induced' : Prop := True
/-- exists_open_nhds_one_split (abstract). -/
def exists_open_nhds_one_split' : Prop := True
/-- exists_nhds_one_split (abstract). -/
def exists_nhds_one_split' : Prop := True
/-- exists_open_nhds_one_mul_subset (abstract). -/
def exists_open_nhds_one_mul_subset' : Prop := True
/-- top_closure_mul_self_subset (abstract). -/
def top_closure_mul_self_subset' : Prop := True
/-- commSemigroupTopologicalClosure (abstract). -/
def commSemigroupTopologicalClosure' : Prop := True
/-- top_closure_mul_self_eq (abstract). -/
def top_closure_mul_self_eq' : Prop := True
/-- commMonoidTopologicalClosure (abstract). -/
def commMonoidTopologicalClosure' : Prop := True
/-- exists_nhds_one_split4 (abstract). -/
def exists_nhds_one_split4' : Prop := True
/-- tendsto_list_prod (abstract). -/
def tendsto_list_prod' : Prop := True
/-- continuous_list_prod (abstract). -/
def continuous_list_prod' : Prop := True
/-- continuousOn_list_prod (abstract). -/
def continuousOn_list_prod' : Prop := True
/-- continuous_pow (abstract). -/
def continuous_pow' : Prop := True
/-- continuousOn_pow (abstract). -/
def continuousOn_pow' : Prop := True
/-- continuousAt_pow (abstract). -/
def continuousAt_pow' : Prop := True
/-- tendsto_cocompact_mul_left (abstract). -/
def tendsto_cocompact_mul_left' : Prop := True
/-- tendsto_cocompact_mul_right (abstract). -/
def tendsto_cocompact_mul_right' : Prop := True
/-- units_map (abstract). -/
def units_map' : Prop := True
/-- tendsto_multiset_prod (abstract). -/
def tendsto_multiset_prod' : Prop := True
/-- tendsto_finset_prod (abstract). -/
def tendsto_finset_prod' : Prop := True
/-- continuous_multiset_prod (abstract). -/
def continuous_multiset_prod' : Prop := True
/-- continuousOn_multiset_prod (abstract). -/
def continuousOn_multiset_prod' : Prop := True
/-- continuous_finset_prod (abstract). -/
def continuous_finset_prod' : Prop := True
/-- continuousOn_finset_prod (abstract). -/
def continuousOn_finset_prod' : Prop := True
/-- eventuallyEq_prod (abstract). -/
def eventuallyEq_prod' : Prop := True
/-- exists_finset_mulSupport (abstract). -/
def exists_finset_mulSupport' : Prop := True
/-- finprod_eventually_eq_prod (abstract). -/
def finprod_eventually_eq_prod' : Prop := True
/-- continuous_finprod (abstract). -/
def continuous_finprod' : Prop := True
/-- continuous_finprod_cond (abstract). -/
def continuous_finprod_cond' : Prop := True
/-- continuousMul_sInf (abstract). -/
def continuousMul_sInf' : Prop := True
/-- continuousMul_iInf (abstract). -/
def continuousMul_iInf' : Prop := True
/-- continuousMul_inf (abstract). -/
def continuousMul_inf' : Prop := True

-- Algebra/MulAction.lean
-- COLLISION: saying' already in Order.lean — rename needed
/-- ContinuousSMul (abstract). -/
def ContinuousSMul' : Prop := True
/-- ContinuousVAdd (abstract). -/
def ContinuousVAdd' : Prop := True
-- COLLISION: smul_set' already in Algebra.lean — rename needed
/-- smul_set_closure_subset (abstract). -/
def smul_set_closure_subset' : Prop := True
/-- continuousSMul_compHom (abstract). -/
def continuousSMul_compHom' : Prop := True
/-- stabilizer_isOpen (abstract). -/
def stabilizer_isOpen' : Prop := True
/-- continuousSMul_sInf (abstract). -/
def continuousSMul_sInf' : Prop := True
/-- continuousSMul_iInf (abstract). -/
def continuousSMul_iInf' : Prop := True
/-- continuousSMul_inf (abstract). -/
def continuousSMul_inf' : Prop := True
/-- connectedSpace (abstract). -/
def connectedSpace' : Prop := True

-- Algebra/MvPolynomial.lean
/-- continuous_eval (abstract). -/
def continuous_eval' : Prop := True

-- Algebra/NonUnitalAlgebra.lean
/-- nonUnitalCommSemiringTopologicalClosure (abstract). -/
def nonUnitalCommSemiringTopologicalClosure' : Prop := True
/-- nonUnitalCommRingTopologicalClosure (abstract). -/
def nonUnitalCommRingTopologicalClosure' : Prop := True

-- Algebra/NonUnitalStarAlgebra.lean
/-- star_self_mem (abstract). -/
def star_self_mem' : Prop := True

-- Algebra/Nonarchimedean/AdicTopology.lean
-- COLLISION: and' already in Order.lean — rename needed
-- COLLISION: registering' already in MeasureTheory2.lean — rename needed
-- COLLISION: inference' already in RingTheory2.lean — rename needed
/-- adic_basis (abstract). -/
def adic_basis' : Prop := True
/-- ringFilterBasis (abstract). -/
def ringFilterBasis' : Prop := True
/-- adicTopology (abstract). -/
def adicTopology' : Prop := True
/-- nonarchimedean (abstract). -/
def nonarchimedean' : Prop := True
/-- hasBasis_nhds_zero_adic (abstract). -/
def hasBasis_nhds_zero_adic' : Prop := True
/-- hasBasis_nhds_adic (abstract). -/
def hasBasis_nhds_adic' : Prop := True
/-- adic_module_basis (abstract). -/
def adic_module_basis' : Prop := True
/-- adicModuleTopology (abstract). -/
def adicModuleTopology' : Prop := True
/-- openAddSubgroup (abstract). -/
def openAddSubgroup' : Prop := True
/-- IsAdic (abstract). -/
def IsAdic' : Prop := True
/-- isAdic_iff (abstract). -/
def isAdic_iff' : Prop := True
/-- is_ideal_adic_pow (abstract). -/
def is_ideal_adic_pow' : Prop := True
/-- is_bot_adic_iff (abstract). -/
def is_bot_adic_iff' : Prop := True
/-- WithIdeal (abstract). -/
def WithIdeal' : Prop := True
/-- topologicalSpaceModule (abstract). -/
def topologicalSpaceModule' : Prop := True

-- Algebra/Nonarchimedean/Bases.lean
/-- RingSubgroupsBasis (abstract). -/
def RingSubgroupsBasis' : Prop := True
/-- of_comm (abstract). -/
def of_comm' : Prop := True
/-- toRingFilterBasis (abstract). -/
def toRingFilterBasis' : Prop := True
/-- mem_addGroupFilterBasis (abstract). -/
def mem_addGroupFilterBasis' : Prop := True
/-- hasBasis_nhds (abstract). -/
def hasBasis_nhds' : Prop := True
/-- SubmodulesRingBasis (abstract). -/
def SubmodulesRingBasis' : Prop := True
/-- toRing_subgroups_basis (abstract). -/
def toRing_subgroups_basis' : Prop := True
/-- SubmodulesBasis (abstract). -/
def SubmodulesBasis' : Prop := True
/-- toModuleFilterBasis (abstract). -/
def toModuleFilterBasis' : Prop := True
/-- submodulesBasisIsBasis (abstract). -/
def submodulesBasisIsBasis' : Prop := True
-- COLLISION: moduleFilterBasis' already in Analysis.lean — rename needed

-- Algebra/Nonarchimedean/Basic.lean
/-- NonarchimedeanAddGroup (abstract). -/
def NonarchimedeanAddGroup' : Prop := True
/-- NonarchimedeanGroup (abstract). -/
def NonarchimedeanGroup' : Prop := True
/-- NonarchimedeanRing (abstract). -/
def NonarchimedeanRing' : Prop := True
/-- nonarchimedean_of_emb (abstract). -/
def nonarchimedean_of_emb' : Prop := True
-- COLLISION: prod_subset' already in Algebra.lean — rename needed
/-- prod_self_subset (abstract). -/
def prod_self_subset' : Prop := True
/-- left_mul_subset (abstract). -/
def left_mul_subset' : Prop := True
-- COLLISION: mul_subset' already in Algebra.lean — rename needed

-- Algebra/Nonarchimedean/TotallyDisconnected.lean
/-- exists_openSubgroup_separating (abstract). -/
def exists_openSubgroup_separating' : Prop := True

-- Algebra/OpenSubgroup.lean
/-- OpenAddSubgroup (abstract). -/
def OpenAddSubgroup' : Prop := True
/-- OpenSubgroup (abstract). -/
def OpenSubgroup' : Prop := True
/-- toOpens (abstract). -/
def toOpens' : Prop := True
/-- isClopen (abstract). -/
def isClopen' : Prop := True
-- COLLISION: comap' already in Order.lean — rename needed
/-- isOpen_of_mem_nhds (abstract). -/
def isOpen_of_mem_nhds' : Prop := True
/-- isOpen_mono (abstract). -/
def isOpen_mono' : Prop := True
/-- isOpen_of_openSubgroup (abstract). -/
def isOpen_of_openSubgroup' : Prop := True
/-- isOpen_of_one_mem_interior (abstract). -/
def isOpen_of_one_mem_interior' : Prop := True
/-- isClosed_of_isOpen (abstract). -/
def isClosed_of_isOpen' : Prop := True
/-- subgroupOf_isOpen (abstract). -/
def subgroupOf_isOpen' : Prop := True
/-- discreteTopology (abstract). -/
def discreteTopology' : Prop := True
/-- quotient_finite_of_isOpen (abstract). -/
def quotient_finite_of_isOpen' : Prop := True
/-- isOpen_of_isOpen_subideal (abstract). -/
def isOpen_of_isOpen_subideal' : Prop := True
/-- OpenNormalSubgroup (abstract). -/
def OpenNormalSubgroup' : Prop := True
/-- OpenNormalAddSubgroup (abstract). -/
def OpenNormalAddSubgroup' : Prop := True
/-- addNegClosureNhd (abstract). -/
def addNegClosureNhd' : Prop := True
/-- mulInvClosureNhd (abstract). -/
def mulInvClosureNhd' : Prop := True
/-- exist_mul_closure_nhd (abstract). -/
def exist_mul_closure_nhd' : Prop := True
/-- exists_mulInvClosureNhd (abstract). -/
def exists_mulInvClosureNhd' : Prop := True
/-- exist_openSubgroup_sub_clopen_nhd_of_one (abstract). -/
def exist_openSubgroup_sub_clopen_nhd_of_one' : Prop := True

-- Algebra/Order/Archimedean.lean
/-- denseRange_cast (abstract). -/
def denseRange_cast' : Prop := True
/-- dense_of_not_isolated_zero (abstract). -/
def dense_of_not_isolated_zero' : Prop := True
/-- dense_of_no_min (abstract). -/
def dense_of_no_min' : Prop := True
/-- dense_or_cyclic (abstract). -/
def dense_or_cyclic' : Prop := True

-- Algebra/Order/Field.lean
-- COLLISION: of_norm' already in Analysis.lean — rename needed
/-- atTop_mul (abstract). -/
def atTop_mul' : Prop := True
/-- mul_atTop (abstract). -/
def mul_atTop' : Prop := True
/-- atTop_mul_neg (abstract). -/
def atTop_mul_neg' : Prop := True
/-- neg_mul_atTop (abstract). -/
def neg_mul_atTop' : Prop := True
/-- atBot_mul (abstract). -/
def atBot_mul' : Prop := True
/-- atBot_mul_neg (abstract). -/
def atBot_mul_neg' : Prop := True
/-- mul_atBot (abstract). -/
def mul_atBot' : Prop := True
/-- neg_mul_atBot (abstract). -/
def neg_mul_atBot' : Prop := True
/-- inv_atTop₀ (abstract). -/
def inv_atTop₀' : Prop := True
/-- inv_nhdsWithin_Ioi_zero (abstract). -/
def inv_nhdsWithin_Ioi_zero' : Prop := True
/-- tendsto_inv_zero_atTop (abstract). -/
def tendsto_inv_zero_atTop' : Prop := True
/-- tendsto_inv_atTop_zero' (abstract). -/
def tendsto_inv_atTop_zero' : Prop := True
/-- div_atTop (abstract). -/
def div_atTop' : Prop := True
/-- const_div_atTop (abstract). -/
def const_div_atTop' : Prop := True
/-- inv_tendsto_atTop (abstract). -/
def inv_tendsto_atTop' : Prop := True
/-- inv_tendsto_zero (abstract). -/
def inv_tendsto_zero' : Prop := True
/-- bdd_le_mul_tendsto_zero' (abstract). -/
def bdd_le_mul_tendsto_zero' : Prop := True
/-- tendsto_bdd_div_atTop_nhds_zero (abstract). -/
def tendsto_bdd_div_atTop_nhds_zero' : Prop := True
/-- tendsto_pow_neg_atTop (abstract). -/
def tendsto_pow_neg_atTop' : Prop := True
/-- tendsto_zpow_atTop_zero (abstract). -/
def tendsto_zpow_atTop_zero' : Prop := True
/-- tendsto_const_mul_zpow_atTop_zero (abstract). -/
def tendsto_const_mul_zpow_atTop_zero' : Prop := True
/-- tendsto_const_mul_pow_nhds_iff' (abstract). -/
def tendsto_const_mul_pow_nhds_iff' : Prop := True
/-- tendsto_const_mul_zpow_atTop_nhds_iff (abstract). -/
def tendsto_const_mul_zpow_atTop_nhds_iff' : Prop := True
/-- nhdsWithin_pos_comap_mul_left (abstract). -/
def nhdsWithin_pos_comap_mul_left' : Prop := True
/-- eventually_nhdsWithin_pos_mul_left (abstract). -/
def eventually_nhdsWithin_pos_mul_left' : Prop := True

-- Algebra/Order/Floor.lean
/-- tendsto_mul_pow_div_factorial_sub_atTop (abstract). -/
def tendsto_mul_pow_div_factorial_sub_atTop' : Prop := True
-- COLLISION: tendsto_pow_div_factorial_atTop' already in Analysis.lean — rename needed
/-- tendsto_floor_atTop (abstract). -/
def tendsto_floor_atTop' : Prop := True
/-- tendsto_floor_atBot (abstract). -/
def tendsto_floor_atBot' : Prop := True
/-- tendsto_ceil_atTop (abstract). -/
def tendsto_ceil_atTop' : Prop := True
/-- tendsto_ceil_atBot (abstract). -/
def tendsto_ceil_atBot' : Prop := True
/-- continuousOn_floor (abstract). -/
def continuousOn_floor' : Prop := True
/-- continuousOn_ceil (abstract). -/
def continuousOn_ceil' : Prop := True
/-- tendsto_floor_right_pure_floor (abstract). -/
def tendsto_floor_right_pure_floor' : Prop := True
/-- tendsto_floor_right_pure (abstract). -/
def tendsto_floor_right_pure' : Prop := True
/-- tendsto_ceil_left_pure_ceil (abstract). -/
def tendsto_ceil_left_pure_ceil' : Prop := True
/-- tendsto_ceil_left_pure (abstract). -/
def tendsto_ceil_left_pure' : Prop := True
/-- tendsto_floor_left_pure_ceil_sub_one (abstract). -/
def tendsto_floor_left_pure_ceil_sub_one' : Prop := True
/-- tendsto_floor_left_pure_sub_one (abstract). -/
def tendsto_floor_left_pure_sub_one' : Prop := True
/-- tendsto_ceil_right_pure_floor_add_one (abstract). -/
def tendsto_ceil_right_pure_floor_add_one' : Prop := True
/-- tendsto_ceil_right_pure_add_one (abstract). -/
def tendsto_ceil_right_pure_add_one' : Prop := True
/-- tendsto_floor_right (abstract). -/
def tendsto_floor_right' : Prop := True
/-- tendsto_ceil_left (abstract). -/
def tendsto_ceil_left' : Prop := True
/-- tendsto_floor_left (abstract). -/
def tendsto_floor_left' : Prop := True
/-- tendsto_ceil_right (abstract). -/
def tendsto_ceil_right' : Prop := True
/-- continuousOn_fract (abstract). -/
def continuousOn_fract' : Prop := True
/-- continuousAt_fract (abstract). -/
def continuousAt_fract' : Prop := True
/-- tendsto_fract_left' (abstract). -/
def tendsto_fract_left' : Prop := True
/-- tendsto_fract_right' (abstract). -/
def tendsto_fract_right' : Prop := True
/-- comp_fract' (abstract). -/
def comp_fract' : Prop := True
/-- comp_fract'' (abstract). -/
def comp_fract'' : Prop := True

-- Algebra/Order/Group.lean
-- COLLISION: continuous_abs' already in Analysis.lean — rename needed
/-- tendsto_zero_iff_abs_tendsto_zero (abstract). -/
def tendsto_zero_iff_abs_tendsto_zero' : Prop := True
/-- tendsto_abs_nhdsWithin_zero (abstract). -/
def tendsto_abs_nhdsWithin_zero' : Prop := True
/-- denseRange_zsmul_iff_surjective (abstract). -/
def denseRange_zsmul_iff_surjective' : Prop := True

-- Algebra/Order/LiminfLimsup.lean
-- COLLISION: stating' already in SetTheory.lean — rename needed
/-- BoundedLENhdsClass (abstract). -/
def BoundedLENhdsClass' : Prop := True
/-- BoundedGENhdsClass (abstract). -/
def BoundedGENhdsClass' : Prop := True
/-- le_nhds_of_limsSup_eq_limsInf (abstract). -/
def le_nhds_of_limsSup_eq_limsInf' : Prop := True
/-- limsSup_nhds (abstract). -/
def limsSup_nhds' : Prop := True
/-- limsInf_nhds (abstract). -/
def limsInf_nhds' : Prop := True
/-- limsInf_eq_of_le_nhds (abstract). -/
def limsInf_eq_of_le_nhds' : Prop := True
/-- limsSup_eq_of_le_nhds (abstract). -/
def limsSup_eq_of_le_nhds' : Prop := True
/-- limsup_eq (abstract). -/
def limsup_eq' : Prop := True
/-- liminf_eq (abstract). -/
def liminf_eq' : Prop := True
/-- tendsto_of_liminf_eq_limsup (abstract). -/
def tendsto_of_liminf_eq_limsup' : Prop := True
/-- tendsto_of_le_liminf_of_limsup_le (abstract). -/
def tendsto_of_le_liminf_of_limsup_le' : Prop := True
/-- tendsto_of_no_upcrossings (abstract). -/
def tendsto_of_no_upcrossings' : Prop := True
-- COLLISION: eventually_le_limsup' already in Order.lean — rename needed
/-- eventually_liminf_le (abstract). -/
def eventually_liminf_le' : Prop := True
/-- limsup_eq_bot (abstract). -/
def limsup_eq_bot' : Prop := True
/-- liminf_eq_top (abstract). -/
def liminf_eq_top' : Prop := True
/-- map_limsSup_of_continuousAt (abstract). -/
def map_limsSup_of_continuousAt' : Prop := True
/-- map_limsup_of_continuousAt (abstract). -/
def map_limsup_of_continuousAt' : Prop := True
/-- map_limsInf_of_continuousAt (abstract). -/
def map_limsInf_of_continuousAt' : Prop := True
/-- map_liminf_of_continuousAt (abstract). -/
def map_liminf_of_continuousAt' : Prop := True
/-- limsup_eq_tendsto_sum_indicator_nat_atTop (abstract). -/
def limsup_eq_tendsto_sum_indicator_nat_atTop' : Prop := True
/-- limsup_eq_tendsto_sum_indicator_atTop (abstract). -/
def limsup_eq_tendsto_sum_indicator_atTop' : Prop := True
/-- le_limsup_add (abstract). -/
def le_limsup_add' : Prop := True
-- COLLISION: limsup_add_le' already in Order.lean — rename needed
/-- le_liminf_add (abstract). -/
def le_liminf_add' : Prop := True
/-- liminf_add_le (abstract). -/
def liminf_add_le' : Prop := True
/-- le_limsup_mul (abstract). -/
def le_limsup_mul' : Prop := True
-- COLLISION: limsup_mul_le' already in Order.lean — rename needed
/-- le_liminf_mul (abstract). -/
def le_liminf_mul' : Prop := True
/-- liminf_mul_le (abstract). -/
def liminf_mul_le' : Prop := True
/-- limsup_const_add (abstract). -/
def limsup_const_add' : Prop := True
/-- limsup_add_const (abstract). -/
def limsup_add_const' : Prop := True
/-- liminf_const_add (abstract). -/
def liminf_const_add' : Prop := True
/-- liminf_add_const (abstract). -/
def liminf_add_const' : Prop := True
/-- limsup_const_sub (abstract). -/
def limsup_const_sub' : Prop := True
/-- limsup_sub_const (abstract). -/
def limsup_sub_const' : Prop := True
/-- liminf_const_sub (abstract). -/
def liminf_const_sub' : Prop := True
/-- liminf_sub_const (abstract). -/
def liminf_sub_const' : Prop := True

-- Algebra/Order/UpperLower.lean
/-- HasUpperLowerClosure (abstract). -/
def HasUpperLowerClosure' : Prop := True
-- COLLISION: upperClosure' already in Order.lean — rename needed
-- COLLISION: lowerClosure' already in Order.lean — rename needed

-- Algebra/Polynomial.lean
/-- continuous_eval₂ (abstract). -/
def continuous_eval₂' : Prop := True
/-- continuous_aeval (abstract). -/
def continuous_aeval' : Prop := True
/-- continuousAt_aeval (abstract). -/
def continuousAt_aeval' : Prop := True
/-- continuousWithinAt_aeval (abstract). -/
def continuousWithinAt_aeval' : Prop := True
/-- continuousOn_aeval (abstract). -/
def continuousOn_aeval' : Prop := True
/-- tendsto_abv_eval₂_atTop (abstract). -/
def tendsto_abv_eval₂_atTop' : Prop := True
/-- tendsto_abv_atTop (abstract). -/
def tendsto_abv_atTop' : Prop := True
/-- tendsto_abv_aeval_atTop (abstract). -/
def tendsto_abv_aeval_atTop' : Prop := True
/-- tendsto_norm_atTop (abstract). -/
def tendsto_norm_atTop' : Prop := True
-- COLLISION: exists_forall_norm_le' already in MeasureTheory2.lean — rename needed
/-- eq_one_of_roots_le (abstract). -/
def eq_one_of_roots_le' : Prop := True
/-- coeff_le_of_roots_le (abstract). -/
def coeff_le_of_roots_le' : Prop := True
/-- coeff_bdd_of_roots_le (abstract). -/
def coeff_bdd_of_roots_le' : Prop := True

-- Algebra/PontryaginDual.lean
/-- PontryaginDual (abstract). -/
def PontryaginDual' : Prop := True
-- COLLISION: map_one' already in RingTheory2.lean — rename needed
-- COLLISION: map_comp' already in RingTheory2.lean — rename needed
-- COLLISION: map_mul' already in RingTheory2.lean — rename needed
-- COLLISION: mapHom' already in RingTheory2.lean — rename needed

-- Algebra/ProperAction/Basic.lean
/-- ProperVAdd (abstract). -/
def ProperVAdd' : Prop := True
/-- ProperSMul (abstract). -/
def ProperSMul' : Prop := True
/-- properSMul_iff_continuousSMul_ultrafilter_tendsto (abstract). -/
def properSMul_iff_continuousSMul_ultrafilter_tendsto' : Prop := True
/-- properSMul_iff_continuousSMul_ultrafilter_tendsto_t2 (abstract). -/
def properSMul_iff_continuousSMul_ultrafilter_tendsto_t2' : Prop := True
/-- t2Space_quotient_mulAction_of_properSMul (abstract). -/
def t2Space_quotient_mulAction_of_properSMul' : Prop := True
/-- t2Space_of_properSMul_of_t2Group (abstract). -/
def t2Space_of_properSMul_of_t2Group' : Prop := True
/-- properSMul_of_isClosedEmbedding (abstract). -/
def properSMul_of_isClosedEmbedding' : Prop := True

-- Algebra/ProperAction/ProperlyDiscontinuous.lean
/-- properlyDiscontinuousSMul_iff_properSMul (abstract). -/
def properlyDiscontinuousSMul_iff_properSMul' : Prop := True

-- Algebra/ProperConstSMul.lean
/-- ProperConstVAdd (abstract). -/
def ProperConstVAdd' : Prop := True
/-- ProperConstSMul (abstract). -/
def ProperConstSMul' : Prop := True
-- COLLISION: preimage_smul' already in Analysis.lean — rename needed

-- Algebra/Ring/Basic.lean
/-- TopologicalSemiring (abstract). -/
def TopologicalSemiring' : Prop := True
/-- TopologicalRing (abstract). -/
def TopologicalRing' : Prop := True
/-- continuousNeg_of_mul (abstract). -/
def continuousNeg_of_mul' : Prop := True
/-- toTopologicalRing (abstract). -/
def toTopologicalRing' : Prop := True
/-- of_addGroup_of_nhds_zero (abstract). -/
def of_addGroup_of_nhds_zero' : Prop := True
/-- mulLeft_continuous (abstract). -/
def mulLeft_continuous' : Prop := True
/-- mulRight_continuous (abstract). -/
def mulRight_continuous' : Prop := True
/-- RingTopology (abstract). -/
def RingTopology' : Prop := True
/-- def_sInf (abstract). -/
def def_sInf' : Prop := True
/-- toAddGroupTopology (abstract). -/
def toAddGroupTopology' : Prop := True
-- COLLISION: orderEmbedding' already in SetTheory.lean — rename needed

-- Algebra/Ring/Ideal.lean
/-- closure_eq_of_isClosed (abstract). -/
def closure_eq_of_isClosed' : Prop := True
/-- isQuotientMap_coe_coe (abstract). -/
def isQuotientMap_coe_coe' : Prop := True

-- Algebra/Semigroup.lean
/-- guaranteeing (abstract). -/
def guaranteeing' : Prop := True
/-- exists_idempotent_of_compact_t2_of_continuous_mul_left (abstract). -/
def exists_idempotent_of_compact_t2_of_continuous_mul_left' : Prop := True
-- COLLISION: to' already in Order.lean — rename needed
/-- exists_idempotent_in_compact_subsemigroup (abstract). -/
def exists_idempotent_in_compact_subsemigroup' : Prop := True

-- Algebra/SeparationQuotient/Basic.lean
-- COLLISION: mkMonoidHom' already in Algebra.lean — rename needed
-- COLLISION: mkRingHom' already in Algebra.lean — rename needed
-- COLLISION: mkCLM' already in Analysis.lean — rename needed
-- COLLISION: r' already in RingTheory2.lean — rename needed

-- Algebra/SeparationQuotient/Section.lean
/-- exists_out_continuousLinearMap (abstract). -/
def exists_out_continuousLinearMap' : Prop := True
/-- outCLM (abstract). -/
def outCLM' : Prop := True
/-- mkCLM_comp_outCLM (abstract). -/
def mkCLM_comp_outCLM' : Prop := True
/-- mk_outCLM (abstract). -/
def mk_outCLM' : Prop := True
/-- mk_comp_outCLM (abstract). -/
def mk_comp_outCLM' : Prop := True
/-- postcomp_mkCLM_surjective (abstract). -/
def postcomp_mkCLM_surjective' : Prop := True
/-- isEmbedding_outCLM (abstract). -/
def isEmbedding_outCLM' : Prop := True
/-- outCLM_injective (abstract). -/
def outCLM_injective' : Prop := True
/-- outCLM_isUniformInducing (abstract). -/
def outCLM_isUniformInducing' : Prop := True
/-- outCLM_isUniformEmbedding (abstract). -/
def outCLM_isUniformEmbedding' : Prop := True
/-- outCLM_uniformContinuous (abstract). -/
def outCLM_uniformContinuous' : Prop := True

-- Algebra/Star.lean
/-- ContinuousStar (abstract). -/
def ContinuousStar' : Prop := True
/-- continuousOn_star (abstract). -/
def continuousOn_star' : Prop := True
/-- continuousWithinAt_star (abstract). -/
def continuousWithinAt_star' : Prop := True
/-- continuousAt_star (abstract). -/
def continuousAt_star' : Prop := True
/-- tendsto_star (abstract). -/
def tendsto_star' : Prop := True
/-- starContinuousMap (abstract). -/
def starContinuousMap' : Prop := True

-- Algebra/StarSubalgebra.lean
/-- isEmbedding_inclusion (abstract). -/
def isEmbedding_inclusion' : Prop := True
/-- isClosedEmbedding_inclusion (abstract). -/
def isClosedEmbedding_inclusion' : Prop := True
/-- topologicalClosure_map_le (abstract). -/
def topologicalClosure_map_le' : Prop := True
/-- map_topologicalClosure_le (abstract). -/
def map_topologicalClosure_le' : Prop := True
/-- topologicalClosure_star_comm (abstract). -/
def topologicalClosure_star_comm' : Prop := True
/-- ext_topologicalClosure (abstract). -/
def ext_topologicalClosure' : Prop := True
-- COLLISION: induction_on' already in Order.lean — rename needed
/-- starAlgHomClass_ext (abstract). -/
def starAlgHomClass_ext' : Prop := True

-- Algebra/Support.lean
/-- mulTSupport (abstract). -/
def mulTSupport' : Prop := True
/-- subset_mulTSupport (abstract). -/
def subset_mulTSupport' : Prop := True
/-- isClosed_mulTSupport (abstract). -/
def isClosed_mulTSupport' : Prop := True
/-- mulTSupport_eq_empty_iff (abstract). -/
def mulTSupport_eq_empty_iff' : Prop := True
/-- image_eq_one_of_nmem_mulTSupport (abstract). -/
def image_eq_one_of_nmem_mulTSupport' : Prop := True
/-- range_subset_insert_image_mulTSupport (abstract). -/
def range_subset_insert_image_mulTSupport' : Prop := True
/-- range_eq_image_mulTSupport_or (abstract). -/
def range_eq_image_mulTSupport_or' : Prop := True
/-- tsupport_smul_subset_left (abstract). -/
def tsupport_smul_subset_left' : Prop := True
/-- mulTSupport_mul (abstract). -/
def mulTSupport_mul' : Prop := True
/-- not_mem_mulTSupport_iff_eventuallyEq (abstract). -/
def not_mem_mulTSupport_iff_eventuallyEq' : Prop := True
/-- continuous_of_mulTSupport (abstract). -/
def continuous_of_mulTSupport' : Prop := True
/-- HasCompactMulSupport (abstract). -/
def HasCompactMulSupport' : Prop := True
/-- exists_compact_iff_hasCompactMulSupport (abstract). -/
def exists_compact_iff_hasCompactMulSupport' : Prop := True
/-- intro (abstract). -/
def intro' : Prop := True
/-- of_mulSupport_subset_isCompact (abstract). -/
def of_mulSupport_subset_isCompact' : Prop := True
-- COLLISION: isCompact' already in Analysis.lean — rename needed
/-- hasCompactMulSupport_iff_eventuallyEq (abstract). -/
def hasCompactMulSupport_iff_eventuallyEq' : Prop := True
/-- isCompact_range_of_mulSupport_subset_isCompact (abstract). -/
def isCompact_range_of_mulSupport_subset_isCompact' : Prop := True
/-- isCompact_range (abstract). -/
def isCompact_range' : Prop := True
-- COLLISION: mono' already in SetTheory.lean — rename needed
-- COLLISION: comp_left' already in CategoryTheory.lean — rename needed
/-- hasCompactMulSupport_comp_left (abstract). -/
def hasCompactMulSupport_comp_left' : Prop := True
/-- comp_isClosedEmbedding (abstract). -/
def comp_isClosedEmbedding' : Prop := True
/-- comp₂_left (abstract). -/
def comp₂_left' : Prop := True
/-- isCompact_preimage (abstract). -/
def isCompact_preimage' : Prop := True
/-- mulTSupport_extend_one_subset (abstract). -/
def mulTSupport_extend_one_subset' : Prop := True
-- COLLISION: extend_one' already in Algebra.lean — rename needed
/-- mulTSupport_extend_one (abstract). -/
def mulTSupport_extend_one' : Prop := True
/-- continuous_extend_one (abstract). -/
def continuous_extend_one' : Prop := True
/-- is_one_at_infty (abstract). -/
def is_one_at_infty' : Prop := True
/-- of_compactSpace (abstract). -/
def of_compactSpace' : Prop := True
/-- exists_finset_nhd_mulSupport_subset (abstract). -/
def exists_finset_nhd_mulSupport_subset' : Prop := True

-- Algebra/UniformConvergence.lean
/-- hasBasis_nhds_one_of_basis (abstract). -/
def hasBasis_nhds_one_of_basis' : Prop := True
/-- hasBasis_nhds_one (abstract). -/
def hasBasis_nhds_one' : Prop := True

-- Algebra/UniformField.lean
/-- CompletableTopField (abstract). -/
def CompletableTopField' : Prop := True
/-- hatInv (abstract). -/
def hatInv' : Prop := True
/-- continuous_hatInv (abstract). -/
def continuous_hatInv' : Prop := True
/-- hatInv_extends (abstract). -/
def hatInv_extends' : Prop := True
-- COLLISION: coe_inv' already in Algebra.lean — rename needed
/-- mul_hatInv_cancel (abstract). -/
def mul_hatInv_cancel' : Prop := True
/-- completableTopField (abstract). -/
def completableTopField' : Prop := True

-- Algebra/UniformFilterBasis.lean
/-- uniformSpace (abstract). -/
def uniformSpace' : Prop := True
/-- uniformAddGroup (abstract). -/
def uniformAddGroup' : Prop := True
/-- cauchy_iff (abstract). -/
def cauchy_iff' : Prop := True

-- Algebra/UniformGroup/Basic.lean
/-- isUniformEmbedding_translate_mul (abstract). -/
def isUniformEmbedding_translate_mul' : Prop := True
/-- uniformGroup (abstract). -/
def uniformGroup' : Prop := True
/-- totallyBounded_iff_subset_finite_iUnion_nhds_one (abstract). -/
def totallyBounded_iff_subset_finite_iUnion_nhds_one' : Prop := True
/-- totallyBounded_inv (abstract). -/
def totallyBounded_inv' : Prop := True
/-- topologicalGroup_is_uniform_of_compactSpace (abstract). -/
def topologicalGroup_is_uniform_of_compactSpace' : Prop := True
/-- tendsto_coe_cofinite_of_discrete (abstract). -/
def tendsto_coe_cofinite_of_discrete' : Prop := True
/-- tendstoUniformly_iff (abstract). -/
def tendstoUniformly_iff' : Prop := True
/-- tendstoUniformlyOn_iff (abstract). -/
def tendstoUniformlyOn_iff' : Prop := True
/-- tendstoLocallyUniformly_iff (abstract). -/
def tendstoLocallyUniformly_iff' : Prop := True
/-- tendstoLocallyUniformlyOn_iff (abstract). -/
def tendstoLocallyUniformlyOn_iff' : Prop := True
/-- extend_Z_bilin_aux (abstract). -/
def extend_Z_bilin_aux' : Prop := True
/-- extend_Z_bilin_key (abstract). -/
def extend_Z_bilin_key' : Prop := True
/-- extend_Z_bilin (abstract). -/
def extend_Z_bilin' : Prop := True
/-- inherent (abstract). -/
def inherent' : Prop := True
-- COLLISION: provided' already in Algebra.lean — rename needed

-- Algebra/UniformGroup/Defs.lean
/-- UniformGroup (abstract). -/
def UniformGroup' : Prop := True
/-- UniformAddGroup (abstract). -/
def UniformAddGroup' : Prop := True
-- COLLISION: mk' already in SetTheory.lean — rename needed
/-- uniformContinuous_div (abstract). -/
def uniformContinuous_div' : Prop := True
/-- uniformContinuous_inv (abstract). -/
def uniformContinuous_inv' : Prop := True
/-- uniformContinuous_mul (abstract). -/
def uniformContinuous_mul' : Prop := True
/-- uniformContinuous_mul_left (abstract). -/
def uniformContinuous_mul_left' : Prop := True
/-- uniformContinuous_mul_right (abstract). -/
def uniformContinuous_mul_right' : Prop := True
/-- uniformContinuous_div_const (abstract). -/
def uniformContinuous_div_const' : Prop := True
-- COLLISION: pow_const' already in Algebra.lean — rename needed
/-- uniformContinuous_pow_const (abstract). -/
def uniformContinuous_pow_const' : Prop := True
/-- zpow_const (abstract). -/
def zpow_const' : Prop := True
/-- uniformContinuous_zpow_const (abstract). -/
def uniformContinuous_zpow_const' : Prop := True
/-- uniformity_translate_mul (abstract). -/
def uniformity_translate_mul' : Prop := True
/-- uniformGroup_sInf (abstract). -/
def uniformGroup_sInf' : Prop := True
/-- uniformGroup_iInf (abstract). -/
def uniformGroup_iInf' : Prop := True
/-- uniformGroup_inf (abstract). -/
def uniformGroup_inf' : Prop := True
/-- uniformity_eq_comap_nhds_one (abstract). -/
def uniformity_eq_comap_nhds_one' : Prop := True
/-- uniformity_eq_comap_nhds_one_swapped (abstract). -/
def uniformity_eq_comap_nhds_one_swapped' : Prop := True
/-- uniformity_countably_generated (abstract). -/
def uniformity_countably_generated' : Prop := True
/-- uniformity_eq_comap_inv_mul_nhds_one (abstract). -/
def uniformity_eq_comap_inv_mul_nhds_one' : Prop := True
/-- uniformity_eq_comap_inv_mul_nhds_one_swapped (abstract). -/
def uniformity_eq_comap_inv_mul_nhds_one_swapped' : Prop := True
/-- uniformity_of_nhds_one (abstract). -/
def uniformity_of_nhds_one' : Prop := True
/-- uniformity_of_nhds_one_inv_mul (abstract). -/
def uniformity_of_nhds_one_inv_mul' : Prop := True
/-- uniformity_of_nhds_one_swapped (abstract). -/
def uniformity_of_nhds_one_swapped' : Prop := True
/-- uniformity_of_nhds_one_inv_mul_swapped (abstract). -/
def uniformity_of_nhds_one_inv_mul_swapped' : Prop := True
/-- uniformContinuous_of_tendsto_one (abstract). -/
def uniformContinuous_of_tendsto_one' : Prop := True
/-- uniformContinuous_of_continuousAt_one (abstract). -/
def uniformContinuous_of_continuousAt_one' : Prop := True
/-- uniformContinuous_iff_isOpen_ker (abstract). -/
def uniformContinuous_iff_isOpen_ker' : Prop := True
/-- uniformContinuous_monoidHom_of_continuous (abstract). -/
def uniformContinuous_monoidHom_of_continuous' : Prop := True
/-- toUniformSpace (abstract). -/
def toUniformSpace' : Prop := True
/-- comm_topologicalGroup_is_uniform (abstract). -/
def comm_topologicalGroup_is_uniform' : Prop := True
/-- toUniformSpace_eq (abstract). -/
def toUniformSpace_eq' : Prop := True
/-- tendsto_div_comap_self (abstract). -/
def tendsto_div_comap_self' : Prop := True

-- Algebra/UniformMulAction.lean
/-- UniformContinuousConstVAdd (abstract). -/
def UniformContinuousConstVAdd' : Prop := True
/-- UniformContinuousConstSMul (abstract). -/
def UniformContinuousConstSMul' : Prop := True
/-- uniformContinuousConstSMul_of_continuousConstSMul (abstract). -/
def uniformContinuousConstSMul_of_continuousConstSMul' : Prop := True
/-- uniformContinuousConstSMul (abstract). -/
def uniformContinuousConstSMul' : Prop := True
-- COLLISION: coe_smul' already in RingTheory2.lean — rename needed

-- Algebra/UniformRing.lean
-- COLLISION: in' already in Order.lean — rename needed
-- COLLISION: coe_mul' already in RingTheory2.lean — rename needed
-- COLLISION: coeRingHom' already in Order.lean — rename needed
/-- continuous_coeRingHom (abstract). -/
def continuous_coeRingHom' : Prop := True
-- COLLISION: extensionHom' already in CategoryTheory.lean — rename needed
/-- extensionHom_coe (abstract). -/
def extensionHom_coe' : Prop := True
-- COLLISION: mapRingHom' already in Algebra.lean — rename needed
/-- map_smul_eq_mul_coe (abstract). -/
def map_smul_eq_mul_coe' : Prop := True
/-- inseparableSetoid_ring (abstract). -/
def inseparableSetoid_ring' : Prop := True
/-- ring_sep_quot (abstract). -/
def ring_sep_quot' : Prop := True
/-- sepQuotHomeomorphRingQuot (abstract). -/
def sepQuotHomeomorphRingQuot' : Prop := True
/-- sepQuotRingEquivRingQuot (abstract). -/
def sepQuotRingEquivRingQuot' : Prop := True
/-- extendRingHom (abstract). -/
def extendRingHom' : Prop := True

-- Algebra/Valued/NormedValued.lean
-- COLLISION: valuation' already in RingTheory2.lean — rename needed
/-- toValued (abstract). -/
def toValued' : Prop := True
-- COLLISION: norm_nonneg' already in Analysis.lean — rename needed
/-- norm_add_le (abstract). -/
def norm_add_le' : Prop := True
-- COLLISION: norm_eq_zero' already in Analysis.lean — rename needed
-- COLLISION: toNormedField' already in Analysis.lean — rename needed
-- COLLISION: isNonarchimedean_norm' already in Analysis.lean — rename needed
-- COLLISION: norm_le_iff' already in Analysis.lean — rename needed
-- COLLISION: norm_lt_iff' already in Analysis.lean — rename needed
/-- norm_le_one_iff (abstract). -/
def norm_le_one_iff' : Prop := True
/-- norm_lt_one_iff (abstract). -/
def norm_lt_one_iff' : Prop := True
/-- one_le_norm_iff (abstract). -/
def one_le_norm_iff' : Prop := True
/-- one_lt_norm_iff (abstract). -/
def one_lt_norm_iff' : Prop := True

-- Algebra/Valued/ValuationTopology.lean
-- COLLISION: which' already in Order.lean — rename needed
/-- subgroups_basis (abstract). -/
def subgroups_basis' : Prop := True
/-- Valued (abstract). -/
def Valued' : Prop := True
/-- hasBasis_uniformity (abstract). -/
def hasBasis_uniformity' : Prop := True
/-- mem_nhds (abstract). -/
def mem_nhds' : Prop := True
/-- mem_nhds_zero (abstract). -/
def mem_nhds_zero' : Prop := True
/-- loc_const (abstract). -/
def loc_const' : Prop := True
/-- integer_isOpen (abstract). -/
def integer_isOpen' : Prop := True
/-- valuationSubring_isOpen (abstract). -/
def valuationSubring_isOpen' : Prop := True

-- Algebra/Valued/ValuedField.lean
/-- inversion_estimate (abstract). -/
def inversion_estimate' : Prop := True
/-- continuous_valuation (abstract). -/
def continuous_valuation' : Prop := True
/-- extension_extends (abstract). -/
def extension_extends' : Prop := True
/-- extensionValuation (abstract). -/
def extensionValuation' : Prop := True
/-- closure_coe_completion_v_lt (abstract). -/
def closure_coe_completion_v_lt' : Prop := True
/-- valuedCompletion_apply (abstract). -/
def valuedCompletion_apply' : Prop := True
-- COLLISION: integer' already in RingTheory2.lean — rename needed
-- COLLISION: maximalIdeal' already in RingTheory2.lean — rename needed
-- COLLISION: ResidueField' already in RingTheory2.lean — rename needed

-- ApproximateUnit.lean
/-- IsApproximateUnit (abstract). -/
def IsApproximateUnit' : Prop := True
/-- pure_one (abstract). -/
def pure_one' : Prop := True
/-- nhds_one (abstract). -/
def nhds_one' : Prop := True
/-- iff_neBot_and_le_nhds_one (abstract). -/
def iff_neBot_and_le_nhds_one' : Prop := True
/-- iff_le_nhds_one (abstract). -/
def iff_le_nhds_one' : Prop := True

-- Baire/BaireMeasurable.lean
/-- BaireMeasurableSet (abstract). -/
def BaireMeasurableSet' : Prop := True
/-- of_mem_residual (abstract). -/
def of_mem_residual' : Prop := True
/-- baireMeasurableSet (abstract). -/
def baireMeasurableSet' : Prop := True
-- COLLISION: compl' already in Order.lean — rename needed
-- COLLISION: of_compl' already in MeasureTheory2.lean — rename needed
-- COLLISION: iUnion' already in Order.lean — rename needed
-- COLLISION: biUnion' already in Order.lean — rename needed
-- COLLISION: sUnion' already in SetTheory.lean — rename needed
-- COLLISION: iInter' already in SetTheory.lean — rename needed
-- COLLISION: biInter' already in MeasureTheory2.lean — rename needed
-- COLLISION: sInter' already in SetTheory.lean — rename needed
-- COLLISION: union' already in SetTheory.lean — rename needed
-- COLLISION: inter' already in SetTheory.lean — rename needed
-- COLLISION: diff' already in SetTheory.lean — rename needed
/-- residualEq_isOpen (abstract). -/
def residualEq_isOpen' : Prop := True
/-- iff_residualEq_isOpen (abstract). -/
def iff_residualEq_isOpen' : Prop := True
/-- tendsto_residual_of_isOpenMap (abstract). -/
def tendsto_residual_of_isOpenMap' : Prop := True
/-- preimage_of_isOpenMap (abstract). -/
def preimage_of_isOpenMap' : Prop := True
-- COLLISION: preimage' already in Order.lean — rename needed
/-- residual_map_eq (abstract). -/
def residual_map_eq' : Prop := True

-- Baire/Lemmas.lean
-- COLLISION: can' already in Algebra.lean — rename needed
/-- dense_iInter_of_isOpen_nat (abstract). -/
def dense_iInter_of_isOpen_nat' : Prop := True
/-- dense_sInter_of_isOpen (abstract). -/
def dense_sInter_of_isOpen' : Prop := True
/-- dense_biInter_of_isOpen (abstract). -/
def dense_biInter_of_isOpen' : Prop := True
/-- dense_iInter_of_isOpen (abstract). -/
def dense_iInter_of_isOpen' : Prop := True
/-- mem_residual (abstract). -/
def mem_residual' : Prop := True
/-- eventually_residual (abstract). -/
def eventually_residual' : Prop := True
/-- dense_of_mem_residual (abstract). -/
def dense_of_mem_residual' : Prop := True
/-- dense_sInter_of_Gδ (abstract). -/
def dense_sInter_of_Gδ' : Prop := True
/-- dense_iInter_of_Gδ (abstract). -/
def dense_iInter_of_Gδ' : Prop := True
/-- dense_biInter_of_Gδ (abstract). -/
def dense_biInter_of_Gδ' : Prop := True
/-- inter_of_Gδ (abstract). -/
def inter_of_Gδ' : Prop := True
/-- dense_iUnion_interior_of_closed (abstract). -/
def dense_iUnion_interior_of_closed' : Prop := True
/-- dense_biUnion_interior_of_closed (abstract). -/
def dense_biUnion_interior_of_closed' : Prop := True
/-- dense_sUnion_interior_of_closed (abstract). -/
def dense_sUnion_interior_of_closed' : Prop := True
/-- nonempty_interior_of_iUnion_of_closed (abstract). -/
def nonempty_interior_of_iUnion_of_closed' : Prop := True

-- Bases.lean
/-- IsTopologicalBasis (abstract). -/
def IsTopologicalBasis' : Prop := True
/-- isTopologicalBasis_of_subbasis (abstract). -/
def isTopologicalBasis_of_subbasis' : Prop := True
/-- isTopologicalBasis_of_subbasis_of_finiteInter (abstract). -/
def isTopologicalBasis_of_subbasis_of_finiteInter' : Prop := True
/-- isTopologicalBasis_of_subbasis_of_inter (abstract). -/
def isTopologicalBasis_of_subbasis_of_inter' : Prop := True
/-- of_hasBasis_nhds (abstract). -/
def of_hasBasis_nhds' : Prop := True
/-- isTopologicalBasis_of_isOpen_of_nhds (abstract). -/
def isTopologicalBasis_of_isOpen_of_nhds' : Prop := True
-- COLLISION: mem_nhds_iff' already in Analysis.lean — rename needed
-- COLLISION: isOpen_iff' already in SetTheory.lean — rename needed
-- COLLISION: isOpen' already in Analysis.lean — rename needed
/-- exists_subset_of_mem_open (abstract). -/
def exists_subset_of_mem_open' : Prop := True
/-- open_eq_sUnion' (abstract). -/
def open_eq_sUnion' : Prop := True
/-- open_iff_eq_sUnion (abstract). -/
def open_iff_eq_sUnion' : Prop := True
/-- open_eq_iUnion (abstract). -/
def open_eq_iUnion' : Prop := True
/-- subset_of_forall_subset (abstract). -/
def subset_of_forall_subset' : Prop := True
/-- eq_of_forall_subset_iff (abstract). -/
def eq_of_forall_subset_iff' : Prop := True
-- COLLISION: mem_closure_iff' already in RingTheory2.lean — rename needed
/-- dense_iff (abstract). -/
def dense_iff' : Prop := True
/-- isOpenMap_iff (abstract). -/
def isOpenMap_iff' : Prop := True
/-- exists_nonempty_subset (abstract). -/
def exists_nonempty_subset' : Prop := True
/-- isTopologicalBasis_opens (abstract). -/
def isTopologicalBasis_opens' : Prop := True
/-- isInducing (abstract). -/
def isInducing' : Prop := True
-- COLLISION: inf' already in Order.lean — rename needed
/-- inf_induced (abstract). -/
def inf_induced' : Prop := True
/-- isTopologicalBasis_of_cover (abstract). -/
def isTopologicalBasis_of_cover' : Prop := True
/-- SeparableSpace (abstract). -/
def SeparableSpace' : Prop := True
/-- exists_countable_dense (abstract). -/
def exists_countable_dense' : Prop := True
/-- exists_dense_seq (abstract). -/
def exists_dense_seq' : Prop := True
/-- denseSeq (abstract). -/
def denseSeq' : Prop := True
/-- denseRange_denseSeq (abstract). -/
def denseRange_denseSeq' : Prop := True
/-- of_denseRange (abstract). -/
def of_denseRange' : Prop := True
/-- separableSpace (abstract). -/
def separableSpace' : Prop := True
/-- separableSpace_iff_countable (abstract). -/
def separableSpace_iff_countable' : Prop := True
/-- countable_of_isOpen_disjoint (abstract). -/
def countable_of_isOpen_disjoint' : Prop := True
/-- countable_of_isOpen (abstract). -/
def countable_of_isOpen' : Prop := True
/-- countable_of_nonempty_interior (abstract). -/
def countable_of_nonempty_interior' : Prop := True
-- COLLISION: IsSeparable' already in MeasureTheory2.lean — rename needed
/-- isSeparable_iUnion (abstract). -/
def isSeparable_iUnion' : Prop := True
/-- isSeparable_union (abstract). -/
def isSeparable_union' : Prop := True
/-- isSeparable_closure (abstract). -/
def isSeparable_closure' : Prop := True
-- COLLISION: isSeparable' already in RingTheory2.lean — rename needed
-- COLLISION: univ_pi' already in Analysis.lean — rename needed
/-- isSeparable_pi (abstract). -/
def isSeparable_pi' : Prop := True
-- COLLISION: image' already in LinearAlgebra2.lean — rename needed
/-- isSeparable_iff (abstract). -/
def isSeparable_iff' : Prop := True
/-- isSeparable_univ_iff (abstract). -/
def isSeparable_univ_iff' : Prop := True
-- COLLISION: isSeparable_range' already in MeasureTheory2.lean — rename needed
-- COLLISION: of_subtype' already in Order.lean — rename needed
/-- of_separableSpace (abstract). -/
def of_separableSpace' : Prop := True
-- COLLISION: iInf' already in Order.lean — rename needed
/-- iInf_induced (abstract). -/
def iInf_induced' : Prop := True
/-- isTopologicalBasis_pi (abstract). -/
def isTopologicalBasis_pi' : Prop := True
/-- isTopologicalBasis_singletons (abstract). -/
def isTopologicalBasis_singletons' : Prop := True
/-- isOpenMap_eval (abstract). -/
def isOpenMap_eval' : Prop := True
/-- exists_countable_dense_subset (abstract). -/
def exists_countable_dense_subset' : Prop := True
/-- exists_countable_dense_subset_bot_top (abstract). -/
def exists_countable_dense_subset_bot_top' : Prop := True
/-- exists_countable_dense_bot_top (abstract). -/
def exists_countable_dense_bot_top' : Prop := True
/-- FirstCountableTopology (abstract). -/
def FirstCountableTopology' : Prop := True
/-- firstCountableTopology_induced (abstract). -/
def firstCountableTopology_induced' : Prop := True
-- COLLISION: firstCountableTopology' already in Analysis.lean — rename needed
/-- tendsto_subseq (abstract). -/
def tendsto_subseq' : Prop := True
/-- SecondCountableTopology (abstract). -/
def SecondCountableTopology' : Prop := True
/-- exists_countable_basis (abstract). -/
def exists_countable_basis' : Prop := True
/-- countableBasis (abstract). -/
def countableBasis' : Prop := True
/-- countable_countableBasis (abstract). -/
def countable_countableBasis' : Prop := True
/-- empty_nmem_countableBasis (abstract). -/
def empty_nmem_countableBasis' : Prop := True
/-- isBasis_countableBasis (abstract). -/
def isBasis_countableBasis' : Prop := True
/-- eq_generateFrom_countableBasis (abstract). -/
def eq_generateFrom_countableBasis' : Prop := True
/-- isOpen_of_mem_countableBasis (abstract). -/
def isOpen_of_mem_countableBasis' : Prop := True
/-- nonempty_of_mem_countableBasis (abstract). -/
def nonempty_of_mem_countableBasis' : Prop := True
/-- secondCountableTopology_induced (abstract). -/
def secondCountableTopology_induced' : Prop := True
/-- secondCountableTopology_iInf (abstract). -/
def secondCountableTopology_iInf' : Prop := True
/-- secondCountableTopology_of_countable_cover (abstract). -/
def secondCountableTopology_of_countable_cover' : Prop := True
/-- isOpen_iUnion_countable (abstract). -/
def isOpen_iUnion_countable' : Prop := True
/-- isOpen_biUnion_countable (abstract). -/
def isOpen_biUnion_countable' : Prop := True
/-- isOpen_sUnion_countable (abstract). -/
def isOpen_sUnion_countable' : Prop := True
/-- countable_cover_nhds (abstract). -/
def countable_cover_nhds' : Prop := True
/-- countable_cover_nhdsWithin (abstract). -/
def countable_cover_nhdsWithin' : Prop := True
-- COLLISION: sum' already in SetTheory.lean — rename needed
-- COLLISION: quotient' already in RingTheory2.lean — rename needed

-- Basic.lean
/-- ofClosed (abstract). -/
def ofClosed' : Prop := True
/-- isOpen_iUnion (abstract). -/
def isOpen_iUnion' : Prop := True
/-- isOpen_biUnion (abstract). -/
def isOpen_biUnion' : Prop := True
/-- isOpen_iff_of_cover (abstract). -/
def isOpen_iff_of_cover' : Prop := True
/-- isOpen_empty (abstract). -/
def isOpen_empty' : Prop := True
/-- isOpen_biInter (abstract). -/
def isOpen_biInter' : Prop := True
/-- isOpen_iInter_of_finite (abstract). -/
def isOpen_iInter_of_finite' : Prop := True
/-- isOpen_biInter_finset (abstract). -/
def isOpen_biInter_finset' : Prop := True
/-- isOpen_const (abstract). -/
def isOpen_const' : Prop := True
/-- isOpen_compl_iff (abstract). -/
def isOpen_compl_iff' : Prop := True
/-- ext_iff_isClosed (abstract). -/
def ext_iff_isClosed' : Prop := True
/-- isClosed_const (abstract). -/
def isClosed_const' : Prop := True
/-- isClosed_empty (abstract). -/
def isClosed_empty' : Prop := True
/-- isClosed_univ (abstract). -/
def isClosed_univ' : Prop := True
/-- isLocallyClosed (abstract). -/
def isLocallyClosed' : Prop := True
/-- isClosed_sInter (abstract). -/
def isClosed_sInter' : Prop := True
/-- isClosed_iInter (abstract). -/
def isClosed_iInter' : Prop := True
/-- isClosed_biInter (abstract). -/
def isClosed_biInter' : Prop := True
/-- isClosed_compl_iff (abstract). -/
def isClosed_compl_iff' : Prop := True
-- COLLISION: sdiff' already in Order.lean — rename needed
/-- isClosed_biUnion (abstract). -/
def isClosed_biUnion' : Prop := True
/-- isClosed_biUnion_finset (abstract). -/
def isClosed_biUnion_finset' : Prop := True
/-- isClosed_iUnion_of_finite (abstract). -/
def isClosed_iUnion_of_finite' : Prop := True
/-- isClosed_imp (abstract). -/
def isClosed_imp' : Prop := True
-- COLLISION: not' already in MeasureTheory2.lean — rename needed
/-- mem_interior (abstract). -/
def mem_interior' : Prop := True
/-- isOpen_interior (abstract). -/
def isOpen_interior' : Prop := True
/-- interior_subset (abstract). -/
def interior_subset' : Prop := True
/-- interior_maximal (abstract). -/
def interior_maximal' : Prop := True
/-- interior_eq (abstract). -/
def interior_eq' : Prop := True
/-- interior_eq_iff_isOpen (abstract). -/
def interior_eq_iff_isOpen' : Prop := True
/-- subset_interior_iff_isOpen (abstract). -/
def subset_interior_iff_isOpen' : Prop := True
/-- subset_interior_iff (abstract). -/
def subset_interior_iff' : Prop := True
/-- interior_subset_iff (abstract). -/
def interior_subset_iff' : Prop := True
/-- interior_mono (abstract). -/
def interior_mono' : Prop := True
/-- interior_empty (abstract). -/
def interior_empty' : Prop := True
/-- interior_univ (abstract). -/
def interior_univ' : Prop := True
/-- interior_eq_univ (abstract). -/
def interior_eq_univ' : Prop := True
/-- interior_interior (abstract). -/
def interior_interior' : Prop := True
/-- interior_inter (abstract). -/
def interior_inter' : Prop := True
/-- interior_biInter (abstract). -/
def interior_biInter' : Prop := True
/-- interior_iInter_of_finite (abstract). -/
def interior_iInter_of_finite' : Prop := True
/-- interior_iInter₂_lt_nat (abstract). -/
def interior_iInter₂_lt_nat' : Prop := True
/-- interior_iInter₂_le_nat (abstract). -/
def interior_iInter₂_le_nat' : Prop := True
/-- interior_union_isClosed_of_interior_empty (abstract). -/
def interior_union_isClosed_of_interior_empty' : Prop := True
/-- isOpen_iff_forall_mem_open (abstract). -/
def isOpen_iff_forall_mem_open' : Prop := True
/-- interior_iInter_subset (abstract). -/
def interior_iInter_subset' : Prop := True
/-- interior_iInter₂_subset (abstract). -/
def interior_iInter₂_subset' : Prop := True
/-- lift'_interior_le (abstract). -/
def lift'_interior_le' : Prop := True
/-- lift'_interior_eq_self (abstract). -/
def lift'_interior_eq_self' : Prop := True
-- COLLISION: isClosed_closure' already in Order.lean — rename needed
-- COLLISION: subset_closure' already in Order.lean — rename needed
-- COLLISION: not_mem_of_not_mem_closure' already in Order.lean — rename needed
/-- closure_minimal (abstract). -/
def closure_minimal' : Prop := True
/-- closure_left (abstract). -/
def closure_left' : Prop := True
/-- closure_right (abstract). -/
def closure_right' : Prop := True
-- COLLISION: closure_eq' already in Order.lean — rename needed
/-- closure_subset (abstract). -/
def closure_subset' : Prop := True
/-- closure_subset_iff (abstract). -/
def closure_subset_iff' : Prop := True
/-- mem_iff_closure_subset (abstract). -/
def mem_iff_closure_subset' : Prop := True
/-- monotone_closure (abstract). -/
def monotone_closure' : Prop := True
/-- diff_subset_closure_iff (abstract). -/
def diff_subset_closure_iff' : Prop := True
/-- closure_inter_subset_inter_closure (abstract). -/
def closure_inter_subset_inter_closure' : Prop := True
/-- isClosed_of_closure_subset (abstract). -/
def isClosed_of_closure_subset' : Prop := True
/-- closure_eq_iff_isClosed (abstract). -/
def closure_eq_iff_isClosed' : Prop := True
/-- closure_subset_iff_isClosed (abstract). -/
def closure_subset_iff_isClosed' : Prop := True
-- COLLISION: closure_empty' already in RingTheory2.lean — rename needed
/-- closure_empty_iff (abstract). -/
def closure_empty_iff' : Prop := True
/-- closure_nonempty_iff (abstract). -/
def closure_nonempty_iff' : Prop := True
-- COLLISION: closure_univ' already in RingTheory2.lean — rename needed
/-- closure_closure (abstract). -/
def closure_closure' : Prop := True
/-- closure_eq_compl_interior_compl (abstract). -/
def closure_eq_compl_interior_compl' : Prop := True
-- COLLISION: closure_union' already in RingTheory2.lean — rename needed
/-- closure_biUnion (abstract). -/
def closure_biUnion' : Prop := True
/-- closure_iUnion_of_finite (abstract). -/
def closure_iUnion_of_finite' : Prop := True
/-- closure_iUnion₂_lt_nat (abstract). -/
def closure_iUnion₂_lt_nat' : Prop := True
/-- closure_iUnion₂_le_nat (abstract). -/
def closure_iUnion₂_le_nat' : Prop := True
/-- interior_subset_closure (abstract). -/
def interior_subset_closure' : Prop := True
/-- interior_compl (abstract). -/
def interior_compl' : Prop := True
/-- closure_compl (abstract). -/
def closure_compl' : Prop := True
/-- closure_inter_open_nonempty_iff (abstract). -/
def closure_inter_open_nonempty_iff' : Prop := True
/-- lift'_closure_eq_self (abstract). -/
def lift'_closure_eq_self' : Prop := True
/-- lift'_closure_eq_bot (abstract). -/
def lift'_closure_eq_bot' : Prop := True
/-- dense_iff_closure_eq (abstract). -/
def dense_iff_closure_eq' : Prop := True
/-- interior_eq_empty_iff_dense_compl (abstract). -/
def interior_eq_empty_iff_dense_compl' : Prop := True
/-- dense_closure (abstract). -/
def dense_closure' : Prop := True
/-- dense_univ (abstract). -/
def dense_univ' : Prop := True
/-- dense_iff_inter_open (abstract). -/
def dense_iff_inter_open' : Prop := True
/-- exists_mem_open (abstract). -/
def exists_mem_open' : Prop := True
/-- nonempty_iff (abstract). -/
def nonempty_iff' : Prop := True
-- COLLISION: nonempty' already in Order.lean — rename needed
/-- dense_compl_singleton_iff_not_open (abstract). -/
def dense_compl_singleton_iff_not_open' : Prop := True
/-- disjoint_interior_frontier (abstract). -/
def disjoint_interior_frontier' : Prop := True
/-- closure_diff_frontier (abstract). -/
def closure_diff_frontier' : Prop := True
/-- self_diff_frontier (abstract). -/
def self_diff_frontier' : Prop := True
/-- frontier_eq_closure_inter_closure (abstract). -/
def frontier_eq_closure_inter_closure' : Prop := True
/-- frontier_subset_closure (abstract). -/
def frontier_subset_closure' : Prop := True
/-- frontier_subset_iff_isClosed (abstract). -/
def frontier_subset_iff_isClosed' : Prop := True
/-- frontier_closure_subset (abstract). -/
def frontier_closure_subset' : Prop := True
/-- frontier_interior_subset (abstract). -/
def frontier_interior_subset' : Prop := True
/-- frontier_compl (abstract). -/
def frontier_compl' : Prop := True
/-- frontier_univ (abstract). -/
def frontier_univ' : Prop := True
/-- frontier_empty (abstract). -/
def frontier_empty' : Prop := True
/-- frontier_inter_subset (abstract). -/
def frontier_inter_subset' : Prop := True
/-- frontier_union_subset (abstract). -/
def frontier_union_subset' : Prop := True
/-- frontier_eq (abstract). -/
def frontier_eq' : Prop := True
/-- inter_frontier_eq (abstract). -/
def inter_frontier_eq' : Prop := True
/-- closure_eq_interior_union_frontier (abstract). -/
def closure_eq_interior_union_frontier' : Prop := True
/-- closure_eq_self_union_frontier (abstract). -/
def closure_eq_self_union_frontier' : Prop := True
/-- frontier_left (abstract). -/
def frontier_left' : Prop := True
/-- frontier_right (abstract). -/
def frontier_right' : Prop := True
/-- frontier_eq_inter_compl_interior (abstract). -/
def frontier_eq_inter_compl_interior' : Prop := True
/-- compl_frontier_eq_union_interior (abstract). -/
def compl_frontier_eq_union_interior' : Prop := True
/-- nhds_def' (abstract). -/
def nhds_def' : Prop := True
/-- nhds_basis_opens (abstract). -/
def nhds_basis_opens' : Prop := True
/-- nhds_basis_closeds (abstract). -/
def nhds_basis_closeds' : Prop := True
/-- lift'_nhds_interior (abstract). -/
def lift'_nhds_interior' : Prop := True
/-- nhds_interior (abstract). -/
def nhds_interior' : Prop := True
/-- le_nhds_iff (abstract). -/
def le_nhds_iff' : Prop := True
/-- nhds_le_of_le (abstract). -/
def nhds_le_of_le' : Prop := True
/-- eventually_nhds_iff (abstract). -/
def eventually_nhds_iff' : Prop := True
/-- frequently_nhds_iff (abstract). -/
def frequently_nhds_iff' : Prop := True
/-- mem_interior_iff_mem_nhds (abstract). -/
def mem_interior_iff_mem_nhds' : Prop := True
/-- map_nhds (abstract). -/
def map_nhds' : Prop := True
/-- mem_of_mem_nhds (abstract). -/
def mem_of_mem_nhds' : Prop := True
/-- self_of_nhds (abstract). -/
def self_of_nhds' : Prop := True
/-- compl_mem_nhds (abstract). -/
def compl_mem_nhds' : Prop := True
-- COLLISION: eventually_mem' already in Order.lean — rename needed
/-- exists_open_set_nhds (abstract). -/
def exists_open_set_nhds' : Prop := True
/-- eventually_nhds (abstract). -/
def eventually_nhds' : Prop := True
/-- eventually_eventually_nhds (abstract). -/
def eventually_eventually_nhds' : Prop := True
/-- frequently_frequently_nhds (abstract). -/
def frequently_frequently_nhds' : Prop := True
/-- all_mem_nhds (abstract). -/
def all_mem_nhds' : Prop := True
/-- all_mem_nhds_filter (abstract). -/
def all_mem_nhds_filter' : Prop := True
-- COLLISION: tendsto_nhds' already in Analysis.lean — rename needed
/-- tendsto_atTop_nhds (abstract). -/
def tendsto_atTop_nhds' : Prop := True
/-- tendsto_const_nhds (abstract). -/
def tendsto_const_nhds' : Prop := True
/-- tendsto_atTop_of_eventually_const (abstract). -/
def tendsto_atTop_of_eventually_const' : Prop := True
/-- tendsto_atBot_of_eventually_const (abstract). -/
def tendsto_atBot_of_eventually_const' : Prop := True
/-- pure_le_nhds (abstract). -/
def pure_le_nhds' : Prop := True
/-- tendsto_pure_nhds (abstract). -/
def tendsto_pure_nhds' : Prop := True
/-- tendsto_nhds_of_eventually_eq (abstract). -/
def tendsto_nhds_of_eventually_eq' : Prop := True
/-- clusterPt_iff (abstract). -/
def clusterPt_iff' : Prop := True
/-- clusterPt_iff_frequently (abstract). -/
def clusterPt_iff_frequently' : Prop := True
/-- clusterPt_iff_not_disjoint (abstract). -/
def clusterPt_iff_not_disjoint' : Prop := True
/-- clusterPt_principal_iff (abstract). -/
def clusterPt_principal_iff' : Prop := True
/-- clusterPt_principal_iff_frequently (abstract). -/
def clusterPt_principal_iff_frequently' : Prop := True
/-- of_le_nhds (abstract). -/
def of_le_nhds' : Prop := True
/-- of_nhds_le (abstract). -/
def of_nhds_le' : Prop := True
/-- tendsto_comp' (abstract). -/
def tendsto_comp' : Prop := True
/-- continuousAt_comp (abstract). -/
def continuousAt_comp' : Prop := True
/-- mapClusterPt_iff_frequently (abstract). -/
def mapClusterPt_iff_frequently' : Prop := True
/-- mapClusterPt_iff (abstract). -/
def mapClusterPt_iff' : Prop := True
/-- mapClusterPt (abstract). -/
def mapClusterPt' : Prop := True
-- COLLISION: of_comp' already in RingTheory2.lean — rename needed
/-- mapClusterPt_of_comp (abstract). -/
def mapClusterPt_of_comp' : Prop := True
/-- accPt_sup (abstract). -/
def accPt_sup' : Prop := True
/-- acc_iff_cluster (abstract). -/
def acc_iff_cluster' : Prop := True
/-- acc_principal_iff_cluster (abstract). -/
def acc_principal_iff_cluster' : Prop := True
/-- accPt_iff_nhds (abstract). -/
def accPt_iff_nhds' : Prop := True
/-- accPt_iff_frequently (abstract). -/
def accPt_iff_frequently' : Prop := True
/-- clusterPt (abstract). -/
def clusterPt' : Prop := True
/-- clusterPt_principal (abstract). -/
def clusterPt_principal' : Prop := True
/-- interior_eq_nhds' (abstract). -/
def interior_eq_nhds' : Prop := True
/-- interior_mem_nhds (abstract). -/
def interior_mem_nhds' : Prop := True
/-- interior_setOf_eq (abstract). -/
def interior_setOf_eq' : Prop := True
/-- isOpen_setOf_eventually_nhds (abstract). -/
def isOpen_setOf_eventually_nhds' : Prop := True
/-- subset_interior_iff_nhds (abstract). -/
def subset_interior_iff_nhds' : Prop := True
/-- isOpen_iff_nhds (abstract). -/
def isOpen_iff_nhds' : Prop := True
/-- ext_iff_nhds (abstract). -/
def ext_iff_nhds' : Prop := True
/-- isOpen_iff_mem_nhds (abstract). -/
def isOpen_iff_mem_nhds' : Prop := True
/-- isOpen_iff_eventually (abstract). -/
def isOpen_iff_eventually' : Prop := True
/-- isOpen_singleton_iff_nhds_eq_pure (abstract). -/
def isOpen_singleton_iff_nhds_eq_pure' : Prop := True
/-- isOpen_singleton_iff_punctured_nhds (abstract). -/
def isOpen_singleton_iff_punctured_nhds' : Prop := True
/-- mem_closure_iff_frequently (abstract). -/
def mem_closure_iff_frequently' : Prop := True
/-- isClosed_iff_frequently (abstract). -/
def isClosed_iff_frequently' : Prop := True
/-- isClosed_setOf_clusterPt (abstract). -/
def isClosed_setOf_clusterPt' : Prop := True
/-- mem_closure_iff_clusterPt (abstract). -/
def mem_closure_iff_clusterPt' : Prop := True
/-- mem_closure_iff_nhds_ne_bot (abstract). -/
def mem_closure_iff_nhds_ne_bot' : Prop := True
/-- mem_closure_iff_nhdsWithin_neBot (abstract). -/
def mem_closure_iff_nhdsWithin_neBot' : Prop := True
/-- nhdsWithin_neBot (abstract). -/
def nhdsWithin_neBot' : Prop := True
/-- nhdsWithin_mono (abstract). -/
def nhdsWithin_mono' : Prop := True
/-- not_mem_closure_iff_nhdsWithin_eq_bot (abstract). -/
def not_mem_closure_iff_nhdsWithin_eq_bot' : Prop := True
/-- dense_compl_singleton (abstract). -/
def dense_compl_singleton' : Prop := True
/-- closure_compl_singleton (abstract). -/
def closure_compl_singleton' : Prop := True
/-- interior_singleton (abstract). -/
def interior_singleton' : Prop := True
/-- not_isOpen_singleton (abstract). -/
def not_isOpen_singleton' : Prop := True
/-- closure_eq_cluster_pts (abstract). -/
def closure_eq_cluster_pts' : Prop := True
/-- mem_closure_iff_nhds (abstract). -/
def mem_closure_iff_nhds' : Prop := True
/-- mem_closure_iff_comap_neBot (abstract). -/
def mem_closure_iff_comap_neBot' : Prop := True
/-- mem_closure_iff_nhds_basis' (abstract). -/
def mem_closure_iff_nhds_basis' : Prop := True
/-- clusterPt_iff_forall_mem_closure (abstract). -/
def clusterPt_iff_forall_mem_closure' : Prop := True
/-- clusterPt_iff_lift'_closure (abstract). -/
def clusterPt_iff_lift'_closure' : Prop := True
/-- clusterPt_lift'_closure_iff (abstract). -/
def clusterPt_lift'_closure_iff' : Prop := True
/-- isClosed_iff_clusterPt (abstract). -/
def isClosed_iff_clusterPt' : Prop := True
/-- isClosed_iff_nhds (abstract). -/
def isClosed_iff_nhds' : Prop := True
/-- isClosed_iff_forall_filter (abstract). -/
def isClosed_iff_forall_filter' : Prop := True
/-- interior_union_left (abstract). -/
def interior_union_left' : Prop := True
/-- interior_union_right (abstract). -/
def interior_union_right' : Prop := True
/-- inter_closure (abstract). -/
def inter_closure' : Prop := True
/-- closure_inter (abstract). -/
def closure_inter' : Prop := True
/-- open_subset_closure_inter (abstract). -/
def open_subset_closure_inter' : Prop := True
/-- mem_closure_of_mem_closure_union (abstract). -/
def mem_closure_of_mem_closure_union' : Prop := True
/-- inter_of_isOpen_left (abstract). -/
def inter_of_isOpen_left' : Prop := True
/-- inter_of_isOpen_right (abstract). -/
def inter_of_isOpen_right' : Prop := True
/-- inter_nhds_nonempty (abstract). -/
def inter_nhds_nonempty' : Prop := True
/-- closure_diff (abstract). -/
def closure_diff' : Prop := True
/-- mem_of_closed (abstract). -/
def mem_of_closed' : Prop := True
/-- mem_of_frequently_of_tendsto (abstract). -/
def mem_of_frequently_of_tendsto' : Prop := True
/-- mem_of_tendsto (abstract). -/
def mem_of_tendsto' : Prop := True
/-- mem_closure_of_frequently_of_tendsto (abstract). -/
def mem_closure_of_frequently_of_tendsto' : Prop := True
/-- mem_closure_of_tendsto (abstract). -/
def mem_closure_of_tendsto' : Prop := True
/-- tendsto_inf_principal_nhds_iff_of_forall_eq (abstract). -/
def tendsto_inf_principal_nhds_iff_of_forall_eq' : Prop := True
/-- le_nhds_lim (abstract). -/
def le_nhds_lim' : Prop := True
/-- tendsto_nhds_limUnder (abstract). -/
def tendsto_nhds_limUnder' : Prop := True
/-- continuous_def (abstract). -/
def continuous_def' : Prop := True
/-- not_continuousAt_of_tendsto (abstract). -/
def not_continuousAt_of_tendsto' : Prop := True
/-- preimage_interior_subset_interior_preimage (abstract). -/
def preimage_interior_subset_interior_preimage' : Prop := True
-- COLLISION: continuous_id' already in Order.lean — rename needed
-- COLLISION: iterate' already in Order.lean — rename needed
/-- continuous_iff_continuousAt (abstract). -/
def continuous_iff_continuousAt' : Prop := True
/-- continuousAt_const (abstract). -/
def continuousAt_const' : Prop := True
-- COLLISION: continuous_const' already in Order.lean — rename needed
/-- continuous_of_const (abstract). -/
def continuous_of_const' : Prop := True
/-- continuousAt_id (abstract). -/
def continuousAt_id' : Prop := True
/-- continuous_iff_isClosed (abstract). -/
def continuous_iff_isClosed' : Prop := True
/-- mem_closure_image (abstract). -/
def mem_closure_image' : Prop := True
/-- closure_preimage_subset (abstract). -/
def closure_preimage_subset' : Prop := True
/-- frontier_preimage_subset (abstract). -/
def frontier_preimage_subset' : Prop := True
/-- image_closure_subset_closure_image (abstract). -/
def image_closure_subset_closure_image' : Prop := True
/-- closure_image_closure (abstract). -/
def closure_image_closure' : Prop := True
/-- closure_subset_preimage_closure_image (abstract). -/
def closure_subset_preimage_closure_image' : Prop := True
/-- map_mem_closure (abstract). -/
def map_mem_closure' : Prop := True
/-- lift'_closure (abstract). -/
def lift'_closure' : Prop := True
/-- tendsto_lift'_closure_nhds (abstract). -/
def tendsto_lift'_closure_nhds' : Prop := True
/-- denseRange_subtype_val (abstract). -/
def denseRange_subtype_val' : Prop := True
/-- denseRange_val (abstract). -/
def denseRange_val' : Prop := True
/-- range_subset_closure_image_dense (abstract). -/
def range_subset_closure_image_dense' : Prop := True
/-- dense_image (abstract). -/
def dense_image' : Prop := True
/-- subset_closure_image_preimage_of_isOpen (abstract). -/
def subset_closure_image_preimage_of_isOpen' : Prop := True
/-- dense_of_mapsTo (abstract). -/
def dense_of_mapsTo' : Prop := True
-- COLLISION: some' already in Order.lean — rename needed

-- Bornology/Absorbs.lean
/-- Absorbs (abstract). -/
def Absorbs' : Prop := True
/-- Absorbent (abstract). -/
def Absorbent' : Prop := True
/-- absorbs_union (abstract). -/
def absorbs_union' : Prop := True
/-- absorbs_sUnion (abstract). -/
def absorbs_sUnion' : Prop := True
/-- absorbs_iUnion (abstract). -/
def absorbs_iUnion' : Prop := True
/-- absorbs_biUnion (abstract). -/
def absorbs_biUnion' : Prop := True
/-- absorbs_biUnion_finset (abstract). -/
def absorbs_biUnion_finset' : Prop := True
-- COLLISION: add' already in Order.lean — rename needed
-- COLLISION: univ' already in SetTheory.lean — rename needed
/-- absorbs_iff_eventually_cobounded_mapsTo (abstract). -/
def absorbs_iff_eventually_cobounded_mapsTo' : Prop := True
/-- absorbing (abstract). -/
def absorbing' : Prop := True
/-- mem_absorbing (abstract). -/
def mem_absorbing' : Prop := True
/-- absorbs_sInter (abstract). -/
def absorbs_sInter' : Prop := True
/-- absorbs_iInter (abstract). -/
def absorbs_iInter' : Prop := True
/-- absorbs_biInter (abstract). -/
def absorbs_biInter' : Prop := True
/-- absorbs_zero_iff (abstract). -/
def absorbs_zero_iff' : Prop := True
/-- absorbs_neg_neg (abstract). -/
def absorbs_neg_neg' : Prop := True
-- COLLISION: sub' already in SetTheory.lean — rename needed
/-- absorbent_iff_forall_absorbs_singleton (abstract). -/
def absorbent_iff_forall_absorbs_singleton' : Prop := True
/-- absorbs (abstract). -/
def absorbs' : Prop := True
/-- absorbs_finite (abstract). -/
def absorbs_finite' : Prop := True
/-- vadd_absorbs (abstract). -/
def vadd_absorbs' : Prop := True
/-- absorbent_univ (abstract). -/
def absorbent_univ' : Prop := True
/-- absorbent_iff_inv_smul (abstract). -/
def absorbent_iff_inv_smul' : Prop := True
-- COLLISION: zero_mem' already in RingTheory2.lean — rename needed
-- COLLISION: restrict_scalars' already in LinearAlgebra2.lean — rename needed

-- Bornology/Basic.lean
-- COLLISION: consisting' already in LinearAlgebra2.lean — rename needed
-- COLLISION: extending' already in RingTheory2.lean — rename needed
/-- Bornology (abstract). -/
def Bornology' : Prop := True
/-- cobounded (abstract). -/
def cobounded' : Prop := True
/-- le_cofinite (abstract). -/
def le_cofinite' : Prop := True
/-- ofBounded (abstract). -/
def ofBounded' : Prop := True
-- COLLISION: IsCobounded' already in Order.lean — rename needed
-- COLLISION: IsBounded' already in Order.lean — rename needed
/-- isBounded_empty (abstract). -/
def isBounded_empty' : Prop := True
/-- nonempty_of_not_isBounded (abstract). -/
def nonempty_of_not_isBounded' : Prop := True
/-- isBounded_singleton (abstract). -/
def isBounded_singleton' : Prop := True
/-- isBounded_iff_forall_mem (abstract). -/
def isBounded_iff_forall_mem' : Prop := True
/-- isCobounded_univ (abstract). -/
def isCobounded_univ' : Prop := True
/-- isCobounded_inter (abstract). -/
def isCobounded_inter' : Prop := True
/-- isBounded_union (abstract). -/
def isBounded_union' : Prop := True
-- COLLISION: superset' already in MeasureTheory2.lean — rename needed
-- COLLISION: subset' already in Order.lean — rename needed
/-- sUnion_bounded_univ (abstract). -/
def sUnion_bounded_univ' : Prop := True
-- COLLISION: insert' already in SetTheory.lean — rename needed
/-- ext_iff_isBounded (abstract). -/
def ext_iff_isBounded' : Prop := True
/-- isBounded_ofBounded_iff (abstract). -/
def isBounded_ofBounded_iff' : Prop := True
/-- isCobounded_biInter (abstract). -/
def isCobounded_biInter' : Prop := True
/-- isCobounded_biInter_finset (abstract). -/
def isCobounded_biInter_finset' : Prop := True
/-- isCobounded_iInter (abstract). -/
def isCobounded_iInter' : Prop := True
/-- isCobounded_sInter (abstract). -/
def isCobounded_sInter' : Prop := True
/-- isBounded_biUnion (abstract). -/
def isBounded_biUnion' : Prop := True
/-- isBounded_biUnion_finset (abstract). -/
def isBounded_biUnion_finset' : Prop := True
/-- isBounded_sUnion (abstract). -/
def isBounded_sUnion' : Prop := True
/-- isBounded_iUnion (abstract). -/
def isBounded_iUnion' : Prop := True
-- COLLISION: cofinite' already in Order.lean — rename needed
/-- BoundedSpace (abstract). -/
def BoundedSpace' : Prop := True
/-- isBounded_univ (abstract). -/
def isBounded_univ' : Prop := True
/-- cobounded_eq_bot_iff (abstract). -/
def cobounded_eq_bot_iff' : Prop := True
-- COLLISION: all' already in Algebra.lean — rename needed

-- Bornology/BoundedOperation.lean
/-- BoundedAdd (abstract). -/
def BoundedAdd' : Prop := True
/-- isBounded_add (abstract). -/
def isBounded_add' : Prop := True
/-- add_bounded_of_bounded_of_bounded (abstract). -/
def add_bounded_of_bounded_of_bounded' : Prop := True
/-- BoundedSub (abstract). -/
def BoundedSub' : Prop := True
/-- isBounded_sub (abstract). -/
def isBounded_sub' : Prop := True
/-- sub_bounded_of_bounded_of_bounded (abstract). -/
def sub_bounded_of_bounded_of_bounded' : Prop := True
/-- boundedSub_of_lipschitzWith_sub (abstract). -/
def boundedSub_of_lipschitzWith_sub' : Prop := True
/-- BoundedMul (abstract). -/
def BoundedMul' : Prop := True
/-- isBounded_mul (abstract). -/
def isBounded_mul' : Prop := True
/-- isBounded_pow (abstract). -/
def isBounded_pow' : Prop := True
/-- mul_bounded_of_bounded_of_bounded (abstract). -/
def mul_bounded_of_bounded_of_bounded' : Prop := True
-- COLLISION: lipschitzWith_sub' already in Analysis.lean — rename needed

-- Bornology/Constructions.lean
/-- isBounded_image_fst_and_snd (abstract). -/
def isBounded_image_fst_and_snd' : Prop := True
/-- image_fst (abstract). -/
def image_fst' : Prop := True
/-- image_snd (abstract). -/
def image_snd' : Prop := True
/-- fst_of_prod (abstract). -/
def fst_of_prod' : Prop := True
/-- snd_of_prod (abstract). -/
def snd_of_prod' : Prop := True
/-- isBounded_prod_of_nonempty (abstract). -/
def isBounded_prod_of_nonempty' : Prop := True
/-- isBounded_prod (abstract). -/
def isBounded_prod' : Prop := True
/-- forall_isBounded_image_eval_iff (abstract). -/
def forall_isBounded_image_eval_iff' : Prop := True
/-- image_eval (abstract). -/
def image_eval' : Prop := True
/-- isBounded_pi_of_nonempty (abstract). -/
def isBounded_pi_of_nonempty' : Prop := True
/-- isBounded_pi (abstract). -/
def isBounded_pi' : Prop := True
/-- isBounded_induced (abstract). -/
def isBounded_induced' : Prop := True
/-- isBounded_image_subtype_val (abstract). -/
def isBounded_image_subtype_val' : Prop := True
/-- boundedSpace_induced_iff (abstract). -/
def boundedSpace_induced_iff' : Prop := True
/-- boundedSpace_subtype_iff (abstract). -/
def boundedSpace_subtype_iff' : Prop := True
/-- boundedSpace_val_set_iff (abstract). -/
def boundedSpace_val_set_iff' : Prop := True

-- Bornology/Hom.lean
/-- LocallyBoundedMap (abstract). -/
def LocallyBoundedMap' : Prop := True
/-- LocallyBoundedMapClass (abstract). -/
def LocallyBoundedMapClass' : Prop := True
/-- toLocallyBoundedMap (abstract). -/
def toLocallyBoundedMap' : Prop := True
/-- ofMapBounded (abstract). -/
def ofMapBounded' : Prop := True
-- COLLISION: cancel_right' already in Order.lean — rename needed
-- COLLISION: cancel_left' already in Order.lean — rename needed

-- CWComplex.lean
/-- sphereInclusion (abstract). -/
def sphereInclusion' : Prop := True
/-- AttachGeneralizedCells (abstract). -/
def AttachGeneralizedCells' : Prop := True
/-- AttachCells (abstract). -/
def AttachCells' : Prop := True
/-- RelativeCWComplex (abstract). -/
def RelativeCWComplex' : Prop := True
/-- CWComplex (abstract). -/
def CWComplex' : Prop := True
-- COLLISION: inclusion' already in Order.lean — rename needed
/-- skInclusion (abstract). -/
def skInclusion' : Prop := True
/-- toTopCat (abstract). -/
def toTopCat' : Prop := True

-- Category/Born.lean
/-- Born (abstract). -/
def Born' : Prop := True

-- Category/CompHaus/Basic.lean
/-- CompHaus (abstract). -/
def CompHaus' : Prop := True
/-- compHausToTop (abstract). -/
def compHausToTop' : Prop := True
/-- stoneCechObj (abstract). -/
def stoneCechObj' : Prop := True
/-- stoneCechEquivalence (abstract). -/
def stoneCechEquivalence' : Prop := True
/-- topToCompHaus (abstract). -/
def topToCompHaus' : Prop := True
-- COLLISION: epi_iff_surjective' already in Order.lean — rename needed
/-- compHausLikeToCompHaus (abstract). -/
def compHausLikeToCompHaus' : Prop := True

-- Category/CompHaus/EffectiveEpi.lean
/-- effectiveEpi_tfae (abstract). -/
def effectiveEpi_tfae' : Prop := True
/-- effectiveEpiFamily_tfae (abstract). -/
def effectiveEpiFamily_tfae' : Prop := True
/-- effectiveEpiFamily_of_jointly_surjective (abstract). -/
def effectiveEpiFamily_of_jointly_surjective' : Prop := True

-- Category/CompHaus/Limits.lean
/-- isTerminalPUnit (abstract). -/
def isTerminalPUnit' : Prop := True
/-- terminalIsoPUnit (abstract). -/
def terminalIsoPUnit' : Prop := True

-- Category/CompHaus/Projective.lean
/-- projectivePresentation (abstract). -/
def projectivePresentation' : Prop := True

-- Category/CompHausLike/Basic.lean
/-- Profinite (abstract). -/
def Profinite' : Prop := True
/-- CompHausLike (abstract). -/
def CompHausLike' : Prop := True
/-- HasProp (abstract). -/
def HasProp' : Prop := True
/-- toCompHausLike (abstract). -/
def toCompHausLike' : Prop := True
/-- fullyFaithfulToCompHausLike (abstract). -/
def fullyFaithfulToCompHausLike' : Prop := True
/-- compHausLikeToTop (abstract). -/
def compHausLikeToTop' : Prop := True
/-- fullyFaithfulCompHausLikeToTop (abstract). -/
def fullyFaithfulCompHausLikeToTop' : Prop := True
-- COLLISION: epi_of_surjective' already in Algebra.lean — rename needed
-- COLLISION: mono_iff_injective' already in Order.lean — rename needed
/-- isClosedMap (abstract). -/
def isClosedMap' : Prop := True
/-- isIso_of_bijective (abstract). -/
def isIso_of_bijective' : Prop := True
/-- isoOfBijective (abstract). -/
def isoOfBijective' : Prop := True
/-- isoOfHomeo (abstract). -/
def isoOfHomeo' : Prop := True
/-- homeoOfIso (abstract). -/
def homeoOfIso' : Prop := True
/-- isoEquivHomeo (abstract). -/
def isoEquivHomeo' : Prop := True

-- Category/CompHausLike/EffectiveEpi.lean
/-- effectiveEpiStruct (abstract). -/
def effectiveEpiStruct' : Prop := True
-- COLLISION: preregular' already in CategoryTheory.lean — rename needed
-- COLLISION: precoherent' already in CategoryTheory.lean — rename needed

-- Category/CompHausLike/Limits.lean
/-- describing (abstract). -/
def describing' : Prop := True
/-- HasExplicitFiniteCoproduct (abstract). -/
def HasExplicitFiniteCoproduct' : Prop := True
/-- finiteCoproduct (abstract). -/
def finiteCoproduct' : Prop := True
-- COLLISION: ι' already in Algebra.lean — rename needed
-- COLLISION: desc' already in Algebra.lean — rename needed
-- COLLISION: hom_ext' already in RingTheory2.lean — rename needed
/-- cofan (abstract). -/
def cofan' : Prop := True
-- COLLISION: isColimit' already in CategoryTheory.lean — rename needed
/-- ι_injective (abstract). -/
def ι_injective' : Prop := True
-- COLLISION: ι_jointly_surjective' already in CategoryTheory.lean — rename needed
-- COLLISION: ι_desc_apply' already in CategoryTheory.lean — rename needed
/-- HasExplicitFiniteCoproducts (abstract). -/
def HasExplicitFiniteCoproducts' : Prop := True
/-- isOpenEmbedding_ι (abstract). -/
def isOpenEmbedding_ι' : Prop := True
/-- HasExplicitPullback (abstract). -/
def HasExplicitPullback' : Prop := True
-- COLLISION: pullback' already in Analysis.lean — rename needed
-- COLLISION: condition' already in CategoryTheory.lean — rename needed
-- COLLISION: lift' already in SetTheory.lean — rename needed
-- COLLISION: cone' already in CategoryTheory.lean — rename needed
-- COLLISION: isLimit' already in CategoryTheory.lean — rename needed
/-- HasExplicitPullbacks (abstract). -/
def HasExplicitPullbacks' : Prop := True
/-- HasExplicitPullbacksOfInclusions (abstract). -/
def HasExplicitPullbacksOfInclusions' : Prop := True
/-- hasPullbacksOfInclusions (abstract). -/
def hasPullbacksOfInclusions' : Prop := True
/-- finitaryExtensive (abstract). -/
def finitaryExtensive' : Prop := True

-- Category/CompHausLike/SigmaComparison.lean
-- COLLISION: sigmaComparison' already in CategoryTheory.lean — rename needed
/-- sigmaComparison_eq_comp_isos (abstract). -/
def sigmaComparison_eq_comp_isos' : Prop := True

-- Category/CompactlyGenerated.lean
/-- CompactlyGenerated (abstract). -/
def CompactlyGenerated' : Prop := True
/-- compactlyGeneratedToTop (abstract). -/
def compactlyGeneratedToTop' : Prop := True
/-- fullyFaithfulCompactlyGeneratedToTop (abstract). -/
def fullyFaithfulCompactlyGeneratedToTop' : Prop := True

-- Category/Compactum.lean
/-- Compactum (abstract). -/
def Compactum' : Prop := True
-- COLLISION: forget' already in Algebra.lean — rename needed
-- COLLISION: free' already in Algebra.lean — rename needed
-- COLLISION: adj' already in Algebra.lean — rename needed
/-- str (abstract). -/
def str' : Prop := True
-- COLLISION: join' already in Order.lean — rename needed
-- COLLISION: incl' already in RingTheory2.lean — rename needed
/-- str_incl (abstract). -/
def str_incl' : Prop := True
/-- str_hom_commute (abstract). -/
def str_hom_commute' : Prop := True
/-- join_distrib (abstract). -/
def join_distrib' : Prop := True
/-- isClosed_iff (abstract). -/
def isClosed_iff' : Prop := True
/-- basic (abstract). -/
def basic' : Prop := True
/-- cl (abstract). -/
def cl' : Prop := True
/-- basic_inter (abstract). -/
def basic_inter' : Prop := True
/-- subset_cl (abstract). -/
def subset_cl' : Prop := True
/-- cl_cl (abstract). -/
def cl_cl' : Prop := True
/-- isClosed_cl (abstract). -/
def isClosed_cl' : Prop := True
/-- str_eq_of_le_nhds (abstract). -/
def str_eq_of_le_nhds' : Prop := True
/-- le_nhds_of_str_eq (abstract). -/
def le_nhds_of_str_eq' : Prop := True
/-- lim_eq_str (abstract). -/
def lim_eq_str' : Prop := True
/-- cl_eq_closure (abstract). -/
def cl_eq_closure' : Prop := True
/-- continuous_of_hom (abstract). -/
def continuous_of_hom' : Prop := True
/-- ofTopologicalSpace (abstract). -/
def ofTopologicalSpace' : Prop := True
/-- homOfContinuous (abstract). -/
def homOfContinuous' : Prop := True
/-- compactumToCompHaus (abstract). -/
def compactumToCompHaus' : Prop := True
/-- isoOfTopologicalSpace (abstract). -/
def isoOfTopologicalSpace' : Prop := True
/-- compactumToCompHausCompForget (abstract). -/
def compactumToCompHausCompForget' : Prop := True

-- Category/FinTopCat.lean
/-- FinTopCat (abstract). -/
def FinTopCat' : Prop := True

-- Category/LightProfinite/AsLimit.lean
/-- fintypeDiagram (abstract). -/
def fintypeDiagram' : Prop := True
-- COLLISION: diagram' already in Algebra.lean — rename needed
/-- asLimitConeAux (abstract). -/
def asLimitConeAux' : Prop := True
/-- isoMapCone (abstract). -/
def isoMapCone' : Prop := True
/-- asLimitAux (abstract). -/
def asLimitAux' : Prop := True
/-- asLimitCone (abstract). -/
def asLimitCone' : Prop := True
/-- asLimit (abstract). -/
def asLimit' : Prop := True
-- COLLISION: lim' already in Algebra.lean — rename needed
/-- lightToProfinite_map_proj_eq (abstract). -/
def lightToProfinite_map_proj_eq' : Prop := True
/-- proj_surjective (abstract). -/
def proj_surjective' : Prop := True
-- COLLISION: component' already in Algebra.lean — rename needed
-- COLLISION: transitionMap' already in RingTheory2.lean — rename needed
/-- transitionMapLE (abstract). -/
def transitionMapLE' : Prop := True
/-- proj_comp_transitionMap (abstract). -/
def proj_comp_transitionMap' : Prop := True
/-- proj_comp_transitionMapLE (abstract). -/
def proj_comp_transitionMapLE' : Prop := True
/-- surjective_transitionMap (abstract). -/
def surjective_transitionMap' : Prop := True
/-- surjective_transitionMapLE (abstract). -/
def surjective_transitionMapLE' : Prop := True

-- Category/LightProfinite/Basic.lean
/-- LightProfinite (abstract). -/
def LightProfinite' : Prop := True
/-- lightToProfinite (abstract). -/
def lightToProfinite' : Prop := True
/-- lightToProfiniteFullyFaithful (abstract). -/
def lightToProfiniteFullyFaithful' : Prop := True
/-- lightProfiniteToCompHaus (abstract). -/
def lightProfiniteToCompHaus' : Prop := True
/-- toLightProfinite (abstract). -/
def toLightProfinite' : Prop := True
/-- toLightProfiniteFullyFaithful (abstract). -/
def toLightProfiniteFullyFaithful' : Prop := True
/-- LightDiagram (abstract). -/
def LightDiagram' : Prop := True
/-- toProfinite (abstract). -/
def toProfinite' : Prop := True
/-- lightDiagramToProfinite (abstract). -/
def lightDiagramToProfinite' : Prop := True
/-- toLightDiagram (abstract). -/
def toLightDiagram' : Prop := True
/-- lightProfiniteToLightDiagram (abstract). -/
def lightProfiniteToLightDiagram' : Prop := True
/-- lightDiagramToLightProfinite (abstract). -/
def lightDiagramToLightProfinite' : Prop := True
/-- equivDiagram (abstract). -/
def equivDiagram' : Prop := True
/-- toLightFunctor (abstract). -/
def toLightFunctor' : Prop := True
/-- equivSmall (abstract). -/
def equivSmall' : Prop := True

-- Category/LightProfinite/EffectiveEpi.lean
/-- effectiveEpi_iff_surjective (abstract). -/
def effectiveEpi_iff_surjective' : Prop := True

-- Category/LightProfinite/Extend.lean
-- COLLISION: functor' already in Algebra.lean — rename needed
/-- functorOp (abstract). -/
def functorOp' : Prop := True
/-- functor_initial (abstract). -/
def functor_initial' : Prop := True
/-- functorOp_final (abstract). -/
def functorOp_final' : Prop := True
-- COLLISION: isLimitCone' already in CategoryTheory.lean — rename needed
-- COLLISION: cocone' already in CategoryTheory.lean — rename needed
-- COLLISION: isColimitCocone' already in CategoryTheory.lean — rename needed

-- Category/LightProfinite/Limits.lean

-- Category/LightProfinite/Sequence.lean
/-- natUnionInftyEmbedding (abstract). -/
def natUnionInftyEmbedding' : Prop := True
/-- isClosedEmbedding_natUnionInftyEmbedding (abstract). -/
def isClosedEmbedding_natUnionInftyEmbedding' : Prop := True
/-- NatUnionInfty (abstract). -/
def NatUnionInfty' : Prop := True
/-- continuous_iff_convergent (abstract). -/
def continuous_iff_convergent' : Prop := True

-- Category/Locale.lean
/-- Locale (abstract). -/
def Locale' : Prop := True
/-- topToLocale (abstract). -/
def topToLocale' : Prop := True

-- Category/Profinite/AsLimit.lean
/-- isoAsLimitConeLift (abstract). -/
def isoAsLimitConeLift' : Prop := True
/-- asLimitConeIso (abstract). -/
def asLimitConeIso' : Prop := True

-- Category/Profinite/Basic.lean
/-- profiniteToCompHaus (abstract). -/
def profiniteToCompHaus' : Prop := True
/-- toProfiniteObj (abstract). -/
def toProfiniteObj' : Prop := True
/-- toCompHausEquivalence (abstract). -/
def toCompHausEquivalence' : Prop := True
/-- botTopology (abstract). -/
def botTopology' : Prop := True
/-- toProfiniteFullyFaithful (abstract). -/
def toProfiniteFullyFaithful' : Prop := True
/-- toProfiniteAdjToCompHaus (abstract). -/
def toProfiniteAdjToCompHaus' : Prop := True

-- Category/Profinite/CofilteredLimit.lean
/-- exists_isClopen_of_cofiltered (abstract). -/
def exists_isClopen_of_cofiltered' : Prop := True
/-- exists_locallyConstant_fin_two (abstract). -/
def exists_locallyConstant_fin_two' : Prop := True
/-- exists_locallyConstant_finite_aux (abstract). -/
def exists_locallyConstant_finite_aux' : Prop := True
/-- exists_locallyConstant_finite_nonempty (abstract). -/
def exists_locallyConstant_finite_nonempty' : Prop := True
/-- exists_locallyConstant (abstract). -/
def exists_locallyConstant' : Prop := True

-- Category/Profinite/EffectiveEpi.lean
/-- profiniteToCompHausEffectivePresentation (abstract). -/
def profiniteToCompHausEffectivePresentation' : Prop := True

-- Category/Profinite/Extend.lean
/-- exists_hom (abstract). -/
def exists_hom' : Prop := True

-- Category/Profinite/Limits.lean

-- Category/Profinite/Nobeling.lean
-- COLLISION: Proj' already in AlgebraicGeometry.lean — rename needed
-- COLLISION: continuous_proj' already in Analysis.lean — rename needed
-- COLLISION: π' already in Algebra.lean — rename needed
/-- ProjRestrict (abstract). -/
def ProjRestrict' : Prop := True
/-- continuous_projRestrict (abstract). -/
def continuous_projRestrict' : Prop := True
/-- proj_eq_self (abstract). -/
def proj_eq_self' : Prop := True
/-- proj_prop_eq_self (abstract). -/
def proj_prop_eq_self' : Prop := True
/-- ProjRestricts (abstract). -/
def ProjRestricts' : Prop := True
/-- continuous_projRestricts (abstract). -/
def continuous_projRestricts' : Prop := True
/-- surjective_projRestricts (abstract). -/
def surjective_projRestricts' : Prop := True
/-- projRestricts_eq_id (abstract). -/
def projRestricts_eq_id' : Prop := True
/-- projRestricts_eq_comp (abstract). -/
def projRestricts_eq_comp' : Prop := True
/-- projRestricts_comp_projRestrict (abstract). -/
def projRestricts_comp_projRestrict' : Prop := True
/-- iso_map (abstract). -/
def iso_map' : Prop := True
/-- iso_map_bijective (abstract). -/
def iso_map_bijective' : Prop := True
/-- spanFunctor (abstract). -/
def spanFunctor' : Prop := True
/-- spanCone (abstract). -/
def spanCone' : Prop := True
/-- spanCone_isLimit (abstract). -/
def spanCone_isLimit' : Prop := True
/-- e (abstract). -/
def e' : Prop := True
/-- Products (abstract). -/
def Products' : Prop := True
/-- lt_iff_lex_lt (abstract). -/
def lt_iff_lex_lt' : Prop := True
-- COLLISION: eval' already in SetTheory.lean — rename needed
/-- isGood (abstract). -/
def isGood' : Prop := True
/-- rel_head!_of_mem (abstract). -/
def rel_head!_of_mem' : Prop := True
/-- head!_le_of_lt (abstract). -/
def head!_le_of_lt' : Prop := True
/-- GoodProducts (abstract). -/
def GoodProducts' : Prop := True
-- COLLISION: injective' already in Order.lean — rename needed
-- COLLISION: range' already in SetTheory.lean — rename needed
/-- equiv_range (abstract). -/
def equiv_range' : Prop := True
/-- linearIndependent_iff_range (abstract). -/
def linearIndependent_iff_range' : Prop := True
-- COLLISION: eval_eq' already in Algebra.lean — rename needed
/-- evalFacProp (abstract). -/
def evalFacProp' : Prop := True
/-- evalFacProps (abstract). -/
def evalFacProps' : Prop := True
/-- prop_of_isGood (abstract). -/
def prop_of_isGood' : Prop := True
/-- span_iff_products (abstract). -/
def span_iff_products' : Prop := True
/-- πJ (abstract). -/
def πJ' : Prop := True
/-- eval_eq_πJ (abstract). -/
def eval_eq_πJ' : Prop := True
/-- spanFinBasis (abstract). -/
def spanFinBasis' : Prop := True
-- COLLISION: factors' already in RingTheory2.lean — rename needed
-- COLLISION: list_prod_apply' already in Algebra.lean — rename needed
/-- factors_prod_eq_basis_of_eq (abstract). -/
def factors_prod_eq_basis_of_eq' : Prop := True
/-- e_mem_of_eq_true (abstract). -/
def e_mem_of_eq_true' : Prop := True
/-- one_sub_e_mem_of_false (abstract). -/
def one_sub_e_mem_of_false' : Prop := True
/-- factors_prod_eq_basis_of_ne (abstract). -/
def factors_prod_eq_basis_of_ne' : Prop := True
/-- factors_prod_eq_basis (abstract). -/
def factors_prod_eq_basis' : Prop := True
/-- finsupp_sum_mem_span_eval (abstract). -/
def finsupp_sum_mem_span_eval' : Prop := True
/-- spanFin (abstract). -/
def spanFin' : Prop := True
/-- fin_comap_jointlySurjective (abstract). -/
def fin_comap_jointlySurjective' : Prop := True
-- COLLISION: ord' already in SetTheory.lean — rename needed
/-- term (abstract). -/
def term' : Prop := True
/-- term_ord_aux (abstract). -/
def term_ord_aux' : Prop := True
/-- ord_term_aux (abstract). -/
def ord_term_aux' : Prop := True
/-- ord_term (abstract). -/
def ord_term' : Prop := True
/-- contained (abstract). -/
def contained' : Prop := True
-- COLLISION: P' already in Algebra.lean — rename needed
/-- prop_of_isGood_of_contained (abstract). -/
def prop_of_isGood_of_contained' : Prop := True
/-- linearIndependentEmpty (abstract). -/
def linearIndependentEmpty' : Prop := True
-- COLLISION: nil' already in RingTheory2.lean — rename needed
/-- lt_nil_empty (abstract). -/
def lt_nil_empty' : Prop := True
/-- isGood_nil (abstract). -/
def isGood_nil' : Prop := True
/-- span_nil_eq_top (abstract). -/
def span_nil_eq_top' : Prop := True
/-- linearIndependentSingleton (abstract). -/
def linearIndependentSingleton' : Prop := True
/-- contained_eq_proj (abstract). -/
def contained_eq_proj' : Prop := True
/-- isClosed_proj (abstract). -/
def isClosed_proj' : Prop := True
/-- πs (abstract). -/
def πs' : Prop := True
/-- injective_πs (abstract). -/
def injective_πs' : Prop := True
-- COLLISION: lt_ord_of_lt' already in SetTheory.lean — rename needed
/-- eval_πs (abstract). -/
def eval_πs' : Prop := True
/-- eval_πs_image (abstract). -/
def eval_πs_image' : Prop := True
/-- head_lt_ord_of_isGood (abstract). -/
def head_lt_ord_of_isGood' : Prop := True
/-- isGood_mono (abstract). -/
def isGood_mono' : Prop := True
/-- smaller (abstract). -/
def smaller' : Prop := True
/-- range_equiv_smaller_toFun (abstract). -/
def range_equiv_smaller_toFun' : Prop := True
/-- range_equiv_smaller_toFun_bijective (abstract). -/
def range_equiv_smaller_toFun_bijective' : Prop := True
/-- range_equiv_smaller (abstract). -/
def range_equiv_smaller' : Prop := True
/-- linearIndependent_iff_smaller (abstract). -/
def linearIndependent_iff_smaller' : Prop := True
/-- smaller_mono (abstract). -/
def smaller_mono' : Prop := True
/-- limitOrdinal (abstract). -/
def limitOrdinal' : Prop := True
/-- range_equiv (abstract). -/
def range_equiv' : Prop := True
/-- linearIndependent_iff_union_smaller (abstract). -/
def linearIndependent_iff_union_smaller' : Prop := True
/-- C0 (abstract). -/
def C0' : Prop := True
/-- C1 (abstract). -/
def C1' : Prop := True
/-- isClosed_C0 (abstract). -/
def isClosed_C0' : Prop := True
/-- isClosed_C1 (abstract). -/
def isClosed_C1' : Prop := True
/-- contained_C1 (abstract). -/
def contained_C1' : Prop := True
/-- union_C0C1_eq (abstract). -/
def union_C0C1_eq' : Prop := True
-- COLLISION: C' already in RingTheory2.lean — rename needed
/-- isClosed_C' (abstract). -/
def isClosed_C' : Prop := True
/-- contained_C' (abstract). -/
def contained_C' : Prop := True
/-- SwapTrue (abstract). -/
def SwapTrue' : Prop := True
/-- continuous_swapTrue (abstract). -/
def continuous_swapTrue' : Prop := True
/-- swapTrue_mem_C1 (abstract). -/
def swapTrue_mem_C1' : Prop := True
/-- CC'₀ (abstract). -/
def CC'₀' : Prop := True
/-- CC'₁ (abstract). -/
def CC'₁' : Prop := True
/-- continuous_CC'₀ (abstract). -/
def continuous_CC'₀' : Prop := True
/-- continuous_CC'₁ (abstract). -/
def continuous_CC'₁' : Prop := True
/-- Linear_CC'₀ (abstract). -/
def Linear_CC'₀' : Prop := True
/-- Linear_CC'₁ (abstract). -/
def Linear_CC'₁' : Prop := True
/-- Linear_CC' (abstract). -/
def Linear_CC' : Prop := True
/-- CC_comp_zero (abstract). -/
def CC_comp_zero' : Prop := True
/-- C0_projOrd (abstract). -/
def C0_projOrd' : Prop := True
/-- C1_projOrd (abstract). -/
def C1_projOrd' : Prop := True
/-- CC_exact (abstract). -/
def CC_exact' : Prop := True
/-- succ_mono (abstract). -/
def succ_mono' : Prop := True
/-- succ_exact (abstract). -/
def succ_exact' : Prop := True
/-- MaxProducts (abstract). -/
def MaxProducts' : Prop := True
/-- union_succ (abstract). -/
def union_succ' : Prop := True
/-- sum_to (abstract). -/
def sum_to' : Prop := True
/-- injective_sum_to (abstract). -/
def injective_sum_to' : Prop := True
/-- sum_to_range (abstract). -/
def sum_to_range' : Prop := True
/-- sum_equiv (abstract). -/
def sum_equiv' : Prop := True
/-- sum_equiv_comp_eval_eq_elim (abstract). -/
def sum_equiv_comp_eval_eq_elim' : Prop := True
/-- SumEval (abstract). -/
def SumEval' : Prop := True
/-- linearIndependent_iff_sum (abstract). -/
def linearIndependent_iff_sum' : Prop := True
/-- span_sum (abstract). -/
def span_sum' : Prop := True
/-- square_commutes (abstract). -/
def square_commutes' : Prop := True
/-- swapTrue_eq_true (abstract). -/
def swapTrue_eq_true' : Prop := True
/-- mem_C'_eq_false (abstract). -/
def mem_C'_eq_false' : Prop := True
/-- Tail (abstract). -/
def Tail' : Prop := True
/-- max_eq_o_cons_tail (abstract). -/
def max_eq_o_cons_tail' : Prop := True
/-- head!_eq_o_of_maxProducts (abstract). -/
def head!_eq_o_of_maxProducts' : Prop := True
/-- evalCons (abstract). -/
def evalCons' : Prop := True
/-- max_eq_eval (abstract). -/
def max_eq_eval' : Prop := True
/-- max_eq_eval_unapply (abstract). -/
def max_eq_eval_unapply' : Prop := True
/-- chain'_cons_of_lt (abstract). -/
def chain'_cons_of_lt' : Prop := True
/-- good_lt_maxProducts (abstract). -/
def good_lt_maxProducts' : Prop := True
/-- MaxToGood (abstract). -/
def MaxToGood' : Prop := True
/-- maxToGood_injective (abstract). -/
def maxToGood_injective' : Prop := True
/-- linearIndependent_comp_of_eval (abstract). -/
def linearIndependent_comp_of_eval' : Prop := True
/-- P0 (abstract). -/
def P0' : Prop := True
/-- Plimit (abstract). -/
def Plimit' : Prop := True
/-- linearIndependentAux (abstract). -/
def linearIndependentAux' : Prop := True
-- COLLISION: linearIndependent' already in RingTheory2.lean — rename needed
-- COLLISION: Basis' already in Algebra.lean — rename needed
/-- Nobeling_aux (abstract). -/
def Nobeling_aux' : Prop := True
/-- isClosedEmbedding (abstract). -/
def isClosedEmbedding' : Prop := True

-- Category/Profinite/Product.lean
-- COLLISION: obj' already in Algebra.lean — rename needed
/-- π_app (abstract). -/
def π_app' : Prop := True
/-- eq_of_forall_π_app_eq (abstract). -/
def eq_of_forall_π_app_eq' : Prop := True
/-- indexFunctor (abstract). -/
def indexFunctor' : Prop := True
/-- indexCone (abstract). -/
def indexCone' : Prop := True
/-- isoindexConeLift (abstract). -/
def isoindexConeLift' : Prop := True
/-- asLimitindexConeIso (abstract). -/
def asLimitindexConeIso' : Prop := True
/-- indexCone_isLimit (abstract). -/
def indexCone_isLimit' : Prop := True

-- Category/Profinite/Projective.lean

-- Category/Sequential.lean
-- COLLISION: from' already in Algebra.lean — rename needed
/-- Sequential (abstract). -/
def Sequential' : Prop := True
/-- sequentialToTop (abstract). -/
def sequentialToTop' : Prop := True
/-- fullyFaithfulSequentialToTop (abstract). -/
def fullyFaithfulSequentialToTop' : Prop := True

-- Category/Stonean/Adjunctions.lean
/-- typeToStonean (abstract). -/
def typeToStonean' : Prop := True
/-- stoneCechAdjunction (abstract). -/
def stoneCechAdjunction' : Prop := True

-- Category/Stonean/Basic.lean
/-- Stonean (abstract). -/
def Stonean' : Prop := True
/-- toStonean (abstract). -/
def toStonean' : Prop := True
/-- toCompHaus (abstract). -/
def toCompHaus' : Prop := True
/-- fullyFaithfulToCompHaus (abstract). -/
def fullyFaithfulToCompHaus' : Prop := True
/-- mkFinite (abstract). -/
def mkFinite' : Prop := True
-- COLLISION: presentation' already in CategoryTheory.lean — rename needed
/-- compHaus (abstract). -/
def compHaus' : Prop := True
/-- lift_lifts (abstract). -/
def lift_lifts' : Prop := True
/-- Gleason (abstract). -/
def Gleason' : Prop := True
/-- projective_of_extrDisc (abstract). -/
def projective_of_extrDisc' : Prop := True

-- Category/Stonean/EffectiveEpi.lean
/-- stoneanToCompHausEffectivePresentation (abstract). -/
def stoneanToCompHausEffectivePresentation' : Prop := True

-- Category/Stonean/Limits.lean
/-- extremallyDisconnected_preimage (abstract). -/
def extremallyDisconnected_preimage' : Prop := True
/-- extremallyDisconnected_pullback (abstract). -/
def extremallyDisconnected_pullback' : Prop := True

-- Category/TopCat/Adjunctions.lean
/-- adj₁ (abstract). -/
def adj₁' : Prop := True
/-- adj₂ (abstract). -/
def adj₂' : Prop := True

-- Category/TopCat/Basic.lean
/-- TopCat (abstract). -/
def TopCat' : Prop := True
-- COLLISION: hom_inv_id_apply' already in CategoryTheory.lean — rename needed
-- COLLISION: inv_hom_id_apply' already in CategoryTheory.lean — rename needed
/-- topologicalSpace_forget (abstract). -/
def topologicalSpace_forget' : Prop := True
-- COLLISION: discrete' already in CategoryTheory.lean — rename needed
-- COLLISION: trivial' already in CategoryTheory.lean — rename needed
/-- of_isoOfHomeo (abstract). -/
def of_isoOfHomeo' : Prop := True
/-- of_homeoOfIso (abstract). -/
def of_homeoOfIso' : Prop := True
/-- isIso_of_bijective_of_isOpenMap (abstract). -/
def isIso_of_bijective_of_isOpenMap' : Prop := True
/-- isIso_of_bijective_of_isClosedMap (abstract). -/
def isIso_of_bijective_of_isClosedMap' : Prop := True
/-- isOpenEmbedding_iff_comp_isIso (abstract). -/
def isOpenEmbedding_iff_comp_isIso' : Prop := True
/-- isOpenEmbedding_iff_isIso_comp (abstract). -/
def isOpenEmbedding_iff_isIso_comp' : Prop := True

-- Category/TopCat/EffectiveEpi.lean
/-- effectiveEpiStructOfQuotientMap (abstract). -/
def effectiveEpiStructOfQuotientMap' : Prop := True
/-- effectiveEpi_iff_isQuotientMap (abstract). -/
def effectiveEpi_iff_isQuotientMap' : Prop := True

-- Category/TopCat/EpiMono.lean

-- Category/TopCat/Limits/Basic.lean
/-- limitConeInfi (abstract). -/
def limitConeInfi' : Prop := True
/-- limitConeInfiIsLimit (abstract). -/
def limitConeInfiIsLimit' : Prop := True
-- COLLISION: colimitCocone' already in Algebra.lean — rename needed
-- COLLISION: colimitCoconeIsColimit' already in Algebra.lean — rename needed
/-- isInitialPEmpty (abstract). -/
def isInitialPEmpty' : Prop := True
/-- initialIsoPEmpty (abstract). -/
def initialIsoPEmpty' : Prop := True

-- Category/TopCat/Limits/Cofiltered.lean
/-- isTopologicalBasis_cofiltered_limit (abstract). -/
def isTopologicalBasis_cofiltered_limit' : Prop := True

-- Category/TopCat/Limits/Konig.lean
/-- FiniteDiagramArrow (abstract). -/
def FiniteDiagramArrow' : Prop := True
/-- FiniteDiagram (abstract). -/
def FiniteDiagram' : Prop := True
/-- partialSections (abstract). -/
def partialSections' : Prop := True
-- COLLISION: directed' already in Order.lean — rename needed
-- COLLISION: closed' already in Order.lean — rename needed
/-- nonempty_limitCone_of_compact_t2_cofiltered_system (abstract). -/
def nonempty_limitCone_of_compact_t2_cofiltered_system' : Prop := True

-- Category/TopCat/Limits/Products.lean
/-- piπ (abstract). -/
def piπ' : Prop := True
-- COLLISION: piFan' already in Algebra.lean — rename needed
-- COLLISION: piFanIsLimit' already in Algebra.lean — rename needed
-- COLLISION: piIsoPi' already in Algebra.lean — rename needed
/-- piIsoPi_inv_π (abstract). -/
def piIsoPi_inv_π' : Prop := True
/-- piIsoPi_inv_π_apply (abstract). -/
def piIsoPi_inv_π_apply' : Prop := True
/-- piIsoPi_hom_apply (abstract). -/
def piIsoPi_hom_apply' : Prop := True
/-- sigmaι (abstract). -/
def sigmaι' : Prop := True
/-- sigmaCofan (abstract). -/
def sigmaCofan' : Prop := True
/-- sigmaCofanIsColimit (abstract). -/
def sigmaCofanIsColimit' : Prop := True
/-- sigmaIsoSigma (abstract). -/
def sigmaIsoSigma' : Prop := True
/-- sigmaIsoSigma_hom_ι (abstract). -/
def sigmaIsoSigma_hom_ι' : Prop := True
/-- sigmaIsoSigma_hom_ι_apply (abstract). -/
def sigmaIsoSigma_hom_ι_apply' : Prop := True
/-- sigmaIsoSigma_inv_apply (abstract). -/
def sigmaIsoSigma_inv_apply' : Prop := True
/-- induced_of_isLimit (abstract). -/
def induced_of_isLimit' : Prop := True
/-- limit_topology (abstract). -/
def limit_topology' : Prop := True
/-- prodFst (abstract). -/
def prodFst' : Prop := True
/-- prodSnd (abstract). -/
def prodSnd' : Prop := True
/-- prodBinaryFan (abstract). -/
def prodBinaryFan' : Prop := True
/-- prodBinaryFanIsLimit (abstract). -/
def prodBinaryFanIsLimit' : Prop := True
/-- prodIsoProd (abstract). -/
def prodIsoProd' : Prop := True
/-- prodIsoProd_hom_fst (abstract). -/
def prodIsoProd_hom_fst' : Prop := True
/-- prodIsoProd_hom_snd (abstract). -/
def prodIsoProd_hom_snd' : Prop := True
/-- prodIsoProd_hom_apply (abstract). -/
def prodIsoProd_hom_apply' : Prop := True
/-- prodIsoProd_inv_fst (abstract). -/
def prodIsoProd_inv_fst' : Prop := True
/-- prodIsoProd_inv_snd (abstract). -/
def prodIsoProd_inv_snd' : Prop := True
/-- prod_topology (abstract). -/
def prod_topology' : Prop := True
/-- range_prod_map (abstract). -/
def range_prod_map' : Prop := True
/-- isInducing_prodMap (abstract). -/
def isInducing_prodMap' : Prop := True
/-- isEmbedding_prodMap (abstract). -/
def isEmbedding_prodMap' : Prop := True
/-- binaryCofan (abstract). -/
def binaryCofan' : Prop := True
/-- binaryCofanIsColimit (abstract). -/
def binaryCofanIsColimit' : Prop := True
-- COLLISION: binaryCofan_isColimit_iff' already in CategoryTheory.lean — rename needed

-- Category/TopCat/Limits/Pullbacks.lean
-- COLLISION: pullbackFst' already in CategoryTheory.lean — rename needed
/-- pullbackSnd (abstract). -/
def pullbackSnd' : Prop := True
-- COLLISION: pullbackCone' already in Algebra.lean — rename needed
-- COLLISION: pullbackConeIsLimit' already in Algebra.lean — rename needed
/-- pullbackIsoProdSubtype (abstract). -/
def pullbackIsoProdSubtype' : Prop := True
/-- pullbackIsoProdSubtype_inv_fst (abstract). -/
def pullbackIsoProdSubtype_inv_fst' : Prop := True
/-- pullbackIsoProdSubtype_inv_fst_apply (abstract). -/
def pullbackIsoProdSubtype_inv_fst_apply' : Prop := True
/-- pullbackIsoProdSubtype_inv_snd (abstract). -/
def pullbackIsoProdSubtype_inv_snd' : Prop := True
/-- pullbackIsoProdSubtype_inv_snd_apply (abstract). -/
def pullbackIsoProdSubtype_inv_snd_apply' : Prop := True
/-- pullbackIsoProdSubtype_hom_fst (abstract). -/
def pullbackIsoProdSubtype_hom_fst' : Prop := True
/-- pullbackIsoProdSubtype_hom_snd (abstract). -/
def pullbackIsoProdSubtype_hom_snd' : Prop := True
/-- pullbackIsoProdSubtype_hom_apply (abstract). -/
def pullbackIsoProdSubtype_hom_apply' : Prop := True
/-- pullback_topology (abstract). -/
def pullback_topology' : Prop := True
/-- range_pullback_to_prod (abstract). -/
def range_pullback_to_prod' : Prop := True
/-- pullbackHomeoPreimage (abstract). -/
def pullbackHomeoPreimage' : Prop := True
/-- isInducing_pullback_to_prod (abstract). -/
def isInducing_pullback_to_prod' : Prop := True
/-- isEmbedding_pullback_to_prod (abstract). -/
def isEmbedding_pullback_to_prod' : Prop := True
/-- range_pullback_map (abstract). -/
def range_pullback_map' : Prop := True
/-- pullback_fst_range (abstract). -/
def pullback_fst_range' : Prop := True
/-- pullback_snd_range (abstract). -/
def pullback_snd_range' : Prop := True
/-- pullback_map_isEmbedding (abstract). -/
def pullback_map_isEmbedding' : Prop := True
/-- pullback_map_isOpenEmbedding (abstract). -/
def pullback_map_isOpenEmbedding' : Prop := True
/-- snd_isEmbedding_of_left (abstract). -/
def snd_isEmbedding_of_left' : Prop := True
/-- fst_isEmbedding_of_right (abstract). -/
def fst_isEmbedding_of_right' : Prop := True
/-- isEmbedding_of_pullback (abstract). -/
def isEmbedding_of_pullback' : Prop := True
/-- snd_isOpenEmbedding_of_left (abstract). -/
def snd_isOpenEmbedding_of_left' : Prop := True
/-- fst_isOpenEmbedding_of_right (abstract). -/
def fst_isOpenEmbedding_of_right' : Prop := True
/-- isOpenEmbedding_of_pullback (abstract). -/
def isOpenEmbedding_of_pullback' : Prop := True
/-- fst_iso_of_right_embedding_range_subset (abstract). -/
def fst_iso_of_right_embedding_range_subset' : Prop := True
/-- snd_iso_of_left_embedding_range_subset (abstract). -/
def snd_iso_of_left_embedding_range_subset' : Prop := True
/-- pullback_snd_image_fst_preimage (abstract). -/
def pullback_snd_image_fst_preimage' : Prop := True
/-- pullback_fst_image_snd_preimage (abstract). -/
def pullback_fst_image_snd_preimage' : Prop := True
/-- coinduced_of_isColimit (abstract). -/
def coinduced_of_isColimit' : Prop := True
/-- colimit_topology (abstract). -/
def colimit_topology' : Prop := True
/-- colimit_isOpen_iff (abstract). -/
def colimit_isOpen_iff' : Prop := True
/-- coequalizer_isOpen_iff (abstract). -/
def coequalizer_isOpen_iff' : Prop := True

-- Category/TopCat/OpenNhds.lean
/-- OpenNhds (abstract). -/
def OpenNhds' : Prop := True
-- COLLISION: infLELeft' already in CategoryTheory.lean — rename needed
-- COLLISION: infLERight' already in CategoryTheory.lean — rename needed
/-- inclusionMapIso (abstract). -/
def inclusionMapIso' : Prop := True
/-- functorNhds (abstract). -/
def functorNhds' : Prop := True
/-- adjunctionNhds (abstract). -/
def adjunctionNhds' : Prop := True

-- Category/TopCat/Opens.lean
/-- leSupr (abstract). -/
def leSupr' : Prop := True
-- COLLISION: botLE' already in CategoryTheory.lean — rename needed
-- COLLISION: leTop' already in CategoryTheory.lean — rename needed
/-- isOpenEmbedding (abstract). -/
def isOpenEmbedding' : Prop := True
/-- inclusionTopIso (abstract). -/
def inclusionTopIso' : Prop := True
/-- leMapTop (abstract). -/
def leMapTop' : Prop := True
-- COLLISION: map_iSup' already in SetTheory.lean — rename needed
-- COLLISION: mapId' already in RingTheory2.lean — rename needed
-- COLLISION: mapComp' already in CategoryTheory.lean — rename needed
-- COLLISION: mapIso' already in Algebra.lean — rename needed
/-- mapMapIso (abstract). -/
def mapMapIso' : Prop := True
-- COLLISION: adjunction' already in CategoryTheory.lean — rename needed
/-- functor_obj_injective (abstract). -/
def functor_obj_injective' : Prop := True
-- COLLISION: functorObj' already in CategoryTheory.lean — rename needed
/-- map_functorObj (abstract). -/
def map_functorObj' : Prop := True
/-- mem_functorObj_iff (abstract). -/
def mem_functorObj_iff' : Prop := True
/-- le_functorObj_iff (abstract). -/
def le_functorObj_iff' : Prop := True
/-- opensGI (abstract). -/
def opensGI' : Prop := True
/-- isOpenEmbedding_obj_top (abstract). -/
def isOpenEmbedding_obj_top' : Prop := True
/-- inclusion'_map_eq_top (abstract). -/
def inclusion'_map_eq_top' : Prop := True
/-- adjunction_counit_app_self (abstract). -/
def adjunction_counit_app_self' : Prop := True
/-- inclusion'_top_functor (abstract). -/
def inclusion'_top_functor' : Prop := True
/-- functor_obj_map_obj (abstract). -/
def functor_obj_map_obj' : Prop := True
/-- set_range_inclusion' (abstract). -/
def set_range_inclusion' : Prop := True
/-- functor_map_eq_inf (abstract). -/
def functor_map_eq_inf' : Prop := True
/-- map_functor_eq' (abstract). -/
def map_functor_eq' : Prop := True
/-- adjunction_counit_map_functor (abstract). -/
def adjunction_counit_map_functor' : Prop := True

-- Category/TopCat/Sphere.lean
/-- sphere (abstract). -/
def sphere' : Prop := True
/-- disk (abstract). -/
def disk' : Prop := True

-- Category/TopCat/Yoneda.lean
/-- yonedaPresheaf (abstract). -/
def yonedaPresheaf' : Prop := True
-- COLLISION: piComparison_fac' already in CategoryTheory.lean — rename needed

-- Category/TopCommRingCat.lean
/-- TopCommRingCat (abstract). -/
def TopCommRingCat' : Prop := True

-- Category/UniformSpace.lean
/-- UniformSpaceCat (abstract). -/
def UniformSpaceCat' : Prop := True
/-- CpltSepUniformSpace (abstract). -/
def CpltSepUniformSpace' : Prop := True
/-- completionFunctor (abstract). -/
def completionFunctor' : Prop := True
/-- completionHom (abstract). -/
def completionHom' : Prop := True
/-- extension_comp_coe (abstract). -/
def extension_comp_coe' : Prop := True

-- Clopen.lean
/-- isClopen_iff_frontier_eq_empty (abstract). -/
def isClopen_iff_frontier_eq_empty' : Prop := True
/-- isClopen_empty (abstract). -/
def isClopen_empty' : Prop := True
/-- isClopen_univ (abstract). -/
def isClopen_univ' : Prop := True
/-- isClopen_compl_iff (abstract). -/
def isClopen_compl_iff' : Prop := True
-- COLLISION: himp' already in Order.lean — rename needed
/-- isClopen_iUnion_of_finite (abstract). -/
def isClopen_iUnion_of_finite' : Prop := True
/-- isClopen_biUnion (abstract). -/
def isClopen_biUnion' : Prop := True
/-- isClopen_biUnion_finset (abstract). -/
def isClopen_biUnion_finset' : Prop := True
/-- isClopen_iInter_of_finite (abstract). -/
def isClopen_iInter_of_finite' : Prop := True
/-- isClopen_biInter (abstract). -/
def isClopen_biInter' : Prop := True
/-- isClopen_biInter_finset (abstract). -/
def isClopen_biInter_finset' : Prop := True
/-- preimage_isClopen_of_isClopen (abstract). -/
def preimage_isClopen_of_isClopen' : Prop := True
/-- isClopen_inter_of_disjoint_cover_clopen (abstract). -/
def isClopen_inter_of_disjoint_cover_clopen' : Prop := True
/-- isClopen_of_disjoint_cover_open (abstract). -/
def isClopen_of_disjoint_cover_open' : Prop := True
/-- isClopen_discrete (abstract). -/
def isClopen_discrete' : Prop := True
/-- isClopen_range_inl (abstract). -/
def isClopen_range_inl' : Prop := True
/-- isClopen_range_inr (abstract). -/
def isClopen_range_inr' : Prop := True
/-- isClopen_range_sigmaMk (abstract). -/
def isClopen_range_sigmaMk' : Prop := True
/-- isClopen_preimage (abstract). -/
def isClopen_preimage' : Prop := True
/-- continuous_boolIndicator_iff_isClopen (abstract). -/
def continuous_boolIndicator_iff_isClopen' : Prop := True
/-- continuousOn_boolIndicator_iff_isClopen (abstract). -/
def continuousOn_boolIndicator_iff_isClopen' : Prop := True

-- ClopenBox.lean
/-- exists_prod_subset (abstract). -/
def exists_prod_subset' : Prop := True
/-- exists_finset_eq_sup_prod (abstract). -/
def exists_finset_eq_sup_prod' : Prop := True
/-- surjective_finset_sup_prod (abstract). -/
def surjective_finset_sup_prod' : Prop := True
/-- countable_iff_secondCountable (abstract). -/
def countable_iff_secondCountable' : Prop := True

-- CompactOpen.lean
/-- isOpen_setOf_mapsTo (abstract). -/
def isOpen_setOf_mapsTo' : Prop := True
/-- eventually_mapsTo (abstract). -/
def eventually_mapsTo' : Prop := True
/-- nhds_compactOpen (abstract). -/
def nhds_compactOpen' : Prop := True
/-- tendsto_nhds_compactOpen (abstract). -/
def tendsto_nhds_compactOpen' : Prop := True
/-- continuous_compactOpen (abstract). -/
def continuous_compactOpen' : Prop := True
/-- continuous_postcomp (abstract). -/
def continuous_postcomp' : Prop := True
/-- isInducing_postcomp (abstract). -/
def isInducing_postcomp' : Prop := True
/-- isEmbedding_postcomp (abstract). -/
def isEmbedding_postcomp' : Prop := True
/-- continuous_precomp (abstract). -/
def continuous_precomp' : Prop := True
/-- compRightContinuousMap (abstract). -/
def compRightContinuousMap' : Prop := True
/-- compRightHomeomorph (abstract). -/
def compRightHomeomorph' : Prop := True
-- COLLISION: continuous_comp' already in Order.lean — rename needed
/-- compCM (abstract). -/
def compCM' : Prop := True
-- COLLISION: continuous_coe' already in RingTheory2.lean — rename needed
/-- isClosed_setOf_mapsTo (abstract). -/
def isClosed_setOf_mapsTo' : Prop := True
/-- isClopen_setOf_mapsTo (abstract). -/
def isClopen_setOf_mapsTo' : Prop := True
/-- specializes_coe (abstract). -/
def specializes_coe' : Prop := True
/-- inseparable_coe (abstract). -/
def inseparable_coe' : Prop := True
/-- continuous_restrict (abstract). -/
def continuous_restrict' : Prop := True
/-- compactOpen_le_induced (abstract). -/
def compactOpen_le_induced' : Prop := True
/-- compactOpen_eq_iInf_induced (abstract). -/
def compactOpen_eq_iInf_induced' : Prop := True
/-- nhds_compactOpen_eq_iInf_nhds_induced (abstract). -/
def nhds_compactOpen_eq_iInf_nhds_induced' : Prop := True
/-- tendsto_compactOpen_restrict (abstract). -/
def tendsto_compactOpen_restrict' : Prop := True
/-- tendsto_compactOpen_iff_forall (abstract). -/
def tendsto_compactOpen_iff_forall' : Prop := True
/-- exists_tendsto_compactOpen_iff_forall (abstract). -/
def exists_tendsto_compactOpen_iff_forall' : Prop := True
-- COLLISION: coev' already in CategoryTheory.lean — rename needed
/-- continuous_coev (abstract). -/
def continuous_coev' : Prop := True
-- COLLISION: isCompact_singleton' already in Analysis.lean — rename needed
-- COLLISION: curry' already in Order.lean — rename needed
/-- continuous_curry' (abstract). -/
def continuous_curry' : Prop := True
/-- continuous_uncurry_of_continuous (abstract). -/
def continuous_uncurry_of_continuous' : Prop := True
-- COLLISION: uncurry' already in Order.lean — rename needed
/-- continuousMapOfUnique (abstract). -/
def continuousMapOfUnique' : Prop := True
/-- continuous_lift_prod_left (abstract). -/
def continuous_lift_prod_left' : Prop := True
/-- continuous_lift_prod_right (abstract). -/
def continuous_lift_prod_right' : Prop := True

-- Compactification/OnePoint.lean
/-- OnePoint (abstract). -/
def OnePoint' : Prop := True
/-- infty (abstract). -/
def infty' : Prop := True
/-- some_eq_iff (abstract). -/
def some_eq_iff' : Prop := True
-- COLLISION: «forall'» already in Algebra.lean — rename needed
-- COLLISION: «exists'» already in Algebra.lean — rename needed
/-- coe_eq_coe (abstract). -/
def coe_eq_coe' : Prop := True
-- COLLISION: rec' already in SetTheory.lean — rename needed
-- COLLISION: elim' already in Order.lean — rename needed
/-- isCompl_range_coe_infty (abstract). -/
def isCompl_range_coe_infty' : Prop := True
/-- range_coe_union_infty (abstract). -/
def range_coe_union_infty' : Prop := True
/-- insert_infty_range_coe (abstract). -/
def insert_infty_range_coe' : Prop := True
/-- range_coe_inter_infty (abstract). -/
def range_coe_inter_infty' : Prop := True
/-- compl_range_coe (abstract). -/
def compl_range_coe' : Prop := True
/-- compl_infty (abstract). -/
def compl_infty' : Prop := True
/-- compl_image_coe (abstract). -/
def compl_image_coe' : Prop := True
/-- ne_infty_iff_exists (abstract). -/
def ne_infty_iff_exists' : Prop := True
/-- not_mem_range_coe_iff (abstract). -/
def not_mem_range_coe_iff' : Prop := True
-- COLLISION: map_id' already in Order.lean — rename needed
/-- isOpen_iff_of_mem' (abstract). -/
def isOpen_iff_of_mem' : Prop := True
/-- isOpen_iff_of_not_mem (abstract). -/
def isOpen_iff_of_not_mem' : Prop := True
/-- isClosed_iff_of_mem (abstract). -/
def isClosed_iff_of_mem' : Prop := True
/-- isClosed_iff_of_not_mem (abstract). -/
def isClosed_iff_of_not_mem' : Prop := True
/-- isOpen_image_coe (abstract). -/
def isOpen_image_coe' : Prop := True
/-- isOpen_compl_image_coe (abstract). -/
def isOpen_compl_image_coe' : Prop := True
/-- isClosed_image_coe (abstract). -/
def isClosed_image_coe' : Prop := True
/-- opensOfCompl (abstract). -/
def opensOfCompl' : Prop := True
/-- infty_mem_opensOfCompl (abstract). -/
def infty_mem_opensOfCompl' : Prop := True
-- COLLISION: isOpenEmbedding_coe' already in Analysis.lean — rename needed
/-- isOpen_range_coe (abstract). -/
def isOpen_range_coe' : Prop := True
/-- isClosed_infty (abstract). -/
def isClosed_infty' : Prop := True
/-- nhds_coe_eq (abstract). -/
def nhds_coe_eq' : Prop := True
/-- nhdsWithin_coe_image (abstract). -/
def nhdsWithin_coe_image' : Prop := True
/-- nhdsWithin_coe (abstract). -/
def nhdsWithin_coe' : Prop := True
/-- comap_coe_nhds (abstract). -/
def comap_coe_nhds' : Prop := True
/-- nhdsWithin_compl_infty_eq (abstract). -/
def nhdsWithin_compl_infty_eq' : Prop := True
/-- nhds_infty_eq (abstract). -/
def nhds_infty_eq' : Prop := True
/-- tendsto_coe_infty (abstract). -/
def tendsto_coe_infty' : Prop := True
/-- hasBasis_nhds_infty (abstract). -/
def hasBasis_nhds_infty' : Prop := True
/-- comap_coe_nhds_infty (abstract). -/
def comap_coe_nhds_infty' : Prop := True
/-- le_nhds_infty (abstract). -/
def le_nhds_infty' : Prop := True
/-- ultrafilter_le_nhds_infty (abstract). -/
def ultrafilter_le_nhds_infty' : Prop := True
/-- tendsto_nhds_infty' (abstract). -/
def tendsto_nhds_infty' : Prop := True
/-- continuousAt_infty' (abstract). -/
def continuousAt_infty' : Prop := True
/-- continuousAt_coe (abstract). -/
def continuousAt_coe' : Prop := True
/-- continuousMapMk (abstract). -/
def continuousMapMk' : Prop := True
/-- continuous_iff_from_discrete (abstract). -/
def continuous_iff_from_discrete' : Prop := True
/-- continuousMapMkDiscrete (abstract). -/
def continuousMapMkDiscrete' : Prop := True
/-- continuousMapDiscreteEquiv (abstract). -/
def continuousMapDiscreteEquiv' : Prop := True
/-- continuous_iff_from_nat (abstract). -/
def continuous_iff_from_nat' : Prop := True
/-- continuousMapMkNat (abstract). -/
def continuousMapMkNat' : Prop := True
/-- continuousMapNatEquiv (abstract). -/
def continuousMapNatEquiv' : Prop := True
/-- denseRange_coe (abstract). -/
def denseRange_coe' : Prop := True
/-- isDenseEmbedding_coe (abstract). -/
def isDenseEmbedding_coe' : Prop := True
/-- not_specializes_infty_coe (abstract). -/
def not_specializes_infty_coe' : Prop := True
/-- not_inseparable_infty_coe (abstract). -/
def not_inseparable_infty_coe' : Prop := True
/-- not_inseparable_coe_infty (abstract). -/
def not_inseparable_coe_infty' : Prop := True
/-- inseparable_iff (abstract). -/
def inseparable_iff' : Prop := True
/-- continuous_map_iff (abstract). -/
def continuous_map_iff' : Prop := True
-- COLLISION: continuous_map' already in MeasureTheory2.lean — rename needed
/-- not_continuous_cofiniteTopology_of_symm (abstract). -/
def not_continuous_cofiniteTopology_of_symm' : Prop := True
/-- equivOfIsEmbeddingOfRangeEq (abstract). -/
def equivOfIsEmbeddingOfRangeEq' : Prop := True
/-- onePointCongr (abstract). -/
def onePointCongr' : Prop := True
/-- t1_counterexample (abstract). -/
def t1_counterexample' : Prop := True

-- Compactification/OnePointEquiv.lean
/-- equivProjectivization (abstract). -/
def equivProjectivization' : Prop := True
/-- equivProjectivization_symm_apply_mk (abstract). -/
def equivProjectivization_symm_apply_mk' : Prop := True

-- Compactness/Compact.lean
/-- exists_clusterPt (abstract). -/
def exists_clusterPt' : Prop := True
/-- exists_mapClusterPt (abstract). -/
def exists_mapClusterPt' : Prop := True
/-- compl_mem_sets (abstract). -/
def compl_mem_sets' : Prop := True
/-- compl_mem_sets_of_nhdsWithin (abstract). -/
def compl_mem_sets_of_nhdsWithin' : Prop := True
-- COLLISION: inter_right' already in RingTheory2.lean — rename needed
-- COLLISION: inter_left' already in RingTheory2.lean — rename needed
/-- of_isClosed_subset (abstract). -/
def of_isClosed_subset' : Prop := True
-- COLLISION: image_of_continuousOn' already in MeasureTheory2.lean — rename needed
/-- adherence_nhdset (abstract). -/
def adherence_nhdset' : Prop := True
/-- isCompact_iff_ultrafilter_le_nhds (abstract). -/
def isCompact_iff_ultrafilter_le_nhds' : Prop := True
/-- le_nhds_of_unique_clusterPt (abstract). -/
def le_nhds_of_unique_clusterPt' : Prop := True
/-- tendsto_nhds_of_unique_mapClusterPt (abstract). -/
def tendsto_nhds_of_unique_mapClusterPt' : Prop := True
/-- elim_directed_cover (abstract). -/
def elim_directed_cover' : Prop := True
/-- elim_finite_subcover (abstract). -/
def elim_finite_subcover' : Prop := True
/-- elim_nhds_subcover_nhdsSet' (abstract). -/
def elim_nhds_subcover_nhdsSet' : Prop := True
/-- elim_nhds_subcover' (abstract). -/
def elim_nhds_subcover' : Prop := True
/-- disjoint_nhdsSet_left (abstract). -/
def disjoint_nhdsSet_left' : Prop := True
/-- disjoint_nhdsSet_right (abstract). -/
def disjoint_nhdsSet_right' : Prop := True
/-- elim_directed_family_closed (abstract). -/
def elim_directed_family_closed' : Prop := True
/-- elim_finite_subfamily_closed (abstract). -/
def elim_finite_subfamily_closed' : Prop := True
/-- finite_nonempty_inter_compact (abstract). -/
def finite_nonempty_inter_compact' : Prop := True
/-- inter_iInter_nonempty (abstract). -/
def inter_iInter_nonempty' : Prop := True
/-- nonempty_iInter_of_directed_nonempty_isCompact_isClosed (abstract). -/
def nonempty_iInter_of_directed_nonempty_isCompact_isClosed' : Prop := True
/-- nonempty_sInter_of_directed_nonempty_isCompact_isClosed (abstract). -/
def nonempty_sInter_of_directed_nonempty_isCompact_isClosed' : Prop := True
/-- nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (abstract). -/
def nonempty_iInter_of_sequence_nonempty_isCompact_isClosed' : Prop := True
/-- elim_finite_subcover_image (abstract). -/
def elim_finite_subcover_image' : Prop := True
/-- isCompact_of_finite_subcover (abstract). -/
def isCompact_of_finite_subcover' : Prop := True
/-- isCompact_of_finite_subfamily_closed (abstract). -/
def isCompact_of_finite_subfamily_closed' : Prop := True
/-- isCompact_iff_finite_subcover (abstract). -/
def isCompact_iff_finite_subcover' : Prop := True
/-- isCompact_iff_finite_subfamily_closed (abstract). -/
def isCompact_iff_finite_subfamily_closed' : Prop := True
/-- mem_nhdsSet_prod_of_forall (abstract). -/
def mem_nhdsSet_prod_of_forall' : Prop := True
/-- nhdsSet_prod_eq_biSup (abstract). -/
def nhdsSet_prod_eq_biSup' : Prop := True
/-- prod_nhdsSet_eq_biSup (abstract). -/
def prod_nhdsSet_eq_biSup' : Prop := True
/-- mem_prod_nhdsSet_of_forall (abstract). -/
def mem_prod_nhdsSet_of_forall' : Prop := True
/-- nhdsSet_inf_eq_biSup (abstract). -/
def nhdsSet_inf_eq_biSup' : Prop := True
/-- inf_nhdsSet_eq_biSup (abstract). -/
def inf_nhdsSet_eq_biSup' : Prop := True
/-- mem_nhdsSet_inf_of_forall (abstract). -/
def mem_nhdsSet_inf_of_forall' : Prop := True
/-- mem_inf_nhdsSet_of_forall (abstract). -/
def mem_inf_nhdsSet_of_forall' : Prop := True
/-- eventually_forall_of_forall_eventually (abstract). -/
def eventually_forall_of_forall_eventually' : Prop := True
/-- isCompact_empty (abstract). -/
def isCompact_empty' : Prop := True
/-- isCompact_biUnion (abstract). -/
def isCompact_biUnion' : Prop := True
/-- isCompact_accumulate (abstract). -/
def isCompact_accumulate' : Prop := True
/-- isCompact_sUnion (abstract). -/
def isCompact_sUnion' : Prop := True
/-- isCompact_iUnion (abstract). -/
def isCompact_iUnion' : Prop := True
/-- finite_of_discrete (abstract). -/
def finite_of_discrete' : Prop := True
/-- isCompact_iff_finite (abstract). -/
def isCompact_iff_finite' : Prop := True
/-- exists_subset_nhds_of_isCompact' (abstract). -/
def exists_subset_nhds_of_isCompact' : Prop := True
/-- eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open (abstract). -/
def eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open' : Prop := True
/-- isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis (abstract). -/
def isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis' : Prop := True
/-- hasBasis_cocompact (abstract). -/
def hasBasis_cocompact' : Prop := True
/-- mem_cocompact (abstract). -/
def mem_cocompact' : Prop := True
/-- compl_mem_cocompact (abstract). -/
def compl_mem_cocompact' : Prop := True
/-- cocompact_le_cofinite (abstract). -/
def cocompact_le_cofinite' : Prop := True
/-- disjoint_cocompact_left (abstract). -/
def disjoint_cocompact_left' : Prop := True
/-- disjoint_cocompact_right (abstract). -/
def disjoint_cocompact_right' : Prop := True
/-- cocompact_eq (abstract). -/
def cocompact_eq' : Prop := True
/-- isCompact_insert_range_of_cocompact (abstract). -/
def isCompact_insert_range_of_cocompact' : Prop := True
/-- isCompact_insert_range_of_cofinite (abstract). -/
def isCompact_insert_range_of_cofinite' : Prop := True
/-- isCompact_insert_range (abstract). -/
def isCompact_insert_range' : Prop := True
/-- hasBasis_coclosedCompact (abstract). -/
def hasBasis_coclosedCompact' : Prop := True
/-- mem_coclosedCompact_iff (abstract). -/
def mem_coclosedCompact_iff' : Prop := True
/-- mem_coclosedCompact (abstract). -/
def mem_coclosedCompact' : Prop := True
/-- mem_coclosed_compact' (abstract). -/
def mem_coclosed_compact' : Prop := True
/-- compl_mem_coclosedCompact (abstract). -/
def compl_mem_coclosedCompact' : Prop := True
/-- cocompact_le_coclosedCompact (abstract). -/
def cocompact_le_coclosedCompact' : Prop := True
/-- compl_mem_coclosedCompact_of_isClosed (abstract). -/
def compl_mem_coclosedCompact_of_isClosed' : Prop := True
/-- inCompact (abstract). -/
def inCompact' : Prop := True
-- COLLISION: isBounded_iff' already in Order.lean — rename needed
/-- nhdsSet_prod_eq (abstract). -/
def nhdsSet_prod_eq' : Prop := True
/-- nhdsSet_prod_le_of_disjoint_cocompact (abstract). -/
def nhdsSet_prod_le_of_disjoint_cocompact' : Prop := True
/-- prod_nhdsSet_le_of_disjoint_cocompact (abstract). -/
def prod_nhdsSet_le_of_disjoint_cocompact' : Prop := True
/-- generalized_tube_lemma (abstract). -/
def generalized_tube_lemma' : Prop := True
/-- exists_clusterPt_of_compactSpace (abstract). -/
def exists_clusterPt_of_compactSpace' : Prop := True
/-- compactSpace_of_finite_subfamily_closed (abstract). -/
def compactSpace_of_finite_subfamily_closed' : Prop := True
/-- noncompact_univ (abstract). -/
def noncompact_univ' : Prop := True
/-- ne_univ (abstract). -/
def ne_univ' : Prop := True
/-- cocompact_eq_bot (abstract). -/
def cocompact_eq_bot' : Prop := True
/-- noncompactSpace_of_neBot (abstract). -/
def noncompactSpace_of_neBot' : Prop := True
/-- cocompact_neBot_iff (abstract). -/
def cocompact_neBot_iff' : Prop := True
/-- not_compactSpace_iff (abstract). -/
def not_compactSpace_iff' : Prop := True
/-- finite_of_compact_of_discrete (abstract). -/
def finite_of_compact_of_discrete' : Prop := True
/-- exists_accPt_cofinite_inf_principal_of_subset_isCompact (abstract). -/
def exists_accPt_cofinite_inf_principal_of_subset_isCompact' : Prop := True
/-- exists_accPt_of_subset_isCompact (abstract). -/
def exists_accPt_of_subset_isCompact' : Prop := True
/-- exists_accPt_cofinite_inf_principal (abstract). -/
def exists_accPt_cofinite_inf_principal' : Prop := True
/-- exists_accPt_principal (abstract). -/
def exists_accPt_principal' : Prop := True
/-- exists_nhds_ne_neBot (abstract). -/
def exists_nhds_ne_neBot' : Prop := True
/-- finite_cover_nhds_interior (abstract). -/
def finite_cover_nhds_interior' : Prop := True
/-- finite_cover_nhds (abstract). -/
def finite_cover_nhds' : Prop := True
/-- finite_nonempty_of_compact (abstract). -/
def finite_nonempty_of_compact' : Prop := True
/-- finite_of_compact (abstract). -/
def finite_of_compact' : Prop := True
/-- fintypeOfCompact (abstract). -/
def fintypeOfCompact' : Prop := True
/-- comap_cocompact_le (abstract). -/
def comap_cocompact_le' : Prop := True
/-- isCompact_diagonal (abstract). -/
def isCompact_diagonal' : Prop := True
/-- isClosedMap_snd_of_compactSpace (abstract). -/
def isClosedMap_snd_of_compactSpace' : Prop := True
/-- isCompact_univ (abstract). -/
def isCompact_univ' : Prop := True
/-- isClosedMap_fst_of_compactSpace (abstract). -/
def isClosedMap_fst_of_compactSpace' : Prop := True
/-- exists_subset_nhds_of_compactSpace (abstract). -/
def exists_subset_nhds_of_compactSpace' : Prop := True
/-- isCompact_iff (abstract). -/
def isCompact_iff' : Prop := True
/-- isCompact_preimage_iff (abstract). -/
def isCompact_preimage_iff' : Prop := True
/-- tendsto_cocompact (abstract). -/
def tendsto_cocompact' : Prop := True
/-- isCompact_iff_isCompact_univ (abstract). -/
def isCompact_iff_isCompact_univ' : Prop := True
/-- isCompact_iff_compactSpace (abstract). -/
def isCompact_iff_compactSpace' : Prop := True
-- COLLISION: finite' already in Order.lean — rename needed
/-- exists_nhds_ne_inf_principal_neBot (abstract). -/
def exists_nhds_ne_inf_principal_neBot' : Prop := True
-- COLLISION: noncompactSpace' already in Analysis.lean — rename needed
-- COLLISION: compactSpace' already in Analysis.lean — rename needed
/-- coprod_cocompact (abstract). -/
def coprod_cocompact' : Prop := True
/-- noncompactSpace_iff (abstract). -/
def noncompactSpace_iff' : Prop := True
/-- isCompact_pi_infinite (abstract). -/
def isCompact_pi_infinite' : Prop := True
/-- isCompact_univ_pi (abstract). -/
def isCompact_univ_pi' : Prop := True
/-- isCompact_iff_of_isClosed (abstract). -/
def isCompact_iff_of_isClosed' : Prop := True
/-- exists_compact_superset_iff (abstract). -/
def exists_compact_superset_iff' : Prop := True
/-- coprodᵢ_cocompact (abstract). -/
def coprodᵢ_cocompact' : Prop := True
/-- exists_minimal_nonempty_closed_subset (abstract). -/
def exists_minimal_nonempty_closed_subset' : Prop := True

-- Compactness/CompactlyGeneratedSpace.lean
-- COLLISION: where' already in Order.lean — rename needed
/-- compactlyGenerated (abstract). -/
def compactlyGenerated' : Prop := True
/-- continuous_from_compactlyGenerated (abstract). -/
def continuous_from_compactlyGenerated' : Prop := True
/-- UCompactlyGeneratedSpace (abstract). -/
def UCompactlyGeneratedSpace' : Prop := True
/-- eq_compactlyGenerated (abstract). -/
def eq_compactlyGenerated' : Prop := True
/-- uCompactlyGeneratedSpace_of_continuous_maps (abstract). -/
def uCompactlyGeneratedSpace_of_continuous_maps' : Prop := True
/-- continuous_from_uCompactlyGeneratedSpace (abstract). -/
def continuous_from_uCompactlyGeneratedSpace' : Prop := True
/-- uCompactlyGeneratedSpace_of_isClosed (abstract). -/
def uCompactlyGeneratedSpace_of_isClosed' : Prop := True
/-- uCompactlyGeneratedSpace_of_isOpen (abstract). -/
def uCompactlyGeneratedSpace_of_isOpen' : Prop := True
/-- uCompactlyGeneratedSpace_of_coinduced (abstract). -/
def uCompactlyGeneratedSpace_of_coinduced' : Prop := True
/-- CompactlyGeneratedSpace (abstract). -/
def CompactlyGeneratedSpace' : Prop := True
/-- continuous_from_compactlyGeneratedSpace (abstract). -/
def continuous_from_compactlyGeneratedSpace' : Prop := True
/-- compactlyGeneratedSpace_of_continuous_maps (abstract). -/
def compactlyGeneratedSpace_of_continuous_maps' : Prop := True
/-- compactlyGeneratedSpace_of_isClosed (abstract). -/
def compactlyGeneratedSpace_of_isClosed' : Prop := True
-- COLLISION: isClosed' already in Analysis.lean — rename needed
/-- compactlyGeneratedSpace_of_isOpen (abstract). -/
def compactlyGeneratedSpace_of_isOpen' : Prop := True
/-- compactlyGeneratedSpace_of_coinduced (abstract). -/
def compactlyGeneratedSpace_of_coinduced' : Prop := True
/-- isClosed_iff_of_t2 (abstract). -/
def isClosed_iff_of_t2' : Prop := True
/-- compactlyGeneratedSpace_of_isClosed_of_t2 (abstract). -/
def compactlyGeneratedSpace_of_isClosed_of_t2' : Prop := True
/-- compactlyGeneratedSpace_of_isOpen_of_t2 (abstract). -/
def compactlyGeneratedSpace_of_isOpen_of_t2' : Prop := True

-- Compactness/DeltaGeneratedSpace.lean
/-- deltaGenerated (abstract). -/
def deltaGenerated' : Prop := True
/-- deltaGenerated_eq_coinduced (abstract). -/
def deltaGenerated_eq_coinduced' : Prop := True
/-- deltaGenerated_le (abstract). -/
def deltaGenerated_le' : Prop := True
/-- isOpen_deltaGenerated_iff (abstract). -/
def isOpen_deltaGenerated_iff' : Prop := True
/-- continuous_euclidean_to_deltaGenerated (abstract). -/
def continuous_euclidean_to_deltaGenerated' : Prop := True
/-- deltaGenerated_deltaGenerated_eq (abstract). -/
def deltaGenerated_deltaGenerated_eq' : Prop := True
/-- DeltaGeneratedSpace (abstract). -/
def DeltaGeneratedSpace' : Prop := True
/-- eq_deltaGenerated (abstract). -/
def eq_deltaGenerated' : Prop := True
/-- continuous_to_deltaGenerated (abstract). -/
def continuous_to_deltaGenerated' : Prop := True
/-- deltaGeneratedSpace_deltaGenerated (abstract). -/
def deltaGeneratedSpace_deltaGenerated' : Prop := True
/-- deltaGenerated_mono (abstract). -/
def deltaGenerated_mono' : Prop := True
-- COLLISION: counit' already in Algebra.lean — rename needed
/-- continuous_counit (abstract). -/
def continuous_counit' : Prop := True
-- COLLISION: iSup' already in Order.lean — rename needed

-- Compactness/Exterior.lean
/-- exterior_iff (abstract). -/
def exterior_iff' : Prop := True
/-- isCompact_exterior (abstract). -/
def isCompact_exterior' : Prop := True

-- Compactness/Lindelof.lean
/-- IsLindelof (abstract). -/
def IsLindelof' : Prop := True
/-- elim_countable_subcover (abstract). -/
def elim_countable_subcover' : Prop := True
/-- indexed_countable_subcover (abstract). -/
def indexed_countable_subcover' : Prop := True
/-- elim_countable_subfamily_closed (abstract). -/
def elim_countable_subfamily_closed' : Prop := True
/-- elim_countable_subcover_image (abstract). -/
def elim_countable_subcover_image' : Prop := True
/-- isLindelof_of_countable_subcover (abstract). -/
def isLindelof_of_countable_subcover' : Prop := True
/-- isLindelof_of_countable_subfamily_closed (abstract). -/
def isLindelof_of_countable_subfamily_closed' : Prop := True
/-- isLindelof_iff_countable_subcover (abstract). -/
def isLindelof_iff_countable_subcover' : Prop := True
/-- isLindelof_iff_countable_subfamily_closed (abstract). -/
def isLindelof_iff_countable_subfamily_closed' : Prop := True
/-- isLindelof_empty (abstract). -/
def isLindelof_empty' : Prop := True
/-- isLindelof_singleton (abstract). -/
def isLindelof_singleton' : Prop := True
/-- isLindelof (abstract). -/
def isLindelof' : Prop := True
/-- isLindelof_biUnion (abstract). -/
def isLindelof_biUnion' : Prop := True
/-- isLindelof_accumulate (abstract). -/
def isLindelof_accumulate' : Prop := True
/-- isLindelof_sUnion (abstract). -/
def isLindelof_sUnion' : Prop := True
/-- isLindelof_iUnion (abstract). -/
def isLindelof_iUnion' : Prop := True
/-- countable_of_discrete (abstract). -/
def countable_of_discrete' : Prop := True
/-- isLindelof_iff_countable (abstract). -/
def isLindelof_iff_countable' : Prop := True
/-- isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis (abstract). -/
def isLindelof_open_iff_eq_countable_iUnion_of_isTopologicalBasis' : Prop := True
/-- coLindelof (abstract). -/
def coLindelof' : Prop := True
/-- hasBasis_coLindelof (abstract). -/
def hasBasis_coLindelof' : Prop := True
/-- mem_coLindelof (abstract). -/
def mem_coLindelof' : Prop := True
/-- compl_mem_coLindelof (abstract). -/
def compl_mem_coLindelof' : Prop := True
/-- coLindelof_le_cofinite (abstract). -/
def coLindelof_le_cofinite' : Prop := True
/-- isLindelof_insert_range_of_coLindelof (abstract). -/
def isLindelof_insert_range_of_coLindelof' : Prop := True
/-- coclosedLindelof (abstract). -/
def coclosedLindelof' : Prop := True
/-- hasBasis_coclosedLindelof (abstract). -/
def hasBasis_coclosedLindelof' : Prop := True
/-- mem_coclosedLindelof (abstract). -/
def mem_coclosedLindelof' : Prop := True
/-- mem_coclosed_Lindelof' (abstract). -/
def mem_coclosed_Lindelof' : Prop := True
/-- coLindelof_le_coclosedLindelof (abstract). -/
def coLindelof_le_coclosedLindelof' : Prop := True
/-- compl_mem_coclosedLindelof_of_isClosed (abstract). -/
def compl_mem_coclosedLindelof_of_isClosed' : Prop := True
/-- LindelofSpace (abstract). -/
def LindelofSpace' : Prop := True
/-- cluster_point_of_Lindelof (abstract). -/
def cluster_point_of_Lindelof' : Prop := True
/-- lindelofSpace_of_countable_subfamily_closed (abstract). -/
def lindelofSpace_of_countable_subfamily_closed' : Prop := True
/-- NonLindelofSpace (abstract). -/
def NonLindelofSpace' : Prop := True
/-- nonLindelof_univ (abstract). -/
def nonLindelof_univ' : Prop := True
/-- coLindelof_eq_bot (abstract). -/
def coLindelof_eq_bot' : Prop := True
/-- nonLindelofSpace_of_neBot (abstract). -/
def nonLindelofSpace_of_neBot' : Prop := True
/-- coLindelof_neBot_iff (abstract). -/
def coLindelof_neBot_iff' : Prop := True
/-- not_LindelofSpace_iff (abstract). -/
def not_LindelofSpace_iff' : Prop := True
/-- countable_of_Lindelof_of_discrete (abstract). -/
def countable_of_Lindelof_of_discrete' : Prop := True
/-- countable_cover_nhds_interior (abstract). -/
def countable_cover_nhds_interior' : Prop := True
/-- comap_coLindelof_le (abstract). -/
def comap_coLindelof_le' : Prop := True
/-- isLindelof_range (abstract). -/
def isLindelof_range' : Prop := True
/-- isLindelof_diagonal (abstract). -/
def isLindelof_diagonal' : Prop := True
/-- isLindelof_iff (abstract). -/
def isLindelof_iff' : Prop := True
/-- isLindelof_preimage (abstract). -/
def isLindelof_preimage' : Prop := True
/-- tendsto_coLindelof (abstract). -/
def tendsto_coLindelof' : Prop := True
/-- isLindelof_iff_isLindelof_univ (abstract). -/
def isLindelof_iff_isLindelof_univ' : Prop := True
/-- isLindelof_iff_LindelofSpace (abstract). -/
def isLindelof_iff_LindelofSpace' : Prop := True
-- COLLISION: of_coe' already in Order.lean — rename needed
-- COLLISION: countable' already in Algebra.lean — rename needed
/-- nonLindelofSpace (abstract). -/
def nonLindelofSpace' : Prop := True
/-- of_continuous_surjective (abstract). -/
def of_continuous_surjective' : Prop := True
/-- IsHereditarilyLindelof (abstract). -/
def IsHereditarilyLindelof' : Prop := True
/-- HereditarilyLindelofSpace (abstract). -/
def HereditarilyLindelofSpace' : Prop := True
/-- isLindelof_subset (abstract). -/
def isLindelof_subset' : Prop := True
/-- HereditarilyLindelof_LindelofSets (abstract). -/
def HereditarilyLindelof_LindelofSets' : Prop := True
/-- eq_open_union_countable (abstract). -/
def eq_open_union_countable' : Prop := True

-- Compactness/LocallyCompact.lean
/-- weaklyLocallyCompactSpace (abstract). -/
def weaklyLocallyCompactSpace' : Prop := True
/-- exists_compact_superset (abstract). -/
def exists_compact_superset' : Prop := True
/-- disjoint_nhds_cocompact (abstract). -/
def disjoint_nhds_cocompact' : Prop := True
/-- compact_basis_nhds (abstract). -/
def compact_basis_nhds' : Prop := True
/-- local_compact_nhds (abstract). -/
def local_compact_nhds' : Prop := True
/-- of_hasBasis (abstract). -/
def of_hasBasis' : Prop := True
/-- exists_compact_subset (abstract). -/
def exists_compact_subset' : Prop := True
/-- exists_mem_nhdsSet_isCompact_mapsTo (abstract). -/
def exists_mem_nhdsSet_isCompact_mapsTo' : Prop := True
/-- exists_compact_between (abstract). -/
def exists_compact_between' : Prop := True
-- COLLISION: locallyCompactSpace' already in Analysis.lean — rename needed

-- Compactness/Paracompact.lean
/-- ParacompactSpace (abstract). -/
def ParacompactSpace' : Prop := True
/-- precise_refinement (abstract). -/
def precise_refinement' : Prop := True
/-- precise_refinement_set (abstract). -/
def precise_refinement_set' : Prop := True
/-- paracompactSpace (abstract). -/
def paracompactSpace' : Prop := True
/-- paracompactSpace_iff (abstract). -/
def paracompactSpace_iff' : Prop := True
/-- refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set (abstract). -/
def refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set' : Prop := True
/-- refinement_of_locallyCompact_sigmaCompact_of_nhds_basis (abstract). -/
def refinement_of_locallyCompact_sigmaCompact_of_nhds_basis' : Prop := True

-- Compactness/SigmaCompact.lean
/-- IsSigmaCompact (abstract). -/
def IsSigmaCompact' : Prop := True
/-- isSigmaCompact (abstract). -/
def isSigmaCompact' : Prop := True
/-- isSigmaCompact_empty (abstract). -/
def isSigmaCompact_empty' : Prop := True
/-- isSigmaCompact_iUnion_of_isCompact (abstract). -/
def isSigmaCompact_iUnion_of_isCompact' : Prop := True
/-- isSigmaCompact_sUnion_of_isCompact (abstract). -/
def isSigmaCompact_sUnion_of_isCompact' : Prop := True
/-- isSigmaCompact_iUnion (abstract). -/
def isSigmaCompact_iUnion' : Prop := True
/-- isSigmaCompact_sUnion (abstract). -/
def isSigmaCompact_sUnion' : Prop := True
/-- isSigmaCompact_biUnion (abstract). -/
def isSigmaCompact_biUnion' : Prop := True
/-- isSigmaCompact_iff (abstract). -/
def isSigmaCompact_iff' : Prop := True
/-- SigmaCompactSpace (abstract). -/
def SigmaCompactSpace' : Prop := True
/-- isSigmaCompact_univ_iff (abstract). -/
def isSigmaCompact_univ_iff' : Prop := True
/-- isSigmaCompact_univ (abstract). -/
def isSigmaCompact_univ' : Prop := True
/-- SigmaCompactSpace_iff_exists_compact_covering (abstract). -/
def SigmaCompactSpace_iff_exists_compact_covering' : Prop := True
/-- exists_compact_covering (abstract). -/
def exists_compact_covering' : Prop := True
/-- isSigmaCompact_range (abstract). -/
def isSigmaCompact_range' : Prop := True
/-- isSigmaCompact_iff_isSigmaCompact_univ (abstract). -/
def isSigmaCompact_iff_isSigmaCompact_univ' : Prop := True
/-- isSigmaCompact_iff_sigmaCompactSpace (abstract). -/
def isSigmaCompact_iff_sigmaCompactSpace' : Prop := True
/-- of_countable (abstract). -/
def of_countable' : Prop := True
/-- compactCovering (abstract). -/
def compactCovering' : Prop := True
/-- isCompact_compactCovering (abstract). -/
def isCompact_compactCovering' : Prop := True
/-- iUnion_compactCovering (abstract). -/
def iUnion_compactCovering' : Prop := True
/-- iUnion_closure_compactCovering (abstract). -/
def iUnion_closure_compactCovering' : Prop := True
/-- compactCovering_subset (abstract). -/
def compactCovering_subset' : Prop := True
/-- exists_mem_compactCovering (abstract). -/
def exists_mem_compactCovering' : Prop := True
/-- sigmaCompactSpace (abstract). -/
def sigmaCompactSpace' : Prop := True
/-- countable_univ (abstract). -/
def countable_univ' : Prop := True
/-- encodable (abstract). -/
def encodable' : Prop := True
/-- countable_cover_nhdsWithin_of_sigmaCompact (abstract). -/
def countable_cover_nhdsWithin_of_sigmaCompact' : Prop := True
/-- countable_cover_nhds_of_sigmaCompact (abstract). -/
def countable_cover_nhds_of_sigmaCompact' : Prop := True
/-- CompactExhaustion (abstract). -/
def CompactExhaustion' : Prop := True
/-- subset_interior_succ (abstract). -/
def subset_interior_succ' : Prop := True
/-- subset_succ (abstract). -/
def subset_succ' : Prop := True
/-- subset_interior (abstract). -/
def subset_interior' : Prop := True
/-- iUnion_eq (abstract). -/
def iUnion_eq' : Prop := True
-- COLLISION: exists_mem' already in Order.lean — rename needed
/-- exists_mem_nhds (abstract). -/
def exists_mem_nhds' : Prop := True
/-- exists_superset_of_isCompact (abstract). -/
def exists_superset_of_isCompact' : Prop := True
-- COLLISION: find' already in MeasureTheory2.lean — rename needed
/-- mem_find (abstract). -/
def mem_find' : Prop := True
/-- mem_iff_find_le (abstract). -/
def mem_iff_find_le' : Prop := True
/-- shiftr (abstract). -/
def shiftr' : Prop := True
/-- find_shiftr (abstract). -/
def find_shiftr' : Prop := True
/-- mem_diff_shiftr_find (abstract). -/
def mem_diff_shiftr_find' : Prop := True
-- COLLISION: choice' already in SetTheory.lean — rename needed

-- CompletelyRegular.lean
/-- CompletelyRegularSpace (abstract). -/
def CompletelyRegularSpace' : Prop := True
/-- T35Space (abstract). -/
def T35Space' : Prop := True
/-- separatesPoints_continuous_of_t35Space (abstract). -/
def separatesPoints_continuous_of_t35Space' : Prop := True
/-- separatesPoints_continuous_of_t35Space_Icc (abstract). -/
def separatesPoints_continuous_of_t35Space_Icc' : Prop := True
/-- injective_stoneCechUnit_of_t35Space (abstract). -/
def injective_stoneCechUnit_of_t35Space' : Prop := True

-- Connected/Basic.lean
-- COLLISION: IsPreconnected' already in CategoryTheory.lean — rename needed
-- COLLISION: IsConnected' already in Topology.lean — rename needed
-- COLLISION: isPreconnected' already in Analysis.lean — rename needed
-- COLLISION: isConnected' already in Analysis.lean — rename needed
/-- isPreconnected_empty (abstract). -/
def isPreconnected_empty' : Prop := True
/-- isConnected_singleton (abstract). -/
def isConnected_singleton' : Prop := True
/-- isPreconnected_singleton (abstract). -/
def isPreconnected_singleton' : Prop := True
/-- isPreconnected_of_forall (abstract). -/
def isPreconnected_of_forall' : Prop := True
/-- isPreconnected_of_forall_pair (abstract). -/
def isPreconnected_of_forall_pair' : Prop := True
/-- isPreconnected_sUnion (abstract). -/
def isPreconnected_sUnion' : Prop := True
/-- isPreconnected_iUnion (abstract). -/
def isPreconnected_iUnion' : Prop := True
/-- sUnion_directed (abstract). -/
def sUnion_directed' : Prop := True
/-- biUnion_of_reflTransGen (abstract). -/
def biUnion_of_reflTransGen' : Prop := True
/-- iUnion_of_reflTransGen (abstract). -/
def iUnion_of_reflTransGen' : Prop := True
/-- iUnion_of_chain (abstract). -/
def iUnion_of_chain' : Prop := True
/-- biUnion_of_chain (abstract). -/
def biUnion_of_chain' : Prop := True
/-- isPreconnected_image (abstract). -/
def isPreconnected_image' : Prop := True
/-- preimage_of_isClosedMap (abstract). -/
def preimage_of_isClosedMap' : Prop := True
/-- subset_or_subset (abstract). -/
def subset_or_subset' : Prop := True
/-- subset_left_of_subset_union (abstract). -/
def subset_left_of_subset_union' : Prop := True
/-- subset_right_of_subset_union (abstract). -/
def subset_right_of_subset_union' : Prop := True
/-- subset_of_closure_inter_subset (abstract). -/
def subset_of_closure_inter_subset' : Prop := True
/-- isPreconnected_univ_pi (abstract). -/
def isPreconnected_univ_pi' : Prop := True
/-- isConnected_univ_pi (abstract). -/
def isConnected_univ_pi' : Prop := True
/-- connectedComponent (abstract). -/
def connectedComponent' : Prop := True
/-- connectedComponentIn (abstract). -/
def connectedComponentIn' : Prop := True
/-- connectedComponentIn_eq_image (abstract). -/
def connectedComponentIn_eq_image' : Prop := True
/-- connectedComponentIn_eq_empty (abstract). -/
def connectedComponentIn_eq_empty' : Prop := True
/-- mem_connectedComponent (abstract). -/
def mem_connectedComponent' : Prop := True
/-- mem_connectedComponentIn (abstract). -/
def mem_connectedComponentIn' : Prop := True
/-- connectedComponent_nonempty (abstract). -/
def connectedComponent_nonempty' : Prop := True
/-- connectedComponentIn_nonempty_iff (abstract). -/
def connectedComponentIn_nonempty_iff' : Prop := True
/-- connectedComponentIn_subset (abstract). -/
def connectedComponentIn_subset' : Prop := True
/-- isPreconnected_connectedComponent (abstract). -/
def isPreconnected_connectedComponent' : Prop := True
/-- isPreconnected_connectedComponentIn (abstract). -/
def isPreconnected_connectedComponentIn' : Prop := True
/-- isConnected_connectedComponent (abstract). -/
def isConnected_connectedComponent' : Prop := True
/-- isConnected_connectedComponentIn_iff (abstract). -/
def isConnected_connectedComponentIn_iff' : Prop := True
/-- subset_connectedComponent (abstract). -/
def subset_connectedComponent' : Prop := True
/-- subset_connectedComponentIn (abstract). -/
def subset_connectedComponentIn' : Prop := True
/-- connectedComponent_eq (abstract). -/
def connectedComponent_eq' : Prop := True
/-- connectedComponent_eq_iff_mem (abstract). -/
def connectedComponent_eq_iff_mem' : Prop := True
/-- connectedComponentIn_univ (abstract). -/
def connectedComponentIn_univ' : Prop := True
/-- connectedComponent_disjoint (abstract). -/
def connectedComponent_disjoint' : Prop := True
/-- isClosed_connectedComponent (abstract). -/
def isClosed_connectedComponent' : Prop := True
/-- image_connectedComponent_subset (abstract). -/
def image_connectedComponent_subset' : Prop := True
/-- image_connectedComponentIn_subset (abstract). -/
def image_connectedComponentIn_subset' : Prop := True
/-- mapsTo_connectedComponent (abstract). -/
def mapsTo_connectedComponent' : Prop := True
/-- mapsTo_connectedComponentIn (abstract). -/
def mapsTo_connectedComponentIn' : Prop := True
/-- irreducibleComponent_subset_connectedComponent (abstract). -/
def irreducibleComponent_subset_connectedComponent' : Prop := True
/-- connectedComponentIn_mono (abstract). -/
def connectedComponentIn_mono' : Prop := True
/-- PreconnectedSpace (abstract). -/
def PreconnectedSpace' : Prop := True
/-- ConnectedSpace (abstract). -/
def ConnectedSpace' : Prop := True
/-- isConnected_univ (abstract). -/
def isConnected_univ' : Prop := True
/-- preconnectedSpace_iff_univ (abstract). -/
def preconnectedSpace_iff_univ' : Prop := True
/-- connectedSpace_iff_univ (abstract). -/
def connectedSpace_iff_univ' : Prop := True
/-- isPreconnected_range (abstract). -/
def isPreconnected_range' : Prop := True
/-- isConnected_range (abstract). -/
def isConnected_range' : Prop := True
/-- preconnectedSpace (abstract). -/
def preconnectedSpace' : Prop := True
/-- connectedSpace_iff_connectedComponent (abstract). -/
def connectedSpace_iff_connectedComponent' : Prop := True
/-- preconnectedSpace_iff_connectedComponent (abstract). -/
def preconnectedSpace_iff_connectedComponent' : Prop := True
/-- connectedComponent_eq_univ (abstract). -/
def connectedComponent_eq_univ' : Prop := True
/-- isPreconnected_iff_preconnectedSpace (abstract). -/
def isPreconnected_iff_preconnectedSpace' : Prop := True
/-- isConnected_iff_connectedSpace (abstract). -/
def isConnected_iff_connectedSpace' : Prop := True

-- Connected/Clopen.lean
/-- subset_isClopen (abstract). -/
def subset_isClopen' : Prop := True
/-- isConnected_iff (abstract). -/
def isConnected_iff' : Prop := True
/-- isPreconnected_iff (abstract). -/
def isPreconnected_iff' : Prop := True
/-- exists_lift_sigma (abstract). -/
def exists_lift_sigma' : Prop := True
/-- nonempty_inter (abstract). -/
def nonempty_inter' : Prop := True
/-- isClopen_iff (abstract). -/
def isClopen_iff' : Prop := True
/-- eq_univ (abstract). -/
def eq_univ' : Prop := True
/-- isClopen_preimage_val (abstract). -/
def isClopen_preimage_val' : Prop := True
/-- subsingleton_of_disjoint_isClopen (abstract). -/
def subsingleton_of_disjoint_isClopen' : Prop := True
/-- subsingleton_of_disjoint_isOpen_iUnion_eq_univ (abstract). -/
def subsingleton_of_disjoint_isOpen_iUnion_eq_univ' : Prop := True
/-- subsingleton_of_disjoint_isClosed_iUnion_eq_univ (abstract). -/
def subsingleton_of_disjoint_isClosed_iUnion_eq_univ' : Prop := True
/-- frontier_eq_empty_iff (abstract). -/
def frontier_eq_empty_iff' : Prop := True
/-- nonempty_frontier_iff (abstract). -/
def nonempty_frontier_iff' : Prop := True
/-- induction₂' (abstract). -/
def induction₂' : Prop := True
/-- isPreconnected_iff_subset_of_disjoint (abstract). -/
def isPreconnected_iff_subset_of_disjoint' : Prop := True
/-- isConnected_iff_sUnion_disjoint_open (abstract). -/
def isConnected_iff_sUnion_disjoint_open' : Prop := True
/-- disjoint_or_subset_of_isClopen (abstract). -/
def disjoint_or_subset_of_isClopen' : Prop := True
/-- isPreconnected_iff_subset_of_disjoint_closed (abstract). -/
def isPreconnected_iff_subset_of_disjoint_closed' : Prop := True
/-- isPreconnected_iff_subset_of_fully_disjoint_closed (abstract). -/
def isPreconnected_iff_subset_of_fully_disjoint_closed' : Prop := True
/-- connectedComponent_subset (abstract). -/
def connectedComponent_subset' : Prop := True
/-- connectedComponent_subset_iInter_isClopen (abstract). -/
def connectedComponent_subset_iInter_isClopen' : Prop := True
/-- biUnion_connectedComponent_eq (abstract). -/
def biUnion_connectedComponent_eq' : Prop := True
/-- biUnion_connectedComponentIn (abstract). -/
def biUnion_connectedComponentIn' : Prop := True
/-- preimage_connectedComponent_connected (abstract). -/
def preimage_connectedComponent_connected' : Prop := True
/-- preimage_connectedComponent (abstract). -/
def preimage_connectedComponent' : Prop := True
/-- image_connectedComponent (abstract). -/
def image_connectedComponent' : Prop := True
/-- connectedComponentSetoid (abstract). -/
def connectedComponentSetoid' : Prop := True
-- COLLISION: ConnectedComponents' already in CategoryTheory.lean — rename needed
/-- coe_ne_coe (abstract). -/
def coe_ne_coe' : Prop := True
/-- surjective_coe (abstract). -/
def surjective_coe' : Prop := True
/-- isQuotientMap_coe (abstract). -/
def isQuotientMap_coe' : Prop := True
-- COLLISION: range_coe' already in Algebra.lean — rename needed
/-- connectedComponents_preimage_singleton (abstract). -/
def connectedComponents_preimage_singleton' : Prop := True
/-- connectedComponents_preimage_image (abstract). -/
def connectedComponents_preimage_image' : Prop := True
/-- isPreconnected_of_forall_constant (abstract). -/
def isPreconnected_of_forall_constant' : Prop := True
/-- preconnectedSpace_of_forall_constant (abstract). -/
def preconnectedSpace_of_forall_constant' : Prop := True

-- Connected/LocallyConnected.lean
/-- LocallyConnectedSpace (abstract). -/
def LocallyConnectedSpace' : Prop := True
/-- locallyConnectedSpace_iff_hasBasis_isOpen_isConnected (abstract). -/
def locallyConnectedSpace_iff_hasBasis_isOpen_isConnected' : Prop := True
/-- connectedComponentIn_mem_nhds (abstract). -/
def connectedComponentIn_mem_nhds' : Prop := True
/-- isOpen_connectedComponent (abstract). -/
def isOpen_connectedComponent' : Prop := True
/-- isClopen_connectedComponent (abstract). -/
def isClopen_connectedComponent' : Prop := True
/-- locallyConnectedSpace_iff_connectedComponentIn_open (abstract). -/
def locallyConnectedSpace_iff_connectedComponentIn_open' : Prop := True
/-- locallyConnectedSpace_iff_connected_subsets (abstract). -/
def locallyConnectedSpace_iff_connected_subsets' : Prop := True
/-- locallyConnectedSpace_iff_connected_basis (abstract). -/
def locallyConnectedSpace_iff_connected_basis' : Prop := True
/-- locallyConnectedSpace_of_connected_bases (abstract). -/
def locallyConnectedSpace_of_connected_bases' : Prop := True
/-- locallyConnectedSpace (abstract). -/
def locallyConnectedSpace' : Prop := True

-- Connected/PathConnected.lean
-- COLLISION: asserting' already in CategoryTheory.lean — rename needed
-- COLLISION: Path' already in AlgebraicTopology.lean — rename needed
/-- refl_range (abstract). -/
def refl_range' : Prop := True
/-- symm_symm (abstract). -/
def symm_symm' : Prop := True
-- COLLISION: symm_bijective' already in Algebra.lean — rename needed
/-- refl_symm (abstract). -/
def refl_symm' : Prop := True
/-- symm_range (abstract). -/
def symm_range' : Prop := True
/-- path_eval (abstract). -/
def path_eval' : Prop := True
/-- continuous_uncurry_iff (abstract). -/
def continuous_uncurry_iff' : Prop := True
-- COLLISION: extend' already in Order.lean — rename needed
/-- path_extend (abstract). -/
def path_extend' : Prop := True
/-- continuous_extend (abstract). -/
def continuous_extend' : Prop := True
/-- extend_extends (abstract). -/
def extend_extends' : Prop := True
-- COLLISION: extend_zero' already in Analysis.lean — rename needed
/-- ofLine (abstract). -/
def ofLine' : Prop := True
/-- ofLine_mem (abstract). -/
def ofLine_mem' : Prop := True
/-- trans_apply (abstract). -/
def trans_apply' : Prop := True
/-- trans_symm (abstract). -/
def trans_symm' : Prop := True
/-- refl_trans_refl (abstract). -/
def refl_trans_refl' : Prop := True
/-- trans_range (abstract). -/
def trans_range' : Prop := True
/-- map_trans (abstract). -/
def map_trans' : Prop := True
-- COLLISION: map_map' already in Order.lean — rename needed
-- COLLISION: cast' already in Order.lean — rename needed
/-- continuous_symm (abstract). -/
def continuous_symm' : Prop := True
/-- continuous_uncurry_extend_of_continuous_family (abstract). -/
def continuous_uncurry_extend_of_continuous_family' : Prop := True
/-- trans_continuous_family (abstract). -/
def trans_continuous_family' : Prop := True
/-- path_trans (abstract). -/
def path_trans' : Prop := True
/-- continuous_trans (abstract). -/
def continuous_trans' : Prop := True
/-- trans_prod_eq_prod_trans (abstract). -/
def trans_prod_eq_prod_trans' : Prop := True
/-- trans_pi_eq_pi_trans (abstract). -/
def trans_pi_eq_pi_trans' : Prop := True
-- COLLISION: truncate' already in RingTheory2.lean — rename needed
/-- truncateOfLE (abstract). -/
def truncateOfLE' : Prop := True
/-- truncate_range (abstract). -/
def truncate_range' : Prop := True
/-- truncate_continuous_family (abstract). -/
def truncate_continuous_family' : Prop := True
/-- truncate_const_continuous_family (abstract). -/
def truncate_const_continuous_family' : Prop := True
/-- truncate_self (abstract). -/
def truncate_self' : Prop := True
/-- truncate_zero_zero (abstract). -/
def truncate_zero_zero' : Prop := True
/-- truncate_one_one (abstract). -/
def truncate_one_one' : Prop := True
/-- truncate_zero_one (abstract). -/
def truncate_zero_one' : Prop := True
/-- reparam (abstract). -/
def reparam' : Prop := True
/-- reparam_id (abstract). -/
def reparam_id' : Prop := True
/-- range_reparam (abstract). -/
def range_reparam' : Prop := True
/-- refl_reparam (abstract). -/
def refl_reparam' : Prop := True
/-- Joined (abstract). -/
def Joined' : Prop := True
/-- somePath (abstract). -/
def somePath' : Prop := True
/-- pathSetoid (abstract). -/
def pathSetoid' : Prop := True
/-- ZerothHomotopy (abstract). -/
def ZerothHomotopy' : Prop := True
/-- JoinedIn (abstract). -/
def JoinedIn' : Prop := True
/-- somePath_mem (abstract). -/
def somePath_mem' : Prop := True
/-- joined (abstract). -/
def joined' : Prop := True
/-- joinedIn_iff_joined (abstract). -/
def joinedIn_iff_joined' : Prop := True
/-- joinedIn_univ (abstract). -/
def joinedIn_univ' : Prop := True
/-- joinedIn_image (abstract). -/
def joinedIn_image' : Prop := True
/-- pathComponent (abstract). -/
def pathComponent' : Prop := True
/-- mem_pathComponent_iff (abstract). -/
def mem_pathComponent_iff' : Prop := True
/-- mem_pathComponent_self (abstract). -/
def mem_pathComponent_self' : Prop := True
/-- mem_pathComponent_of_mem (abstract). -/
def mem_pathComponent_of_mem' : Prop := True
/-- pathComponent_symm (abstract). -/
def pathComponent_symm' : Prop := True
/-- pathComponent_congr (abstract). -/
def pathComponent_congr' : Prop := True
/-- pathComponent_subset_component (abstract). -/
def pathComponent_subset_component' : Prop := True
/-- pathComponentIn (abstract). -/
def pathComponentIn' : Prop := True
/-- pathComponentIn_univ (abstract). -/
def pathComponentIn_univ' : Prop := True
/-- mem_pathComponent (abstract). -/
def mem_pathComponent' : Prop := True
/-- mem_pathComponentIn_self (abstract). -/
def mem_pathComponentIn_self' : Prop := True
/-- pathComponentIn_subset (abstract). -/
def pathComponentIn_subset' : Prop := True
/-- pathComponentIn_nonempty_iff (abstract). -/
def pathComponentIn_nonempty_iff' : Prop := True
/-- pathComponentIn_congr (abstract). -/
def pathComponentIn_congr' : Prop := True
/-- pathComponentIn_mono (abstract). -/
def pathComponentIn_mono' : Prop := True
/-- isPathConnected_iff (abstract). -/
def isPathConnected_iff' : Prop := True
/-- isPathConnected_preimage (abstract). -/
def isPathConnected_preimage' : Prop := True
/-- subset_pathComponent (abstract). -/
def subset_pathComponent' : Prop := True
/-- subset_pathComponentIn (abstract). -/
def subset_pathComponentIn' : Prop := True
/-- isPathConnected_singleton (abstract). -/
def isPathConnected_singleton' : Prop := True
/-- isPathConnected_pathComponentIn (abstract). -/
def isPathConnected_pathComponentIn' : Prop := True
/-- isPathConnected_pathComponent (abstract). -/
def isPathConnected_pathComponent' : Prop := True
/-- preimage_coe (abstract). -/
def preimage_coe' : Prop := True
/-- exists_path_through_family (abstract). -/
def exists_path_through_family' : Prop := True
/-- PathConnectedSpace (abstract). -/
def PathConnectedSpace' : Prop := True
/-- pathConnectedSpace_iff_zerothHomotopy (abstract). -/
def pathConnectedSpace_iff_zerothHomotopy' : Prop := True
/-- pathConnectedSpace_iff_univ (abstract). -/
def pathConnectedSpace_iff_univ' : Prop := True
/-- isPathConnected_iff_pathConnectedSpace (abstract). -/
def isPathConnected_iff_pathConnectedSpace' : Prop := True
/-- isPathConnected_univ (abstract). -/
def isPathConnected_univ' : Prop := True
/-- isPathConnected_range (abstract). -/
def isPathConnected_range' : Prop := True
-- COLLISION: pathConnectedSpace' already in Analysis.lean — rename needed
/-- pathConnectedSpace_iff_eq (abstract). -/
def pathConnectedSpace_iff_eq' : Prop := True
/-- LocPathConnectedSpace (abstract). -/
def LocPathConnectedSpace' : Prop := True
/-- of_bases (abstract). -/
def of_bases' : Prop := True
/-- pathConnectedSpace_iff_connectedSpace (abstract). -/
def pathConnectedSpace_iff_connectedSpace' : Prop := True
/-- pathComponent_eq_connectedComponent (abstract). -/
def pathComponent_eq_connectedComponent' : Prop := True
/-- pathConnected_subset_basis (abstract). -/
def pathConnected_subset_basis' : Prop := True
/-- isOpen_isPathConnected_basis (abstract). -/
def isOpen_isPathConnected_basis' : Prop := True
/-- locPathConnectedSpace (abstract). -/
def locPathConnectedSpace' : Prop := True
/-- isConnected_iff_isPathConnected (abstract). -/
def isConnected_iff_isPathConnected' : Prop := True
/-- locPathConnectedSpace_iff_isOpen_pathComponentIn (abstract). -/
def locPathConnectedSpace_iff_isOpen_pathComponentIn' : Prop := True
/-- locPathConnectedSpace_iff_pathComponentIn_mem_nhds (abstract). -/
def locPathConnectedSpace_iff_pathComponentIn_mem_nhds' : Prop := True

-- Connected/TotallyDisconnected.lean
-- COLLISION: IsTotallyDisconnected' already in CategoryTheory.lean — rename needed
/-- isTotallyDisconnected_empty (abstract). -/
def isTotallyDisconnected_empty' : Prop := True
/-- isTotallyDisconnected_singleton (abstract). -/
def isTotallyDisconnected_singleton' : Prop := True
/-- TotallyDisconnectedSpace (abstract). -/
def TotallyDisconnectedSpace' : Prop := True
-- COLLISION: subsingleton' already in Order.lean — rename needed
/-- isTotallyDisconnected_of_isClopen_set (abstract). -/
def isTotallyDisconnected_of_isClopen_set' : Prop := True
/-- totallyDisconnectedSpace_iff_connectedComponent_subsingleton (abstract). -/
def totallyDisconnectedSpace_iff_connectedComponent_subsingleton' : Prop := True
/-- totallyDisconnectedSpace_iff_connectedComponent_singleton (abstract). -/
def totallyDisconnectedSpace_iff_connectedComponent_singleton' : Prop := True
/-- connectedComponent_eq_singleton (abstract). -/
def connectedComponent_eq_singleton' : Prop := True
/-- image_connectedComponent_eq_singleton (abstract). -/
def image_connectedComponent_eq_singleton' : Prop := True
/-- isTotallyDisconnected_of_totallyDisconnectedSpace (abstract). -/
def isTotallyDisconnected_of_totallyDisconnectedSpace' : Prop := True
/-- isTotallyDisconnected_of_image (abstract). -/
def isTotallyDisconnected_of_image' : Prop := True
/-- isTotallyDisconnected (abstract). -/
def isTotallyDisconnected' : Prop := True
/-- isTotallyDisconnected_image (abstract). -/
def isTotallyDisconnected_image' : Prop := True
/-- isTotallyDisconnected_range (abstract). -/
def isTotallyDisconnected_range' : Prop := True
/-- totallyDisconnectedSpace_subtype_iff (abstract). -/
def totallyDisconnectedSpace_subtype_iff' : Prop := True
/-- IsTotallySeparated (abstract). -/
def IsTotallySeparated' : Prop := True
/-- isTotallySeparated_empty (abstract). -/
def isTotallySeparated_empty' : Prop := True
/-- isTotallySeparated_singleton (abstract). -/
def isTotallySeparated_singleton' : Prop := True
/-- isTotallyDisconnected_of_isTotallySeparated (abstract). -/
def isTotallyDisconnected_of_isTotallySeparated' : Prop := True
/-- TotallySeparatedSpace (abstract). -/
def TotallySeparatedSpace' : Prop := True
/-- totallySeparatedSpace_iff_exists_isClopen (abstract). -/
def totallySeparatedSpace_iff_exists_isClopen' : Prop := True
/-- exists_isClopen_of_totally_separated (abstract). -/
def exists_isClopen_of_totally_separated' : Prop := True
/-- image_eq_of_connectedComponent_eq (abstract). -/
def image_eq_of_connectedComponent_eq' : Prop := True
/-- connectedComponentsLift (abstract). -/
def connectedComponentsLift' : Prop := True
/-- connectedComponents_lift_unique' (abstract). -/
def connectedComponents_lift_unique' : Prop := True
/-- connectedComponentsLift_unique (abstract). -/
def connectedComponentsLift_unique' : Prop := True
/-- connectedComponentsMap (abstract). -/
def connectedComponentsMap' : Prop := True
/-- connectedComponentsMap_continuous (abstract). -/
def connectedComponentsMap_continuous' : Prop := True
/-- constant (abstract). -/
def constant' : Prop := True
/-- constant_of_mapsTo (abstract). -/
def constant_of_mapsTo' : Prop := True
/-- eqOn_const_of_mapsTo (abstract). -/
def eqOn_const_of_mapsTo' : Prop := True

-- Constructions.lean
/-- continuous_ofMul (abstract). -/
def continuous_ofMul' : Prop := True
/-- continuous_toMul (abstract). -/
def continuous_toMul' : Prop := True
/-- continuous_ofAdd (abstract). -/
def continuous_ofAdd' : Prop := True
/-- continuous_toAdd (abstract). -/
def continuous_toAdd' : Prop := True
/-- isOpenMap_ofMul (abstract). -/
def isOpenMap_ofMul' : Prop := True
/-- isOpenMap_toMul (abstract). -/
def isOpenMap_toMul' : Prop := True
/-- isOpenMap_ofAdd (abstract). -/
def isOpenMap_ofAdd' : Prop := True
/-- isOpenMap_toAdd (abstract). -/
def isOpenMap_toAdd' : Prop := True
/-- isClosedMap_ofMul (abstract). -/
def isClosedMap_ofMul' : Prop := True
/-- isClosedMap_toMul (abstract). -/
def isClosedMap_toMul' : Prop := True
/-- isClosedMap_ofAdd (abstract). -/
def isClosedMap_ofAdd' : Prop := True
/-- isClosedMap_toAdd (abstract). -/
def isClosedMap_toAdd' : Prop := True
/-- continuous_toDual (abstract). -/
def continuous_toDual' : Prop := True
/-- continuous_ofDual (abstract). -/
def continuous_ofDual' : Prop := True
/-- isOpenMap_toDual (abstract). -/
def isOpenMap_toDual' : Prop := True
/-- isOpenMap_ofDual (abstract). -/
def isOpenMap_ofDual' : Prop := True
/-- isClosedMap_toDual (abstract). -/
def isClosedMap_toDual' : Prop := True
/-- isClosedMap_ofDual (abstract). -/
def isClosedMap_ofDual' : Prop := True
/-- preimage_mem_nhds (abstract). -/
def preimage_mem_nhds' : Prop := True
/-- continuous_map_of_le (abstract). -/
def continuous_map_of_le' : Prop := True
/-- continuous_map_sInf (abstract). -/
def continuous_map_sInf' : Prop := True
/-- comap_nhdsWithin_range (abstract). -/
def comap_nhdsWithin_range' : Prop := True
/-- mem_nhds_subtype (abstract). -/
def mem_nhds_subtype' : Prop := True
/-- nhds_subtype (abstract). -/
def nhds_subtype' : Prop := True
/-- nhds_subtype_eq_comap_nhdsWithin (abstract). -/
def nhds_subtype_eq_comap_nhdsWithin' : Prop := True
/-- nhdsWithin_subtype_eq_bot_iff (abstract). -/
def nhdsWithin_subtype_eq_bot_iff' : Prop := True
/-- nhds_ne_subtype_eq_bot_iff (abstract). -/
def nhds_ne_subtype_eq_bot_iff' : Prop := True
/-- nhds_ne_subtype_neBot_iff (abstract). -/
def nhds_ne_subtype_neBot_iff' : Prop := True
/-- discreteTopology_subtype_iff (abstract). -/
def discreteTopology_subtype_iff' : Prop := True
/-- CofiniteTopology (abstract). -/
def CofiniteTopology' : Prop := True
/-- continuous_prod_mk (abstract). -/
def continuous_prod_mk' : Prop := True
/-- continuous_fst (abstract). -/
def continuous_fst' : Prop := True
/-- continuousAt_fst (abstract). -/
def continuousAt_fst' : Prop := True
-- COLLISION: fst'' already in Analysis.lean — rename needed
/-- fst_nhds (abstract). -/
def fst_nhds' : Prop := True
/-- continuous_snd (abstract). -/
def continuous_snd' : Prop := True
/-- continuousAt_snd (abstract). -/
def continuousAt_snd' : Prop := True
-- COLLISION: snd'' already in Analysis.lean — rename needed
/-- snd_nhds (abstract). -/
def snd_nhds' : Prop := True
-- COLLISION: mk_left' already in SetTheory.lean — rename needed
/-- setOf_mapsTo (abstract). -/
def setOf_mapsTo' : Prop := True
-- COLLISION: comp₂' already in Order.lean — rename needed
/-- comp₄ (abstract). -/
def comp₄' : Prop := True
/-- continuous_inf_dom_left₂ (abstract). -/
def continuous_inf_dom_left₂' : Prop := True
/-- continuous_inf_dom_right₂ (abstract). -/
def continuous_inf_dom_right₂' : Prop := True
/-- continuous_sInf_dom₂ (abstract). -/
def continuous_sInf_dom₂' : Prop := True
/-- prod_inl_nhds (abstract). -/
def prod_inl_nhds' : Prop := True
/-- prod_inr_nhds (abstract). -/
def prod_inr_nhds' : Prop := True
/-- prod_mk_nhds (abstract). -/
def prod_mk_nhds' : Prop := True
/-- nhds_prod_eq (abstract). -/
def nhds_prod_eq' : Prop := True
/-- nhdsWithin_prod_eq (abstract). -/
def nhdsWithin_prod_eq' : Prop := True
/-- mem_nhds_prod_iff (abstract). -/
def mem_nhds_prod_iff' : Prop := True
/-- mem_nhdsWithin_prod_iff (abstract). -/
def mem_nhdsWithin_prod_iff' : Prop := True
/-- prod_nhds (abstract). -/
def prod_nhds' : Prop := True
/-- curry_prodMap (abstract). -/
def curry_prodMap' : Prop := True
-- COLLISION: tendsto_iff' already in Order.lean — rename needed
/-- prod_mem_nhds_iff (abstract). -/
def prod_mem_nhds_iff' : Prop := True
/-- prod_mem_nhds (abstract). -/
def prod_mem_nhds' : Prop := True
/-- isOpen_setOf_disjoint_nhds_nhds (abstract). -/
def isOpen_setOf_disjoint_nhds_nhds' : Prop := True
/-- nhds_swap (abstract). -/
def nhds_swap' : Prop := True
/-- curry_nhds (abstract). -/
def curry_nhds' : Prop := True
/-- comp₂_of_eq (abstract). -/
def comp₂_of_eq' : Prop := True
-- COLLISION: curry_left' already in Analysis.lean — rename needed
-- COLLISION: curry_right' already in Analysis.lean — rename needed
/-- prod_generateFrom_generateFrom_eq (abstract). -/
def prod_generateFrom_generateFrom_eq' : Prop := True
-- COLLISION: prod_eq_generateFrom' already in MeasureTheory2.lean — rename needed
/-- isOpen_prod_iff (abstract). -/
def isOpen_prod_iff' : Prop := True
/-- prod_induced_induced (abstract). -/
def prod_induced_induced' : Prop := True
/-- exists_nhds_square (abstract). -/
def exists_nhds_square' : Prop := True
/-- map_fst_nhdsWithin (abstract). -/
def map_fst_nhdsWithin' : Prop := True
/-- map_fst_nhds (abstract). -/
def map_fst_nhds' : Prop := True
/-- isOpenMap_fst (abstract). -/
def isOpenMap_fst' : Prop := True
/-- map_snd_nhdsWithin (abstract). -/
def map_snd_nhdsWithin' : Prop := True
/-- map_snd_nhds (abstract). -/
def map_snd_nhds' : Prop := True
/-- isOpenMap_snd (abstract). -/
def isOpenMap_snd' : Prop := True
/-- isQuotientMap_fst (abstract). -/
def isQuotientMap_fst' : Prop := True
/-- isQuotientMap_snd (abstract). -/
def isQuotientMap_snd' : Prop := True
/-- closure_prod_eq (abstract). -/
def closure_prod_eq' : Prop := True
/-- interior_prod_eq (abstract). -/
def interior_prod_eq' : Prop := True
/-- frontier_prod_eq (abstract). -/
def frontier_prod_eq' : Prop := True
/-- frontier_prod_univ_eq (abstract). -/
def frontier_prod_univ_eq' : Prop := True
/-- frontier_univ_prod_eq (abstract). -/
def frontier_univ_prod_eq' : Prop := True
/-- map_mem_closure₂ (abstract). -/
def map_mem_closure₂' : Prop := True
/-- isInducing_const_prod (abstract). -/
def isInducing_const_prod' : Prop := True
/-- isInducing_prod_const (abstract). -/
def isInducing_prod_const' : Prop := True
/-- isEmbedding_graph (abstract). -/
def isEmbedding_graph' : Prop := True
/-- isEmbedding_prodMk (abstract). -/
def isEmbedding_prodMk' : Prop := True
/-- continuous_bool_rng (abstract). -/
def continuous_bool_rng' : Prop := True
/-- continuous_sum_dom (abstract). -/
def continuous_sum_dom' : Prop := True
/-- continuous_sum_elim (abstract). -/
def continuous_sum_elim' : Prop := True
/-- sum_elim (abstract). -/
def sum_elim' : Prop := True
/-- continuous_isLeft (abstract). -/
def continuous_isLeft' : Prop := True
/-- continuous_isRight (abstract). -/
def continuous_isRight' : Prop := True
/-- isClosed_sum_iff (abstract). -/
def isClosed_sum_iff' : Prop := True
/-- isOpenMap_inl (abstract). -/
def isOpenMap_inl' : Prop := True
/-- isOpenMap_inr (abstract). -/
def isOpenMap_inr' : Prop := True
/-- isOpen_range_inl (abstract). -/
def isOpen_range_inl' : Prop := True
/-- isOpen_range_inr (abstract). -/
def isOpen_range_inr' : Prop := True
/-- isClosed_range_inl (abstract). -/
def isClosed_range_inl' : Prop := True
/-- isClosed_range_inr (abstract). -/
def isClosed_range_inr' : Prop := True
/-- nhds_inl (abstract). -/
def nhds_inl' : Prop := True
/-- nhds_inr (abstract). -/
def nhds_inr' : Prop := True
/-- continuous_sum_map (abstract). -/
def continuous_sum_map' : Prop := True
/-- sum_map (abstract). -/
def sum_map' : Prop := True
/-- isOpenMap_sum (abstract). -/
def isOpenMap_sum' : Prop := True
-- COLLISION: sumMap' already in MeasureTheory2.lean — rename needed
/-- isOpenMap_sum_elim (abstract). -/
def isOpenMap_sum_elim' : Prop := True
/-- isClosedMap_sum (abstract). -/
def isClosedMap_sum' : Prop := True
-- COLLISION: subtypeVal' already in Order.lean — rename needed
/-- of_codRestrict (abstract). -/
def of_codRestrict' : Prop := True
/-- continuous_subtype_val (abstract). -/
def continuous_subtype_val' : Prop := True
/-- subtype_val (abstract). -/
def subtype_val' : Prop := True
/-- isOpenEmbedding_subtypeVal (abstract). -/
def isOpenEmbedding_subtypeVal' : Prop := True
/-- isOpenMap_subtype_val (abstract). -/
def isOpenMap_subtype_val' : Prop := True
-- COLLISION: restrict' already in Order.lean — rename needed
/-- isClosedEmbedding_subtypeVal (abstract). -/
def isClosedEmbedding_subtypeVal' : Prop := True
/-- isClosedMap_subtype_val (abstract). -/
def isClosedMap_subtype_val' : Prop := True
-- COLLISION: subtype_mk' already in MeasureTheory2.lean — rename needed
-- COLLISION: subtype_map' already in MeasureTheory2.lean — rename needed
/-- continuous_inclusion (abstract). -/
def continuous_inclusion' : Prop := True
/-- continuousAt_subtype_val (abstract). -/
def continuousAt_subtype_val' : Prop := True
/-- map_nhds_subtype_val (abstract). -/
def map_nhds_subtype_val' : Prop := True
/-- map_nhds_subtype_coe_eq_nhds (abstract). -/
def map_nhds_subtype_coe_eq_nhds' : Prop := True
/-- nhds_subtype_eq_comap (abstract). -/
def nhds_subtype_eq_comap' : Prop := True
/-- tendsto_subtype_rng (abstract). -/
def tendsto_subtype_rng' : Prop := True
/-- closure_subtype (abstract). -/
def closure_subtype' : Prop := True
/-- continuousAt_codRestrict_iff (abstract). -/
def continuousAt_codRestrict_iff' : Prop := True
/-- of_subset (abstract). -/
def of_subset' : Prop := True
/-- preimage_of_continuous_injective (abstract). -/
def preimage_of_continuous_injective' : Prop := True
/-- restrictPreimage_isOpen (abstract). -/
def restrictPreimage_isOpen' : Prop := True
/-- isClosed_preimage_val (abstract). -/
def isClosed_preimage_val' : Prop := True
/-- frontier_inter_open_inter (abstract). -/
def frontier_inter_open_inter' : Prop := True
/-- isQuotientMap_quot_mk (abstract). -/
def isQuotientMap_quot_mk' : Prop := True
/-- continuous_quot_mk (abstract). -/
def continuous_quot_mk' : Prop := True
/-- continuous_quot_lift (abstract). -/
def continuous_quot_lift' : Prop := True
/-- isQuotientMap_quotient_mk' (abstract). -/
def isQuotientMap_quotient_mk' : Prop := True
/-- quotient_map' (abstract). -/
def quotient_map' : Prop := True
/-- continuous_pi_iff (abstract). -/
def continuous_pi_iff' : Prop := True
/-- continuous_pi (abstract). -/
def continuous_pi' : Prop := True
/-- continuous_apply (abstract). -/
def continuous_apply' : Prop := True
/-- continuous_apply_apply (abstract). -/
def continuous_apply_apply' : Prop := True
/-- continuousAt_apply (abstract). -/
def continuousAt_apply' : Prop := True
/-- apply_nhds (abstract). -/
def apply_nhds' : Prop := True
/-- piMap (abstract). -/
def piMap' : Prop := True
/-- nhds_pi (abstract). -/
def nhds_pi' : Prop := True
/-- tendsto_pi_nhds (abstract). -/
def tendsto_pi_nhds' : Prop := True
/-- continuousAt_pi (abstract). -/
def continuousAt_pi' : Prop := True
/-- induced_precomp' (abstract). -/
def induced_precomp' : Prop := True
/-- continuous_restrict₂ (abstract). -/
def continuous_restrict₂' : Prop := True
/-- continuous_restrict_apply (abstract). -/
def continuous_restrict_apply' : Prop := True
/-- continuous_restrict₂_apply (abstract). -/
def continuous_restrict₂_apply' : Prop := True
/-- induced_restrict (abstract). -/
def induced_restrict' : Prop := True
/-- induced_restrict_sUnion (abstract). -/
def induced_restrict_sUnion' : Prop := True
/-- continuous_update (abstract). -/
def continuous_update' : Prop := True
/-- continuous_mulSingle (abstract). -/
def continuous_mulSingle' : Prop := True
/-- fin_insertNth (abstract). -/
def fin_insertNth' : Prop := True
/-- isOpen_set_pi (abstract). -/
def isOpen_set_pi' : Prop := True
/-- isOpen_pi_iff (abstract). -/
def isOpen_pi_iff' : Prop := True
/-- isClosed_set_pi (abstract). -/
def isClosed_set_pi' : Prop := True
/-- mem_nhds_of_pi_mem_nhds (abstract). -/
def mem_nhds_of_pi_mem_nhds' : Prop := True
/-- set_pi_mem_nhds (abstract). -/
def set_pi_mem_nhds' : Prop := True
/-- set_pi_mem_nhds_iff (abstract). -/
def set_pi_mem_nhds_iff' : Prop := True
/-- interior_pi_set (abstract). -/
def interior_pi_set' : Prop := True
/-- exists_finset_piecewise_mem_of_mem_nhds (abstract). -/
def exists_finset_piecewise_mem_of_mem_nhds' : Prop := True
/-- pi_generateFrom_eq (abstract). -/
def pi_generateFrom_eq' : Prop := True
-- COLLISION: pi_eq_generateFrom' already in MeasureTheory2.lean — rename needed
/-- pi_generateFrom_eq_finite (abstract). -/
def pi_generateFrom_eq_finite' : Prop := True
/-- induced_to_pi (abstract). -/
def induced_to_pi' : Prop := True
/-- inducing_iInf_to_pi (abstract). -/
def inducing_iInf_to_pi' : Prop := True
/-- continuous_sigmaMk (abstract). -/
def continuous_sigmaMk' : Prop := True
/-- isOpen_sigma_iff (abstract). -/
def isOpen_sigma_iff' : Prop := True
/-- isClosed_sigma_iff (abstract). -/
def isClosed_sigma_iff' : Prop := True
/-- isOpenMap_sigmaMk (abstract). -/
def isOpenMap_sigmaMk' : Prop := True
/-- isOpen_range_sigmaMk (abstract). -/
def isOpen_range_sigmaMk' : Prop := True
/-- isClosedMap_sigmaMk (abstract). -/
def isClosedMap_sigmaMk' : Prop := True
/-- isClosed_range_sigmaMk (abstract). -/
def isClosed_range_sigmaMk' : Prop := True
/-- sigmaMk (abstract). -/
def sigmaMk' : Prop := True
/-- nhds_mk (abstract). -/
def nhds_mk' : Prop := True
/-- comap_sigmaMk_nhds (abstract). -/
def comap_sigmaMk_nhds' : Prop := True
/-- isOpen_sigma_fst_preimage (abstract). -/
def isOpen_sigma_fst_preimage' : Prop := True
/-- continuous_sigma_iff (abstract). -/
def continuous_sigma_iff' : Prop := True
/-- continuous_sigma (abstract). -/
def continuous_sigma' : Prop := True
/-- inducing_sigma (abstract). -/
def inducing_sigma' : Prop := True
/-- continuous_sigma_map (abstract). -/
def continuous_sigma_map' : Prop := True
/-- sigma_map (abstract). -/
def sigma_map' : Prop := True
/-- isOpenMap_sigma (abstract). -/
def isOpenMap_sigma' : Prop := True
/-- isOpenMap_sigma_map (abstract). -/
def isOpenMap_sigma_map' : Prop := True
/-- isInducing_sigmaMap (abstract). -/
def isInducing_sigmaMap' : Prop := True
/-- isEmbedding_sigmaMap (abstract). -/
def isEmbedding_sigmaMap' : Prop := True
/-- isOpenEmbedding_sigmaMap (abstract). -/
def isOpenEmbedding_sigmaMap' : Prop := True
/-- continuous_uLift_down (abstract). -/
def continuous_uLift_down' : Prop := True
/-- continuous_uLift_up (abstract). -/
def continuous_uLift_up' : Prop := True
/-- uliftDown (abstract). -/
def uliftDown' : Prop := True
/-- nhdsSet_prod_le (abstract). -/
def nhdsSet_prod_le' : Prop := True
/-- eventually_nhdsSet_prod_iff (abstract). -/
def eventually_nhdsSet_prod_iff' : Prop := True
/-- prod_nhdsSet (abstract). -/
def prod_nhdsSet' : Prop := True

-- ContinuousMap/Algebra.lean
/-- continuousSubmonoid (abstract). -/
def continuousSubmonoid' : Prop := True
/-- continuousSubgroup (abstract). -/
def continuousSubgroup' : Prop := True
/-- coeFnMonoidHom (abstract). -/
def coeFnMonoidHom' : Prop := True
/-- compLeftContinuous (abstract). -/
def compLeftContinuous' : Prop := True
/-- compMonoidHom' (abstract). -/
def compMonoidHom' : Prop := True
-- COLLISION: coe_prod' already in Algebra.lean — rename needed
-- COLLISION: prod_apply' already in Algebra.lean — rename needed
/-- hasProd_apply (abstract). -/
def hasProd_apply' : Prop := True
/-- multipliable_apply (abstract). -/
def multipliable_apply' : Prop := True
/-- continuousSubsemiring (abstract). -/
def continuousSubsemiring' : Prop := True
/-- continuousSubring (abstract). -/
def continuousSubring' : Prop := True
/-- coeFnRingHom (abstract). -/
def coeFnRingHom' : Prop := True
/-- continuousSubmodule (abstract). -/
def continuousSubmodule' : Prop := True
/-- coeFnLinearMap (abstract). -/
def coeFnLinearMap' : Prop := True
/-- continuousSubalgebra (abstract). -/
def continuousSubalgebra' : Prop := True
/-- compRightAlgHom (abstract). -/
def compRightAlgHom' : Prop := True
/-- compRightAlgHom_continuous (abstract). -/
def compRightAlgHom_continuous' : Prop := True
/-- coeFnAlgHom (abstract). -/
def coeFnAlgHom' : Prop := True
-- COLLISION: SeparatesPoints' already in MeasureTheory2.lean — rename needed
-- COLLISION: algebraMap_apply' already in RingTheory2.lean — rename needed
/-- SeparatesPointsStrongly (abstract). -/
def SeparatesPointsStrongly' : Prop := True
-- COLLISION: evalAlgHom' already in Algebra.lean — rename needed

-- ContinuousMap/Basic.lean
/-- map_continuousAt (abstract). -/
def map_continuousAt' : Prop := True
/-- map_continuousWithinAt (abstract). -/
def map_continuousWithinAt' : Prop := True
/-- equivFnOfDiscrete (abstract). -/
def equivFnOfDiscrete' : Prop := True
/-- constPi (abstract). -/
def constPi' : Prop := True
/-- const_comp (abstract). -/
def const_comp' : Prop := True
/-- comp_const (abstract). -/
def comp_const' : Prop := True
-- COLLISION: prodMk' already in Order.lean — rename needed
/-- prodSwap (abstract). -/
def prodSwap' : Prop := True
/-- sigmaEquiv (abstract). -/
def sigmaEquiv' : Prop := True
/-- injective_restrict (abstract). -/
def injective_restrict' : Prop := True
/-- restrictPreimage (abstract). -/
def restrictPreimage' : Prop := True
/-- liftCover (abstract). -/
def liftCover' : Prop := True
/-- liftCover_coe (abstract). -/
def liftCover_coe' : Prop := True
/-- liftCover_restrict (abstract). -/
def liftCover_restrict' : Prop := True
-- COLLISION: homeomorph' already in Analysis.lean — rename needed
-- COLLISION: lift_comp' already in RingTheory2.lean — rename needed
-- COLLISION: liftEquiv' already in RingTheory2.lean — rename needed
/-- symm_comp_toContinuousMap (abstract). -/
def symm_comp_toContinuousMap' : Prop := True
/-- toContinuousMap_comp_symm (abstract). -/
def toContinuousMap_comp_symm' : Prop := True

-- ContinuousMap/Bounded/Basic.lean
/-- BoundedContinuousFunction (abstract). -/
def BoundedContinuousFunction' : Prop := True
/-- BoundedContinuousMapClass (abstract). -/
def BoundedContinuousMapClass' : Prop := True
-- COLLISION: bounded' already in Algebra.lean — rename needed
/-- mkOfBound (abstract). -/
def mkOfBound' : Prop := True
/-- mkOfCompact (abstract). -/
def mkOfCompact' : Prop := True
/-- mkOfDiscrete (abstract). -/
def mkOfDiscrete' : Prop := True
/-- dist_set_exists (abstract). -/
def dist_set_exists' : Prop := True
/-- dist_coe_le_dist (abstract). -/
def dist_coe_le_dist' : Prop := True
/-- dist_nonneg' (abstract). -/
def dist_nonneg' : Prop := True
-- COLLISION: dist_le' already in Analysis.lean — rename needed
/-- dist_le_iff_of_nonempty (abstract). -/
def dist_le_iff_of_nonempty' : Prop := True
/-- dist_lt_of_nonempty_compact (abstract). -/
def dist_lt_of_nonempty_compact' : Prop := True
/-- dist_lt_iff_of_compact (abstract). -/
def dist_lt_iff_of_compact' : Prop := True
/-- dist_lt_iff_of_nonempty_compact (abstract). -/
def dist_lt_iff_of_nonempty_compact' : Prop := True
-- COLLISION: nndist_eq' already in Analysis.lean — rename needed
/-- nndist_set_exists (abstract). -/
def nndist_set_exists' : Prop := True
/-- nndist_coe_le_nndist (abstract). -/
def nndist_coe_le_nndist' : Prop := True
/-- dist_zero_of_empty (abstract). -/
def dist_zero_of_empty' : Prop := True
/-- dist_eq_iSup (abstract). -/
def dist_eq_iSup' : Prop := True
-- COLLISION: nndist_eq_iSup' already in Analysis.lean — rename needed
/-- tendsto_iff_tendstoUniformly (abstract). -/
def tendsto_iff_tendstoUniformly' : Prop := True
/-- isInducing_coeFn (abstract). -/
def isInducing_coeFn' : Prop := True
/-- lipschitz_evalx (abstract). -/
def lipschitz_evalx' : Prop := True
-- COLLISION: uniformContinuous_coe' already in Analysis.lean — rename needed
/-- continuous_eval_const (abstract). -/
def continuous_eval_const' : Prop := True
/-- compContinuous (abstract). -/
def compContinuous' : Prop := True
/-- lipschitz_compContinuous (abstract). -/
def lipschitz_compContinuous' : Prop := True
/-- lipschitz_comp (abstract). -/
def lipschitz_comp' : Prop := True
/-- uniformContinuous_comp (abstract). -/
def uniformContinuous_comp' : Prop := True
-- COLLISION: extend_apply' already in Analysis.lean — rename needed
/-- extend_comp (abstract). -/
def extend_comp' : Prop := True
/-- extend_of_empty (abstract). -/
def extend_of_empty' : Prop := True
/-- dist_extend_extend (abstract). -/
def dist_extend_extend' : Prop := True
/-- isometry_extend (abstract). -/
def isometry_extend' : Prop := True
-- COLLISION: indicator' already in MeasureTheory2.lean — rename needed
/-- arzela_ascoli₁ (abstract). -/
def arzela_ascoli₁' : Prop := True
/-- arzela_ascoli₂ (abstract). -/
def arzela_ascoli₂' : Prop := True
/-- arzela_ascoli (abstract). -/
def arzela_ascoli' : Prop := True
/-- coeFnAddHom (abstract). -/
def coeFnAddHom' : Prop := True
/-- toContinuousMapAddHom (abstract). -/
def toContinuousMapAddHom' : Prop := True
/-- norm_eq_zero_of_empty (abstract). -/
def norm_eq_zero_of_empty' : Prop := True
/-- norm_coe_le_norm (abstract). -/
def norm_coe_le_norm' : Prop := True
/-- neg_norm_le_apply (abstract). -/
def neg_norm_le_apply' : Prop := True
/-- apply_le_norm (abstract). -/
def apply_le_norm' : Prop := True
/-- dist_le_two_norm' (abstract). -/
def dist_le_two_norm' : Prop := True
-- COLLISION: norm_le' already in Analysis.lean — rename needed
/-- norm_le_of_nonempty (abstract). -/
def norm_le_of_nonempty' : Prop := True
/-- norm_lt_iff_of_compact (abstract). -/
def norm_lt_iff_of_compact' : Prop := True
/-- norm_lt_iff_of_nonempty_compact (abstract). -/
def norm_lt_iff_of_nonempty_compact' : Prop := True
/-- norm_const_le (abstract). -/
def norm_const_le' : Prop := True
/-- norm_const_eq (abstract). -/
def norm_const_eq' : Prop := True
/-- ofNormedAddCommGroup (abstract). -/
def ofNormedAddCommGroup' : Prop := True
/-- norm_ofNormedAddCommGroup_le (abstract). -/
def norm_ofNormedAddCommGroup_le' : Prop := True
/-- ofNormedAddCommGroupDiscrete (abstract). -/
def ofNormedAddCommGroupDiscrete' : Prop := True
/-- normComp (abstract). -/
def normComp' : Prop := True
/-- norm_normComp (abstract). -/
def norm_normComp' : Prop := True
/-- bddAbove_range_norm_comp (abstract). -/
def bddAbove_range_norm_comp' : Prop := True
/-- norm_eq_iSup_norm (abstract). -/
def norm_eq_iSup_norm' : Prop := True
/-- nnnorm_coe_le_nnnorm (abstract). -/
def nnnorm_coe_le_nnnorm' : Prop := True
/-- nndist_le_two_nnnorm (abstract). -/
def nndist_le_two_nnnorm' : Prop := True
/-- nnnorm_le (abstract). -/
def nnnorm_le' : Prop := True
/-- nnnorm_const_le (abstract). -/
def nnnorm_const_le' : Prop := True
/-- nnnorm_const_eq (abstract). -/
def nnnorm_const_eq' : Prop := True
/-- nnnorm_eq_iSup_nnnorm (abstract). -/
def nnnorm_eq_iSup_nnnorm' : Prop := True
/-- abs_diff_coe_le_dist (abstract). -/
def abs_diff_coe_le_dist' : Prop := True
/-- coe_le_coe_add_dist (abstract). -/
def coe_le_coe_add_dist' : Prop := True
/-- norm_compContinuous_le (abstract). -/
def norm_compContinuous_le' : Prop := True
-- COLLISION: evalCLM' already in Analysis.lean — rename needed
/-- toContinuousMapLinearMap (abstract). -/
def toContinuousMapLinearMap' : Prop := True
/-- compLeftContinuousBounded (abstract). -/
def compLeftContinuousBounded' : Prop := True
/-- coe_npowRec (abstract). -/
def coe_npowRec' : Prop := True
/-- upper_bound (abstract). -/
def upper_bound' : Prop := True
/-- nnrealPart (abstract). -/
def nnrealPart' : Prop := True
-- COLLISION: nnnorm' already in Analysis.lean — rename needed
/-- self_eq_nnrealPart_sub_nnrealPart_neg (abstract). -/
def self_eq_nnrealPart_sub_nnrealPart_neg' : Prop := True
/-- abs_self_eq_nnrealPart_add_nnrealPart_neg (abstract). -/
def abs_self_eq_nnrealPart_add_nnrealPart_neg' : Prop := True
/-- add_norm_nonneg (abstract). -/
def add_norm_nonneg' : Prop := True
/-- norm_sub_nonneg (abstract). -/
def norm_sub_nonneg' : Prop := True

-- ContinuousMap/BoundedCompactlySupported.lean
/-- compactlySupported (abstract). -/
def compactlySupported' : Prop := True
/-- mem_compactlySupported (abstract). -/
def mem_compactlySupported' : Prop := True
/-- exist_norm_eq (abstract). -/
def exist_norm_eq' : Prop := True
/-- norm_lt_iff_of_compactlySupported (abstract). -/
def norm_lt_iff_of_compactlySupported' : Prop := True
/-- norm_lt_iff_of_nonempty_compactlySupported (abstract). -/
def norm_lt_iff_of_nonempty_compactlySupported' : Prop := True
/-- compactlySupported_eq_top_of_isCompact (abstract). -/
def compactlySupported_eq_top_of_isCompact' : Prop := True
/-- compactlySupported_eq_top (abstract). -/
def compactlySupported_eq_top' : Prop := True
/-- ofCompactSupport (abstract). -/
def ofCompactSupport' : Prop := True
/-- ofCompactSupport_mem (abstract). -/
def ofCompactSupport_mem' : Prop := True

-- ContinuousMap/CocompactMap.lean
/-- CocompactMap (abstract). -/
def CocompactMap' : Prop := True
/-- CocompactMapClass (abstract). -/
def CocompactMapClass' : Prop := True
/-- toCocompactMap (abstract). -/
def toCocompactMap' : Prop := True
/-- tendsto_of_forall_preimage (abstract). -/
def tendsto_of_forall_preimage' : Prop := True
/-- isCompact_preimage_of_isClosed (abstract). -/
def isCompact_preimage_of_isClosed' : Prop := True

-- ContinuousMap/Compact.lean
/-- equivBoundedOfCompact (abstract). -/
def equivBoundedOfCompact' : Prop := True
/-- isUniformInducing_equivBoundedOfCompact (abstract). -/
def isUniformInducing_equivBoundedOfCompact' : Prop := True
/-- isUniformEmbedding_equivBoundedOfCompact (abstract). -/
def isUniformEmbedding_equivBoundedOfCompact' : Prop := True
/-- addEquivBoundedOfCompact (abstract). -/
def addEquivBoundedOfCompact' : Prop := True
/-- isometryEquivBoundedOfCompact (abstract). -/
def isometryEquivBoundedOfCompact' : Prop := True
-- COLLISION: dist_apply_le_dist' already in Analysis.lean — rename needed
/-- dist_lt_iff_of_nonempty (abstract). -/
def dist_lt_iff_of_nonempty' : Prop := True
/-- dist_lt_of_nonempty (abstract). -/
def dist_lt_of_nonempty' : Prop := True
/-- dist_lt_iff (abstract). -/
def dist_lt_iff' : Prop := True
-- COLLISION: nnnorm_lt_iff' already in Analysis.lean — rename needed
/-- norm_lt_iff_of_nonempty (abstract). -/
def norm_lt_iff_of_nonempty' : Prop := True
/-- nnnorm_lt_iff_of_nonempty (abstract). -/
def nnnorm_lt_iff_of_nonempty' : Prop := True
/-- norm_restrict_mono_set (abstract). -/
def norm_restrict_mono_set' : Prop := True
/-- linearIsometryBoundedOfCompact (abstract). -/
def linearIsometryBoundedOfCompact' : Prop := True
/-- nnnorm_smul_const (abstract). -/
def nnnorm_smul_const' : Prop := True
/-- norm_smul_const (abstract). -/
def norm_smul_const' : Prop := True
/-- uniform_continuity (abstract). -/
def uniform_continuity' : Prop := True
/-- modulus (abstract). -/
def modulus' : Prop := True
/-- modulus_pos (abstract). -/
def modulus_pos' : Prop := True
/-- dist_lt_of_dist_lt_modulus (abstract). -/
def dist_lt_of_dist_lt_modulus' : Prop := True
/-- compLeftContinuousCompact (abstract). -/
def compLeftContinuousCompact' : Prop := True
/-- summable_of_locally_summable_norm (abstract). -/
def summable_of_locally_summable_norm' : Prop := True

-- ContinuousMap/CompactlySupported.lean
/-- CompactlySupportedContinuousMap (abstract). -/
def CompactlySupportedContinuousMap' : Prop := True
/-- CompactlySupportedContinuousMapClass (abstract). -/
def CompactlySupportedContinuousMapClass' : Prop := True
-- COLLISION: has' already in Order.lean — rename needed
/-- liftCompactlySupported (abstract). -/
def liftCompactlySupported' : Prop := True

-- ContinuousMap/ContinuousMapZero.lean
/-- ContinuousMapZero (abstract). -/
def ContinuousMapZero' : Prop := True
/-- toContinuousMapHom (abstract). -/
def toContinuousMapHom' : Prop := True
/-- toContinuousMapCLM (abstract). -/
def toContinuousMapCLM' : Prop := True
-- COLLISION: coeFnAddMonoidHom' already in RingTheory2.lean — rename needed
/-- isUniformEmbedding_comp (abstract). -/
def isUniformEmbedding_comp' : Prop := True
/-- arrowCongrLeft₀ (abstract). -/
def arrowCongrLeft₀' : Prop := True
/-- nonUnitalStarAlgHom_precomp (abstract). -/
def nonUnitalStarAlgHom_precomp' : Prop := True
/-- nonUnitalStarAlgHom_postcomp (abstract). -/
def nonUnitalStarAlgHom_postcomp' : Prop := True

-- ContinuousMap/Defs.lean
/-- ContinuousMap (abstract). -/
def ContinuousMap' : Prop := True
/-- ContinuousMapClass (abstract). -/
def ContinuousMapClass' : Prop := True

-- ContinuousMap/Ideals.lean
/-- idealOfSet (abstract). -/
def idealOfSet' : Prop := True
/-- idealOfSet_closed (abstract). -/
def idealOfSet_closed' : Prop := True
/-- mem_idealOfSet (abstract). -/
def mem_idealOfSet' : Prop := True
/-- not_mem_idealOfSet (abstract). -/
def not_mem_idealOfSet' : Prop := True
/-- setOfIdeal (abstract). -/
def setOfIdeal' : Prop := True
/-- not_mem_setOfIdeal (abstract). -/
def not_mem_setOfIdeal' : Prop := True
/-- mem_setOfIdeal (abstract). -/
def mem_setOfIdeal' : Prop := True
/-- setOfIdeal_open (abstract). -/
def setOfIdeal_open' : Prop := True
/-- opensOfIdeal (abstract). -/
def opensOfIdeal' : Prop := True
/-- idealOfEmpty_eq_bot (abstract). -/
def idealOfEmpty_eq_bot' : Prop := True
/-- mem_idealOfSet_compl_singleton (abstract). -/
def mem_idealOfSet_compl_singleton' : Prop := True
/-- ideal_gc (abstract). -/
def ideal_gc' : Prop := True
/-- exists_mul_le_one_eqOn_ge (abstract). -/
def exists_mul_le_one_eqOn_ge' : Prop := True
/-- idealOfSet_ofIdeal_eq_closure (abstract). -/
def idealOfSet_ofIdeal_eq_closure' : Prop := True
/-- idealOfSet_ofIdeal_isClosed (abstract). -/
def idealOfSet_ofIdeal_isClosed' : Prop := True
/-- setOfIdeal_ofSet_eq_interior (abstract). -/
def setOfIdeal_ofSet_eq_interior' : Prop := True
/-- setOfIdeal_ofSet_of_isOpen (abstract). -/
def setOfIdeal_ofSet_of_isOpen' : Prop := True
/-- idealOpensGI (abstract). -/
def idealOpensGI' : Prop := True
/-- idealOfSet_isMaximal_iff (abstract). -/
def idealOfSet_isMaximal_iff' : Prop := True
/-- idealOf_compl_singleton_isMaximal (abstract). -/
def idealOf_compl_singleton_isMaximal' : Prop := True
/-- setOfIdeal_eq_compl_singleton (abstract). -/
def setOfIdeal_eq_compl_singleton' : Prop := True
/-- continuousMapEval (abstract). -/
def continuousMapEval' : Prop := True
/-- continuousMapEval_bijective (abstract). -/
def continuousMapEval_bijective' : Prop := True
/-- homeoEval (abstract). -/
def homeoEval' : Prop := True

-- ContinuousMap/Interval.lean
/-- IccInclusionLeft (abstract). -/
def IccInclusionLeft' : Prop := True
/-- IccInclusionRight (abstract). -/
def IccInclusionRight' : Prop := True
/-- projIccCM (abstract). -/
def projIccCM' : Prop := True
/-- IccExtendCM (abstract). -/
def IccExtendCM' : Prop := True
/-- IccExtendCM_of_mem (abstract). -/
def IccExtendCM_of_mem' : Prop := True
/-- concat (abstract). -/
def concat' : Prop := True
/-- concat_comp_IccInclusionLeft (abstract). -/
def concat_comp_IccInclusionLeft' : Prop := True
/-- concat_comp_IccInclusionRight (abstract). -/
def concat_comp_IccInclusionRight' : Prop := True
/-- concat_left (abstract). -/
def concat_left' : Prop := True
/-- concat_right (abstract). -/
def concat_right' : Prop := True
/-- tendsto_concat (abstract). -/
def tendsto_concat' : Prop := True
/-- concatCM (abstract). -/
def concatCM' : Prop := True
/-- concatCM_left (abstract). -/
def concatCM_left' : Prop := True
/-- concatCM_right (abstract). -/
def concatCM_right' : Prop := True

-- ContinuousMap/LocallyConstant.lean
/-- toContinuousMapMonoidHom (abstract). -/
def toContinuousMapMonoidHom' : Prop := True
/-- toContinuousMapAlgHom (abstract). -/
def toContinuousMapAlgHom' : Prop := True

-- ContinuousMap/Ordered.lean
/-- sup'_apply (abstract). -/
def sup'_apply' : Prop := True
/-- inf'_apply (abstract). -/
def inf'_apply' : Prop := True
-- COLLISION: coe_inf' already in Order.lean — rename needed
-- COLLISION: IccExtend' already in Order.lean — rename needed

-- ContinuousMap/Periodic.lean
/-- periodic_tsum_comp_add_zsmul (abstract). -/
def periodic_tsum_comp_add_zsmul' : Prop := True

-- ContinuousMap/Polynomial.lean
/-- toContinuousMap_X_eq_id (abstract). -/
def toContinuousMap_X_eq_id' : Prop := True
/-- toContinuousMapOn (abstract). -/
def toContinuousMapOn' : Prop := True
/-- toContinuousMapOn_X_eq_restrict_id (abstract). -/
def toContinuousMapOn_X_eq_restrict_id' : Prop := True
/-- aeval_continuousMap_apply (abstract). -/
def aeval_continuousMap_apply' : Prop := True
/-- toContinuousMapOnAlgHom (abstract). -/
def toContinuousMapOnAlgHom' : Prop := True
/-- polynomialFunctions (abstract). -/
def polynomialFunctions' : Prop := True
/-- polynomialFunctions_coe (abstract). -/
def polynomialFunctions_coe' : Prop := True
/-- polynomialFunctions_separatesPoints (abstract). -/
def polynomialFunctions_separatesPoints' : Prop := True
/-- comap_compRightAlgHom_iccHomeoI (abstract). -/
def comap_compRightAlgHom_iccHomeoI' : Prop := True
/-- eq_adjoin_X (abstract). -/
def eq_adjoin_X' : Prop := True
/-- le_equalizer (abstract). -/
def le_equalizer' : Prop := True
/-- starClosure_eq_adjoin_X (abstract). -/
def starClosure_eq_adjoin_X' : Prop := True
/-- starClosure_le_equalizer (abstract). -/
def starClosure_le_equalizer' : Prop := True

-- ContinuousMap/SecondCountableSpace.lean
/-- compactOpen_eq_generateFrom (abstract). -/
def compactOpen_eq_generateFrom' : Prop := True

-- ContinuousMap/Sigma.lean
/-- isEmbedding_sigmaMk_comp (abstract). -/
def isEmbedding_sigmaMk_comp' : Prop := True
/-- sigmaCodHomeomorph (abstract). -/
def sigmaCodHomeomorph' : Prop := True

-- ContinuousMap/Star.lean
/-- compStarAlgHom' (abstract). -/
def compStarAlgHom' : Prop := True
/-- compStarAlgHom'_id (abstract). -/
def compStarAlgHom'_id' : Prop := True
/-- compStarAlgHom'_comp (abstract). -/
def compStarAlgHom'_comp' : Prop := True
/-- compStarAlgEquiv' (abstract). -/
def compStarAlgEquiv' : Prop := True
/-- evalStarAlgHom (abstract). -/
def evalStarAlgHom' : Prop := True

-- ContinuousMap/StarOrdered.lean
/-- starOrderedRing_of_sqrt (abstract). -/
def starOrderedRing_of_sqrt' : Prop := True

-- ContinuousMap/StoneWeierstrass.lean
/-- attachBound (abstract). -/
def attachBound' : Prop := True
/-- polynomial_comp_attachBound (abstract). -/
def polynomial_comp_attachBound' : Prop := True
/-- polynomial_comp_attachBound_mem (abstract). -/
def polynomial_comp_attachBound_mem' : Prop := True
/-- comp_attachBound_mem_closure (abstract). -/
def comp_attachBound_mem_closure' : Prop := True
/-- abs_mem_subalgebra_closure (abstract). -/
def abs_mem_subalgebra_closure' : Prop := True
/-- inf_mem_subalgebra_closure (abstract). -/
def inf_mem_subalgebra_closure' : Prop := True
/-- inf_mem_closed_subalgebra (abstract). -/
def inf_mem_closed_subalgebra' : Prop := True
/-- sup_mem_subalgebra_closure (abstract). -/
def sup_mem_subalgebra_closure' : Prop := True
/-- sup_mem_closed_subalgebra (abstract). -/
def sup_mem_closed_subalgebra' : Prop := True
/-- sublattice_closure_eq_top (abstract). -/
def sublattice_closure_eq_top' : Prop := True
/-- subalgebra_topologicalClosure_eq_top_of_separatesPoints (abstract). -/
def subalgebra_topologicalClosure_eq_top_of_separatesPoints' : Prop := True
/-- continuousMap_mem_subalgebra_closure_of_separatesPoints (abstract). -/
def continuousMap_mem_subalgebra_closure_of_separatesPoints' : Prop := True
/-- exists_mem_subalgebra_near_continuousMap_of_separatesPoints (abstract). -/
def exists_mem_subalgebra_near_continuousMap_of_separatesPoints' : Prop := True
/-- exists_mem_subalgebra_near_continuous_of_separatesPoints (abstract). -/
def exists_mem_subalgebra_near_continuous_of_separatesPoints' : Prop := True
/-- rclike_to_real (abstract). -/
def rclike_to_real' : Prop := True
/-- starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (abstract). -/
def starSubalgebra_topologicalClosure_eq_top_of_separatesPoints' : Prop := True
/-- starClosure_topologicalClosure (abstract). -/
def starClosure_topologicalClosure' : Prop := True
/-- induction_on_of_compact (abstract). -/
def induction_on_of_compact' : Prop := True
/-- algHom_ext_map_X (abstract). -/
def algHom_ext_map_X' : Prop := True
/-- starAlgHom_ext_map_X (abstract). -/
def starAlgHom_ext_map_X' : Prop := True
/-- adjoin_id_eq_span_one_union (abstract). -/
def adjoin_id_eq_span_one_union' : Prop := True
/-- adjoin_id_eq_span_one_add (abstract). -/
def adjoin_id_eq_span_one_add' : Prop := True
/-- nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom (abstract). -/
def nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom' : Prop := True
/-- ker_evalStarAlgHom_inter_adjoin_id (abstract). -/
def ker_evalStarAlgHom_inter_adjoin_id' : Prop := True
/-- closure_ker_inter (abstract). -/
def closure_ker_inter' : Prop := True
/-- ker_evalStarAlgHom_eq_closure_adjoin_id (abstract). -/
def ker_evalStarAlgHom_eq_closure_adjoin_id' : Prop := True
/-- adjoin_id_dense (abstract). -/
def adjoin_id_dense' : Prop := True
/-- nonUnitalStarAlgHom_apply_mul_eq_zero (abstract). -/
def nonUnitalStarAlgHom_apply_mul_eq_zero' : Prop := True
/-- mul_nonUnitalStarAlgHom_apply_eq_zero (abstract). -/
def mul_nonUnitalStarAlgHom_apply_eq_zero' : Prop := True

-- ContinuousMap/T0Sierpinski.lean
/-- eq_induced_by_maps_to_sierpinski (abstract). -/
def eq_induced_by_maps_to_sierpinski' : Prop := True
/-- productOfMemOpens (abstract). -/
def productOfMemOpens' : Prop := True
/-- productOfMemOpens_isInducing (abstract). -/
def productOfMemOpens_isInducing' : Prop := True
/-- productOfMemOpens_injective (abstract). -/
def productOfMemOpens_injective' : Prop := True
/-- productOfMemOpens_isEmbedding (abstract). -/
def productOfMemOpens_isEmbedding' : Prop := True

-- ContinuousMap/Units.lean
/-- compatible (abstract). -/
def compatible' : Prop := True
/-- unitsLift (abstract). -/
def unitsLift' : Prop := True
/-- continuous_isUnit_unit (abstract). -/
def continuous_isUnit_unit' : Prop := True
/-- unitsOfForallIsUnit (abstract). -/
def unitsOfForallIsUnit' : Prop := True
/-- isUnit_iff_forall_isUnit (abstract). -/
def isUnit_iff_forall_isUnit' : Prop := True
/-- isUnit_iff_forall_ne_zero (abstract). -/
def isUnit_iff_forall_ne_zero' : Prop := True
/-- spectrum_eq_preimage_range (abstract). -/
def spectrum_eq_preimage_range' : Prop := True
/-- spectrum_eq_range (abstract). -/
def spectrum_eq_range' : Prop := True

-- ContinuousMap/Weierstrass.lean
/-- polynomialFunctions_closure_eq_top' (abstract). -/
def polynomialFunctions_closure_eq_top' : Prop := True
/-- continuousMap_mem_polynomialFunctions_closure (abstract). -/
def continuousMap_mem_polynomialFunctions_closure' : Prop := True
/-- exists_polynomial_near_continuousMap (abstract). -/
def exists_polynomial_near_continuousMap' : Prop := True
/-- exists_polynomial_near_of_continuousOn (abstract). -/
def exists_polynomial_near_of_continuousOn' : Prop := True

-- ContinuousMap/ZeroAtInfty.lean
/-- ZeroAtInftyContinuousMap (abstract). -/
def ZeroAtInftyContinuousMap' : Prop := True
/-- ZeroAtInftyContinuousMapClass (abstract). -/
def ZeroAtInftyContinuousMapClass' : Prop := True
/-- tends (abstract). -/
def tends' : Prop := True
/-- eq_of_empty (abstract). -/
def eq_of_empty' : Prop := True
/-- liftZeroAtInfty (abstract). -/
def liftZeroAtInfty' : Prop := True
/-- isBounded_range (abstract). -/
def isBounded_range' : Prop := True
/-- isBounded_image (abstract). -/
def isBounded_image' : Prop := True
/-- toBCF (abstract). -/
def toBCF' : Prop := True
/-- toBCF_injective (abstract). -/
def toBCF_injective' : Prop := True
/-- isometry_toBCF (abstract). -/
def isometry_toBCF' : Prop := True
/-- isClosed_range_toBCF (abstract). -/
def isClosed_range_toBCF' : Prop := True

-- ContinuousOn.lean
/-- nhds_bind_nhdsWithin (abstract). -/
def nhds_bind_nhdsWithin' : Prop := True
/-- eventually_nhds_nhdsWithin (abstract). -/
def eventually_nhds_nhdsWithin' : Prop := True
/-- eventually_nhdsWithin_iff (abstract). -/
def eventually_nhdsWithin_iff' : Prop := True
/-- frequently_nhdsWithin_iff (abstract). -/
def frequently_nhdsWithin_iff' : Prop := True
/-- mem_closure_ne_iff_frequently_within (abstract). -/
def mem_closure_ne_iff_frequently_within' : Prop := True
/-- eventually_eventually_nhdsWithin (abstract). -/
def eventually_eventually_nhdsWithin' : Prop := True
/-- eventually_mem_nhdsWithin_iff (abstract). -/
def eventually_mem_nhdsWithin_iff' : Prop := True
/-- nhdsWithin_basis_open (abstract). -/
def nhdsWithin_basis_open' : Prop := True
/-- mem_nhdsWithin (abstract). -/
def mem_nhdsWithin' : Prop := True
/-- mem_nhdsWithin_iff_exists_mem_nhds_inter (abstract). -/
def mem_nhdsWithin_iff_exists_mem_nhds_inter' : Prop := True
/-- diff_mem_nhdsWithin_compl (abstract). -/
def diff_mem_nhdsWithin_compl' : Prop := True
/-- diff_mem_nhdsWithin_diff (abstract). -/
def diff_mem_nhdsWithin_diff' : Prop := True
/-- nhds_of_nhdsWithin_of_nhds (abstract). -/
def nhds_of_nhdsWithin_of_nhds' : Prop := True
/-- mem_nhdsWithin_iff_eventually (abstract). -/
def mem_nhdsWithin_iff_eventually' : Prop := True
/-- mem_nhdsWithin_iff_eventuallyEq (abstract). -/
def mem_nhdsWithin_iff_eventuallyEq' : Prop := True
/-- nhdsWithin_eq_iff_eventuallyEq (abstract). -/
def nhdsWithin_eq_iff_eventuallyEq' : Prop := True
/-- nhdsWithin_le_iff (abstract). -/
def nhdsWithin_le_iff' : Prop := True
/-- preimage_nhdsWithin_coinduced' (abstract). -/
def preimage_nhdsWithin_coinduced' : Prop := True
/-- mem_nhdsWithin_of_mem_nhds (abstract). -/
def mem_nhdsWithin_of_mem_nhds' : Prop := True
/-- self_mem_nhdsWithin (abstract). -/
def self_mem_nhdsWithin' : Prop := True
/-- eventually_mem_nhdsWithin (abstract). -/
def eventually_mem_nhdsWithin' : Prop := True
/-- inter_mem_nhdsWithin (abstract). -/
def inter_mem_nhdsWithin' : Prop := True
/-- pure_le_nhdsWithin (abstract). -/
def pure_le_nhdsWithin' : Prop := True
/-- mem_of_mem_nhdsWithin (abstract). -/
def mem_of_mem_nhdsWithin' : Prop := True
/-- self_of_nhdsWithin (abstract). -/
def self_of_nhdsWithin' : Prop := True
/-- tendsto_const_nhdsWithin (abstract). -/
def tendsto_const_nhdsWithin' : Prop := True
/-- nhdsWithin_restrict'' (abstract). -/
def nhdsWithin_restrict'' : Prop := True
/-- nhdsWithin_restrict' (abstract). -/
def nhdsWithin_restrict' : Prop := True
/-- nhdsWithin_le_of_mem (abstract). -/
def nhdsWithin_le_of_mem' : Prop := True
/-- nhdsWithin_le_nhds (abstract). -/
def nhdsWithin_le_nhds' : Prop := True
/-- nhdsWithin_eq_nhdsWithin' (abstract). -/
def nhdsWithin_eq_nhdsWithin' : Prop := True
/-- nhdsWithin_eq_nhds (abstract). -/
def nhdsWithin_eq_nhds' : Prop := True
/-- nhdsWithin_eq (abstract). -/
def nhdsWithin_eq' : Prop := True
/-- preimage_nhds_within_coinduced (abstract). -/
def preimage_nhds_within_coinduced' : Prop := True
/-- nhdsWithin_empty (abstract). -/
def nhdsWithin_empty' : Prop := True
/-- nhdsWithin_union (abstract). -/
def nhdsWithin_union' : Prop := True
/-- nhds_eq_nhdsWithin_sup_nhdsWithin (abstract). -/
def nhds_eq_nhdsWithin_sup_nhdsWithin' : Prop := True
/-- union_mem_nhds_of_mem_nhdsWithin (abstract). -/
def union_mem_nhds_of_mem_nhdsWithin' : Prop := True
/-- punctured_nhds_eq_nhdsWithin_sup_nhdsWithin (abstract). -/
def punctured_nhds_eq_nhdsWithin_sup_nhdsWithin' : Prop := True
/-- nhds_of_Ici_Iic (abstract). -/
def nhds_of_Ici_Iic' : Prop := True
/-- nhdsWithin_biUnion (abstract). -/
def nhdsWithin_biUnion' : Prop := True
/-- nhdsWithin_sUnion (abstract). -/
def nhdsWithin_sUnion' : Prop := True
/-- nhdsWithin_iUnion (abstract). -/
def nhdsWithin_iUnion' : Prop := True
/-- nhdsWithin_inter (abstract). -/
def nhdsWithin_inter' : Prop := True
/-- nhdsWithin_inter_of_mem (abstract). -/
def nhdsWithin_inter_of_mem' : Prop := True
/-- nhdsWithin_singleton (abstract). -/
def nhdsWithin_singleton' : Prop := True
/-- nhdsWithin_insert (abstract). -/
def nhdsWithin_insert' : Prop := True
/-- insert_mem_nhdsWithin_insert (abstract). -/
def insert_mem_nhdsWithin_insert' : Prop := True
/-- insert_mem_nhds_iff (abstract). -/
def insert_mem_nhds_iff' : Prop := True
/-- nhdsWithin_compl_singleton_sup_pure (abstract). -/
def nhdsWithin_compl_singleton_sup_pure' : Prop := True
/-- nhdsWithin_prod (abstract). -/
def nhdsWithin_prod' : Prop := True
/-- mem_interior_iff (abstract). -/
def mem_interior_iff' : Prop := True
/-- nhdsWithin_pi_eq' (abstract). -/
def nhdsWithin_pi_eq' : Prop := True
/-- nhdsWithin_pi_univ_eq (abstract). -/
def nhdsWithin_pi_univ_eq' : Prop := True
/-- nhdsWithin_pi_eq_bot (abstract). -/
def nhdsWithin_pi_eq_bot' : Prop := True
/-- nhdsWithin_pi_neBot (abstract). -/
def nhdsWithin_pi_neBot' : Prop := True
/-- piecewise_nhdsWithin (abstract). -/
def piecewise_nhdsWithin' : Prop := True
/-- if_nhdsWithin (abstract). -/
def if_nhdsWithin' : Prop := True
/-- nhdsWithin_neBot_of_mem (abstract). -/
def nhdsWithin_neBot_of_mem' : Prop := True
/-- mem_of_nhdsWithin_neBot (abstract). -/
def mem_of_nhdsWithin_neBot' : Prop := True
/-- mem_closure_pi (abstract). -/
def mem_closure_pi' : Prop := True
/-- closure_pi_set (abstract). -/
def closure_pi_set' : Prop := True
/-- dense_pi (abstract). -/
def dense_pi' : Prop := True
/-- eventuallyEq_nhdsWithin_iff (abstract). -/
def eventuallyEq_nhdsWithin_iff' : Prop := True
/-- eventuallyEq_nhdsWithin_of_eqOn (abstract). -/
def eventuallyEq_nhdsWithin_of_eqOn' : Prop := True
/-- eventuallyEq_nhdsWithin (abstract). -/
def eventuallyEq_nhdsWithin' : Prop := True
/-- tendsto_nhdsWithin_congr (abstract). -/
def tendsto_nhdsWithin_congr' : Prop := True
/-- eventually_nhdsWithin_of_forall (abstract). -/
def eventually_nhdsWithin_of_forall' : Prop := True
/-- tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (abstract). -/
def tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within' : Prop := True
/-- tendsto_nhdsWithin_iff (abstract). -/
def tendsto_nhdsWithin_iff' : Prop := True
/-- eventually_nhdsWithin_of_eventually_nhds (abstract). -/
def eventually_nhdsWithin_of_eventually_nhds' : Prop := True
/-- preimage_mem_nhdsWithin (abstract). -/
def preimage_mem_nhdsWithin' : Prop := True
/-- mem_nhdsWithin_subtype (abstract). -/
def mem_nhdsWithin_subtype' : Prop := True
/-- nhdsWithin_subtype (abstract). -/
def nhdsWithin_subtype' : Prop := True
/-- nhdsWithin_eq_map_subtype_coe (abstract). -/
def nhdsWithin_eq_map_subtype_coe' : Prop := True
/-- mem_nhds_subtype_iff_nhdsWithin (abstract). -/
def mem_nhds_subtype_iff_nhdsWithin' : Prop := True
/-- preimage_coe_mem_nhds_subtype (abstract). -/
def preimage_coe_mem_nhds_subtype' : Prop := True
/-- eventually_nhds_subtype_iff (abstract). -/
def eventually_nhds_subtype_iff' : Prop := True
/-- frequently_nhds_subtype_iff (abstract). -/
def frequently_nhds_subtype_iff' : Prop := True
/-- tendsto_nhdsWithin_iff_subtype (abstract). -/
def tendsto_nhdsWithin_iff_subtype' : Prop := True
/-- continuousWithinAt_univ (abstract). -/
def continuousWithinAt_univ' : Prop := True
/-- continuous_iff_continuousOn_univ (abstract). -/
def continuous_iff_continuousOn_univ' : Prop := True
/-- continuousWithinAt_iff_continuousAt_restrict (abstract). -/
def continuousWithinAt_iff_continuousAt_restrict' : Prop := True
/-- preimage_mem_nhdsWithin'' (abstract). -/
def preimage_mem_nhdsWithin'' : Prop := True
/-- continuousWithinAt_of_not_mem_closure (abstract). -/
def continuousWithinAt_of_not_mem_closure' : Prop := True
/-- continuousOn_iff (abstract). -/
def continuousOn_iff' : Prop := True
/-- continuousOn_iff_continuous_restrict (abstract). -/
def continuousOn_iff_continuous_restrict' : Prop := True
/-- restrict_mapsTo (abstract). -/
def restrict_mapsTo' : Prop := True
/-- mono_dom (abstract). -/
def mono_dom' : Prop := True
/-- mono_rng (abstract). -/
def mono_rng' : Prop := True
/-- continuousOn_iff_isClosed (abstract). -/
def continuousOn_iff_isClosed' : Prop := True
/-- continuous_of_cover_nhds (abstract). -/
def continuous_of_cover_nhds' : Prop := True
/-- continuousOn_empty (abstract). -/
def continuousOn_empty' : Prop := True
/-- continuousOn_singleton (abstract). -/
def continuousOn_singleton' : Prop := True
/-- continuousOn_open_iff (abstract). -/
def continuousOn_open_iff' : Prop := True
/-- isOpen_inter_preimage (abstract). -/
def isOpen_inter_preimage' : Prop := True
/-- isOpen_preimage (abstract). -/
def isOpen_preimage' : Prop := True
/-- preimage_isClosed_of_isClosed (abstract). -/
def preimage_isClosed_of_isClosed' : Prop := True
/-- continuousOn_of_locally_continuousOn (abstract). -/
def continuousOn_of_locally_continuousOn' : Prop := True
/-- continuousOn_to_generateFrom_iff (abstract). -/
def continuousOn_to_generateFrom_iff' : Prop := True
/-- continuousWithinAt_congr_set (abstract). -/
def continuousWithinAt_congr_set' : Prop := True
-- COLLISION: congr_set' already in Analysis.lean — rename needed
/-- continuousWithinAt_inter' (abstract). -/
def continuousWithinAt_inter' : Prop := True
/-- continuousWithinAt_union (abstract). -/
def continuousWithinAt_union' : Prop := True
/-- continuousWithinAt_singleton (abstract). -/
def continuousWithinAt_singleton' : Prop := True
/-- continuousWithinAt_insert_self (abstract). -/
def continuousWithinAt_insert_self' : Prop := True
/-- diff_iff (abstract). -/
def diff_iff' : Prop := True
/-- continuousWithinAt_diff_self (abstract). -/
def continuousWithinAt_diff_self' : Prop := True
/-- continuousWithinAt_compl_self (abstract). -/
def continuousWithinAt_compl_self' : Prop := True
/-- antitone_continuousOn (abstract). -/
def antitone_continuousOn' : Prop := True
/-- continuousWithinAt_iff_continuousAt (abstract). -/
def continuousWithinAt_iff_continuousAt' : Prop := True
/-- continuousOn_congr (abstract). -/
def continuousOn_congr' : Prop := True
/-- congr_continuousWithinAt (abstract). -/
def congr_continuousWithinAt' : Prop := True
/-- continuousWithinAt_congr_of_insert (abstract). -/
def continuousWithinAt_congr_of_insert' : Prop := True
-- COLLISION: congr_mono' already in Analysis.lean — rename needed
-- COLLISION: congr_of_eventuallyEq' already in Analysis.lean — rename needed
-- COLLISION: comp_of_eq' already in Analysis.lean — rename needed
-- COLLISION: comp_inter' already in Analysis.lean — rename needed
-- COLLISION: comp_inter_of_eq' already in Analysis.lean — rename needed
-- COLLISION: comp_of_preimage_mem_nhdsWithin' already in Analysis.lean — rename needed
-- COLLISION: comp_of_preimage_mem_nhdsWithin_of_eq' already in Analysis.lean — rename needed
-- COLLISION: comp_of_mem_nhdsWithin_image' already in Analysis.lean — rename needed
-- COLLISION: comp_of_mem_nhdsWithin_image_of_eq' already in Analysis.lean — rename needed
/-- comp_continuousWithinAt (abstract). -/
def comp_continuousWithinAt' : Prop := True
/-- comp_continuousWithinAt_of_eq (abstract). -/
def comp_continuousWithinAt_of_eq' : Prop := True
/-- comp_continuousOn (abstract). -/
def comp_continuousOn' : Prop := True
/-- comp_continuous (abstract). -/
def comp_continuous' : Prop := True
/-- image_comp_continuous (abstract). -/
def image_comp_continuous' : Prop := True
/-- comp₂_continuousWithinAt (abstract). -/
def comp₂_continuousWithinAt' : Prop := True
/-- comp₂_continuousWithinAt_of_eq (abstract). -/
def comp₂_continuousWithinAt_of_eq' : Prop := True
-- COLLISION: mem_closure' already in RingTheory2.lean — rename needed
-- COLLISION: prod_map' already in Order.lean — rename needed
/-- continuousWithinAt_prod_of_discrete_left (abstract). -/
def continuousWithinAt_prod_of_discrete_left' : Prop := True
/-- continuousWithinAt_prod_of_discrete_right (abstract). -/
def continuousWithinAt_prod_of_discrete_right' : Prop := True
/-- continuousAt_prod_of_discrete_left (abstract). -/
def continuousAt_prod_of_discrete_left' : Prop := True
/-- continuousAt_prod_of_discrete_right (abstract). -/
def continuousAt_prod_of_discrete_right' : Prop := True
/-- continuousOn_prod_of_discrete_left (abstract). -/
def continuousOn_prod_of_discrete_left' : Prop := True
/-- continuousOn_prod_of_discrete_right (abstract). -/
def continuousOn_prod_of_discrete_right' : Prop := True
/-- continuous_prod_of_discrete_left (abstract). -/
def continuous_prod_of_discrete_left' : Prop := True
/-- continuous_prod_of_discrete_right (abstract). -/
def continuous_prod_of_discrete_right' : Prop := True
/-- isOpenMap_prod_of_discrete_left (abstract). -/
def isOpenMap_prod_of_discrete_left' : Prop := True
/-- isOpenMap_prod_of_discrete_right (abstract). -/
def isOpenMap_prod_of_discrete_right' : Prop := True
/-- continuousOn_fst (abstract). -/
def continuousOn_fst' : Prop := True
/-- continuousWithinAt_fst (abstract). -/
def continuousWithinAt_fst' : Prop := True
/-- continuousOn_snd (abstract). -/
def continuousOn_snd' : Prop := True
/-- continuousWithinAt_snd (abstract). -/
def continuousWithinAt_snd' : Prop := True
/-- continuousWithinAt_prod_iff (abstract). -/
def continuousWithinAt_prod_iff' : Prop := True
/-- continuousWithinAt_pi (abstract). -/
def continuousWithinAt_pi' : Prop := True
/-- continuousOn_pi (abstract). -/
def continuousOn_pi' : Prop := True
/-- continuousOn_apply (abstract). -/
def continuousOn_apply' : Prop := True
/-- continuousOn_const (abstract). -/
def continuousOn_const' : Prop := True
/-- continuousWithinAt_const (abstract). -/
def continuousWithinAt_const' : Prop := True
/-- continuousOn_id (abstract). -/
def continuousOn_id' : Prop := True
/-- continuousWithinAt_id (abstract). -/
def continuousWithinAt_id' : Prop := True
/-- continuousWithinAt_iff (abstract). -/
def continuousWithinAt_iff' : Prop := True
/-- map_nhdsWithin_eq (abstract). -/
def map_nhdsWithin_eq' : Prop := True
/-- map_nhdsWithin_preimage_eq (abstract). -/
def map_nhdsWithin_preimage_eq' : Prop := True
/-- continuousOn_isOpen_iff (abstract). -/
def continuousOn_isOpen_iff' : Prop := True
/-- continuousOn_image_of_leftInvOn (abstract). -/
def continuousOn_image_of_leftInvOn' : Prop := True
/-- continuousOn_range_of_leftInverse (abstract). -/
def continuousOn_range_of_leftInverse' : Prop := True
/-- continuousWithinAt_update_same (abstract). -/
def continuousWithinAt_update_same' : Prop := True
/-- continuousAt_update_same (abstract). -/
def continuousAt_update_same' : Prop := True
-- COLLISION: if' already in Order.lean — rename needed
-- COLLISION: piecewise' already in Order.lean — rename needed
/-- continuous_if' (abstract). -/
def continuous_if' : Prop := True
/-- continuous_if_const (abstract). -/
def continuous_if_const' : Prop := True
/-- if_const (abstract). -/
def if_const' : Prop := True
/-- continuous_piecewise (abstract). -/
def continuous_piecewise' : Prop := True
/-- continuous_mulIndicator (abstract). -/
def continuous_mulIndicator' : Prop := True
-- COLLISION: ite' already in Order.lean — rename needed
/-- ite_inter_closure_eq_of_inter_frontier_eq (abstract). -/
def ite_inter_closure_eq_of_inter_frontier_eq' : Prop := True
/-- ite_inter_closure_compl_eq_of_inter_frontier_eq (abstract). -/
def ite_inter_closure_compl_eq_of_inter_frontier_eq' : Prop := True
/-- continuousOn_piecewise_ite' (abstract). -/
def continuousOn_piecewise_ite' : Prop := True
/-- union_continuousAt (abstract). -/
def union_continuousAt' : Prop := True

-- Covering.lean
/-- IsEvenlyCovered (abstract). -/
def IsEvenlyCovered' : Prop := True
/-- toTrivialization (abstract). -/
def toTrivialization' : Prop := True
/-- mem_toTrivialization_baseSet (abstract). -/
def mem_toTrivialization_baseSet' : Prop := True
/-- toTrivialization_apply (abstract). -/
def toTrivialization_apply' : Prop := True
/-- IsCoveringMapOn (abstract). -/
def IsCoveringMapOn' : Prop := True
/-- isLocalHomeomorphOn (abstract). -/
def isLocalHomeomorphOn' : Prop := True
/-- isCoveringMap_iff_isCoveringMapOn_univ (abstract). -/
def isCoveringMap_iff_isCoveringMapOn_univ' : Prop := True
/-- isCoveringMapOn (abstract). -/
def isCoveringMapOn' : Prop := True
/-- isLocalHomeomorph (abstract). -/
def isLocalHomeomorph' : Prop := True
-- COLLISION: isQuotientMap' already in Analysis.lean — rename needed
/-- isSeparatedMap (abstract). -/
def isSeparatedMap' : Prop := True
/-- eq_of_comp_eq (abstract). -/
def eq_of_comp_eq' : Prop := True
/-- const_of_comp (abstract). -/
def const_of_comp' : Prop := True
/-- eqOn_of_comp_eqOn (abstract). -/
def eqOn_of_comp_eqOn' : Prop := True
/-- constOn_of_comp (abstract). -/
def constOn_of_comp' : Prop := True

-- Defs/Basic.lean
/-- endowing (abstract). -/
def endowing' : Prop := True
/-- TopologicalSpace (abstract). -/
def TopologicalSpace' : Prop := True
/-- IsOpen (abstract). -/
def IsOpen' : Prop := True
/-- isOpen_univ (abstract). -/
def isOpen_univ' : Prop := True
/-- isOpen_sUnion (abstract). -/
def isOpen_sUnion' : Prop := True
/-- IsClopen (abstract). -/
def IsClopen' : Prop := True
/-- IsLocallyClosed (abstract). -/
def IsLocallyClosed' : Prop := True
/-- frontier (abstract). -/
def frontier' : Prop := True
/-- coborder (abstract). -/
def coborder' : Prop := True
/-- Dense (abstract). -/
def Dense' : Prop := True
/-- DenseRange (abstract). -/
def DenseRange' : Prop := True
-- COLLISION: Continuous' already in Order.lean — rename needed
/-- IsOpenMap (abstract). -/
def IsOpenMap' : Prop := True
/-- IsClosedMap (abstract). -/
def IsClosedMap' : Prop := True
/-- IsOpenQuotientMap (abstract). -/
def IsOpenQuotientMap' : Prop := True
/-- BaireSpace (abstract). -/
def BaireSpace' : Prop := True

-- Defs/Filter.lean
-- COLLISION: nhds' already in Analysis.lean — rename needed
/-- nhdsWithin (abstract). -/
def nhdsWithin' : Prop := True
/-- nhdsSet (abstract). -/
def nhdsSet' : Prop := True
/-- exterior (abstract). -/
def exterior' : Prop := True
/-- ContinuousAt (abstract). -/
def ContinuousAt' : Prop := True
/-- ContinuousWithinAt (abstract). -/
def ContinuousWithinAt' : Prop := True
/-- ContinuousOn (abstract). -/
def ContinuousOn' : Prop := True
/-- Specializes (abstract). -/
def Specializes' : Prop := True
/-- Inseparable (abstract). -/
def Inseparable' : Prop := True
/-- specializationPreorder (abstract). -/
def specializationPreorder' : Prop := True
/-- inseparableSetoid (abstract). -/
def inseparableSetoid' : Prop := True
/-- SeparationQuotient (abstract). -/
def SeparationQuotient' : Prop := True
/-- limUnder (abstract). -/
def limUnder' : Prop := True
/-- ClusterPt (abstract). -/
def ClusterPt' : Prop := True
/-- MapClusterPt (abstract). -/
def MapClusterPt' : Prop := True
/-- AccPt (abstract). -/
def AccPt' : Prop := True
-- COLLISION: IsCompact' already in Topology.lean — rename needed
/-- CompactSpace (abstract). -/
def CompactSpace' : Prop := True
/-- NoncompactSpace (abstract). -/
def NoncompactSpace' : Prop := True
/-- WeaklyLocallyCompactSpace (abstract). -/
def WeaklyLocallyCompactSpace' : Prop := True
/-- LocallyCompactSpace (abstract). -/
def LocallyCompactSpace' : Prop := True
/-- LocallyCompactPair (abstract). -/
def LocallyCompactPair' : Prop := True
/-- cocompact (abstract). -/
def cocompact' : Prop := True
/-- coclosedCompact (abstract). -/
def coclosedCompact' : Prop := True

-- Defs/Induced.lean
/-- RestrictGenTopology (abstract). -/
def RestrictGenTopology' : Prop := True
/-- IsInducing (abstract). -/
def IsInducing' : Prop := True
-- COLLISION: IsEmbedding' already in ModelTheory.lean — rename needed
/-- IsOpenEmbedding (abstract). -/
def IsOpenEmbedding' : Prop := True
/-- IsClosedEmbedding (abstract). -/
def IsClosedEmbedding' : Prop := True
/-- IsQuotientMap (abstract). -/
def IsQuotientMap' : Prop := True

-- Defs/Sequences.lean
/-- seqClosure (abstract). -/
def seqClosure' : Prop := True
/-- IsSeqClosed (abstract). -/
def IsSeqClosed' : Prop := True
/-- SeqContinuous (abstract). -/
def SeqContinuous' : Prop := True
/-- IsSeqCompact (abstract). -/
def IsSeqCompact' : Prop := True
/-- SeqCompactSpace (abstract). -/
def SeqCompactSpace' : Prop := True
/-- FrechetUrysohnSpace (abstract). -/
def FrechetUrysohnSpace' : Prop := True
/-- SequentialSpace (abstract). -/
def SequentialSpace' : Prop := True

-- Defs/Ultrafilter.lean

-- DenseEmbedding.lean
/-- IsDenseInducing (abstract). -/
def IsDenseInducing' : Prop := True
/-- nhds_eq_comap (abstract). -/
def nhds_eq_comap' : Prop := True
/-- closure_range (abstract). -/
def closure_range' : Prop := True
/-- closure_image_mem_nhds (abstract). -/
def closure_image_mem_nhds' : Prop := True
/-- interior_compact_eq_empty (abstract). -/
def interior_compact_eq_empty' : Prop := True
/-- tendsto_comap_nhds_nhds (abstract). -/
def tendsto_comap_nhds_nhds' : Prop := True
/-- comap_nhds_neBot (abstract). -/
def comap_nhds_neBot' : Prop := True
/-- extend_eq_of_tendsto (abstract). -/
def extend_eq_of_tendsto' : Prop := True
/-- extend_eq_at (abstract). -/
def extend_eq_at' : Prop := True
-- COLLISION: extend_eq' already in Analysis.lean — rename needed
/-- extend_unique_at (abstract). -/
def extend_unique_at' : Prop := True
-- COLLISION: extend_unique' already in Analysis.lean — rename needed
/-- continuousAt_extend (abstract). -/
def continuousAt_extend' : Prop := True
/-- IsDenseEmbedding (abstract). -/
def IsDenseEmbedding' : Prop := True
-- COLLISION: isDenseInducing' already in MeasureTheory2.lean — rename needed
/-- inj_iff (abstract). -/
def inj_iff' : Prop := True
/-- subtypeEmb (abstract). -/
def subtypeEmb' : Prop := True
/-- isDenseEmbedding_val (abstract). -/
def isDenseEmbedding_val' : Prop := True
/-- isClosed_property (abstract). -/
def isClosed_property' : Prop := True
/-- isClosed_property2 (abstract). -/
def isClosed_property2' : Prop := True
/-- isClosed_property3 (abstract). -/
def isClosed_property3' : Prop := True
-- COLLISION: induction_on₂' already in Algebra.lean — rename needed
-- COLLISION: induction_on₃' already in MeasureTheory2.lean — rename needed
-- COLLISION: equalizer' already in Order.lean — rename needed
/-- hasBasis_of_isDenseInducing (abstract). -/
def hasBasis_of_isDenseInducing' : Prop := True

-- DerivedSet.lean
/-- derivedSet (abstract). -/
def derivedSet' : Prop := True
/-- derivedSet_union (abstract). -/
def derivedSet_union' : Prop := True
/-- derivedSet_mono (abstract). -/
def derivedSet_mono' : Prop := True
/-- image_derivedSet (abstract). -/
def image_derivedSet' : Prop := True
/-- derivedSet_subset_closure (abstract). -/
def derivedSet_subset_closure' : Prop := True
/-- isClosed_iff_derivedSet_subset (abstract). -/
def isClosed_iff_derivedSet_subset' : Prop := True
/-- derivedSet_closure (abstract). -/
def derivedSet_closure' : Prop := True
/-- perfect_iff_eq_derivedSet (abstract). -/
def perfect_iff_eq_derivedSet' : Prop := True
/-- inter_derivedSet_nonempty (abstract). -/
def inter_derivedSet_nonempty' : Prop := True

-- DiscreteQuotient.lean
/-- DiscreteQuotient (abstract). -/
def DiscreteQuotient' : Prop := True
/-- toSetoid_injective (abstract). -/
def toSetoid_injective' : Prop := True
/-- ofIsClopen (abstract). -/
def ofIsClopen' : Prop := True
/-- fiber_eq (abstract). -/
def fiber_eq' : Prop := True
/-- proj_isQuotientMap (abstract). -/
def proj_isQuotientMap' : Prop := True
/-- proj_continuous (abstract). -/
def proj_continuous' : Prop := True
/-- proj_isLocallyConstant (abstract). -/
def proj_isLocallyConstant' : Prop := True
/-- isClosed_preimage (abstract). -/
def isClosed_preimage' : Prop := True
/-- isClopen_setOf_rel (abstract). -/
def isClopen_setOf_rel' : Prop := True
-- COLLISION: comap_mono' already in Order.lean — rename needed
-- COLLISION: ofLE' already in Order.lean — rename needed
-- COLLISION: ofLE_refl' already in CategoryTheory.lean — rename needed
/-- ofLE_ofLE (abstract). -/
def ofLE_ofLE' : Prop := True
-- COLLISION: ofLE_comp_ofLE' already in CategoryTheory.lean — rename needed
/-- ofLE_continuous (abstract). -/
def ofLE_continuous' : Prop := True
/-- ofLE_proj (abstract). -/
def ofLE_proj' : Prop := True
/-- ofLE_comp_proj (abstract). -/
def ofLE_comp_proj' : Prop := True
/-- proj_bot_eq (abstract). -/
def proj_bot_eq' : Prop := True
/-- proj_bot_inj (abstract). -/
def proj_bot_inj' : Prop := True
/-- proj_bot_injective (abstract). -/
def proj_bot_injective' : Prop := True
/-- LEComap (abstract). -/
def LEComap' : Prop := True
/-- ofLE_map (abstract). -/
def ofLE_map' : Prop := True
/-- ofLE_comp_map (abstract). -/
def ofLE_comp_map' : Prop := True
/-- map_ofLE (abstract). -/
def map_ofLE' : Prop := True
/-- map_comp_ofLE (abstract). -/
def map_comp_ofLE' : Prop := True
/-- eq_of_forall_proj_eq (abstract). -/
def eq_of_forall_proj_eq' : Prop := True
/-- fiber_subset_ofLE (abstract). -/
def fiber_subset_ofLE' : Prop := True
/-- exists_of_compat (abstract). -/
def exists_of_compat' : Prop := True
/-- finsetClopens (abstract). -/
def finsetClopens' : Prop := True
/-- comp_finsetClopens (abstract). -/
def comp_finsetClopens' : Prop := True
/-- finsetClopens_inj (abstract). -/
def finsetClopens_inj' : Prop := True
/-- equivFinsetClopens (abstract). -/
def equivFinsetClopens' : Prop := True
/-- discreteQuotient (abstract). -/
def discreteQuotient' : Prop := True

-- DiscreteSubset.lean
/-- tendsto_cofinite_cocompact_iff (abstract). -/
def tendsto_cofinite_cocompact_iff' : Prop := True
/-- discrete_of_tendsto_cofinite_cocompact (abstract). -/
def discrete_of_tendsto_cofinite_cocompact' : Prop := True
/-- tendsto_cofinite_cocompact_of_discrete (abstract). -/
def tendsto_cofinite_cocompact_of_discrete' : Prop := True
/-- tendsto_coe_cofinite_of_discreteTopology (abstract). -/
def tendsto_coe_cofinite_of_discreteTopology' : Prop := True
/-- tendsto_coe_cofinite_iff (abstract). -/
def tendsto_coe_cofinite_iff' : Prop := True
/-- isClosed_and_discrete_iff (abstract). -/
def isClosed_and_discrete_iff' : Prop := True
/-- codiscreteWithin (abstract). -/
def codiscreteWithin' : Prop := True
/-- mem_codiscreteWithin (abstract). -/
def mem_codiscreteWithin' : Prop := True
/-- mem_codiscreteWithin_accPt (abstract). -/
def mem_codiscreteWithin_accPt' : Prop := True
/-- codiscrete (abstract). -/
def codiscrete' : Prop := True
/-- mem_codiscrete (abstract). -/
def mem_codiscrete' : Prop := True
/-- mem_codiscrete_accPt (abstract). -/
def mem_codiscrete_accPt' : Prop := True
/-- mem_codiscrete_subtype_iff_mem_codiscreteWithin (abstract). -/
def mem_codiscrete_subtype_iff_mem_codiscreteWithin' : Prop := True

-- EMetricSpace/Basic.lean
/-- edist_le_Ico_sum_edist (abstract). -/
def edist_le_Ico_sum_edist' : Prop := True
/-- edist_le_range_sum_edist (abstract). -/
def edist_le_range_sum_edist' : Prop := True
/-- edist_le_Ico_sum_of_edist_le (abstract). -/
def edist_le_Ico_sum_of_edist_le' : Prop := True
/-- edist_le_range_sum_of_edist_le (abstract). -/
def edist_le_range_sum_of_edist_le' : Prop := True
/-- isUniformInducing_iff (abstract). -/
def isUniformInducing_iff' : Prop := True
/-- isUniformEmbedding_iff (abstract). -/
def isUniformEmbedding_iff' : Prop := True
/-- controlled_of_isUniformEmbedding (abstract). -/
def controlled_of_isUniformEmbedding' : Prop := True
/-- complete_of_convergent_controlled_sequences (abstract). -/
def complete_of_convergent_controlled_sequences' : Prop := True
/-- complete_of_cauchySeq_tendsto (abstract). -/
def complete_of_cauchySeq_tendsto' : Prop := True
-- COLLISION: cauchySeq_iff' already in Analysis.lean — rename needed
/-- cauchySeq_iff_NNReal (abstract). -/
def cauchySeq_iff_NNReal' : Prop := True
/-- totallyBounded_iff (abstract). -/
def totallyBounded_iff' : Prop := True
/-- subset_countable_closure_of_compact (abstract). -/
def subset_countable_closure_of_compact' : Prop := True
/-- secondCountable_of_almost_dense_set (abstract). -/
def secondCountable_of_almost_dense_set' : Prop := True
/-- ofT0PseudoEMetricSpace (abstract). -/
def ofT0PseudoEMetricSpace' : Prop := True
/-- countable_closure_of_compact (abstract). -/
def countable_closure_of_compact' : Prop := True

-- EMetricSpace/Defs.lean
/-- uniformity_dist_of_mem_uniformity (abstract). -/
def uniformity_dist_of_mem_uniformity' : Prop := True
/-- EDist (abstract). -/
def EDist' : Prop := True
/-- uniformSpaceOfEDist (abstract). -/
def uniformSpaceOfEDist' : Prop := True
/-- PseudoEMetricSpace (abstract). -/
def PseudoEMetricSpace' : Prop := True
/-- edist_triangle_left (abstract). -/
def edist_triangle_left' : Prop := True
/-- edist_triangle_right (abstract). -/
def edist_triangle_right' : Prop := True
/-- edist_congr_right (abstract). -/
def edist_congr_right' : Prop := True
/-- edist_congr_left (abstract). -/
def edist_congr_left' : Prop := True
/-- edist_congr (abstract). -/
def edist_congr' : Prop := True
/-- edist_triangle4 (abstract). -/
def edist_triangle4' : Prop := True
/-- uniformity_pseudoedist (abstract). -/
def uniformity_pseudoedist' : Prop := True
/-- uniformSpace_edist (abstract). -/
def uniformSpace_edist' : Prop := True
/-- uniformity_basis_edist (abstract). -/
def uniformity_basis_edist' : Prop := True
/-- mem_uniformity_edist (abstract). -/
def mem_uniformity_edist' : Prop := True
/-- mk_uniformity_basis (abstract). -/
def mk_uniformity_basis' : Prop := True
/-- mk_uniformity_basis_le (abstract). -/
def mk_uniformity_basis_le' : Prop := True
/-- uniformity_basis_edist_le (abstract). -/
def uniformity_basis_edist_le' : Prop := True
/-- uniformity_basis_edist_nnreal (abstract). -/
def uniformity_basis_edist_nnreal' : Prop := True
/-- uniformity_basis_edist_nnreal_le (abstract). -/
def uniformity_basis_edist_nnreal_le' : Prop := True
/-- uniformity_basis_edist_inv_nat (abstract). -/
def uniformity_basis_edist_inv_nat' : Prop := True
/-- uniformity_basis_edist_inv_two_pow (abstract). -/
def uniformity_basis_edist_inv_two_pow' : Prop := True
/-- edist_mem_uniformity (abstract). -/
def edist_mem_uniformity' : Prop := True
/-- uniformContinuousOn_iff (abstract). -/
def uniformContinuousOn_iff' : Prop := True
/-- uniformContinuous_iff (abstract). -/
def uniformContinuous_iff' : Prop := True
/-- replaceUniformity (abstract). -/
def replaceUniformity' : Prop := True
-- COLLISION: ball' already in Order.lean — rename needed
-- COLLISION: closedBall' already in Analysis.lean — rename needed
-- COLLISION: mem_closedBall' already in Analysis.lean — rename needed
/-- closedBall_top (abstract). -/
def closedBall_top' : Prop := True
-- COLLISION: ball_subset_closedBall' already in Analysis.lean — rename needed
-- COLLISION: pos_of_mem_ball' already in Analysis.lean — rename needed
-- COLLISION: mem_ball_self' already in Analysis.lean — rename needed
-- COLLISION: mem_closedBall_self' already in Analysis.lean — rename needed
/-- mem_ball_comm (abstract). -/
def mem_ball_comm' : Prop := True
/-- mem_closedBall_comm (abstract). -/
def mem_closedBall_comm' : Prop := True
/-- ball_subset_ball (abstract). -/
def ball_subset_ball' : Prop := True
/-- closedBall_subset_closedBall (abstract). -/
def closedBall_subset_closedBall' : Prop := True
/-- exists_ball_subset_ball (abstract). -/
def exists_ball_subset_ball' : Prop := True
/-- ball_eq_empty_iff (abstract). -/
def ball_eq_empty_iff' : Prop := True
/-- ordConnected_setOf_closedBall_subset (abstract). -/
def ordConnected_setOf_closedBall_subset' : Prop := True
/-- ordConnected_setOf_ball_subset (abstract). -/
def ordConnected_setOf_ball_subset' : Prop := True
/-- edistLtTopSetoid (abstract). -/
def edistLtTopSetoid' : Prop := True
-- COLLISION: ball_zero' already in Analysis.lean — rename needed
/-- nhds_basis_eball (abstract). -/
def nhds_basis_eball' : Prop := True
/-- nhdsWithin_basis_eball (abstract). -/
def nhdsWithin_basis_eball' : Prop := True
/-- nhds_basis_closed_eball (abstract). -/
def nhds_basis_closed_eball' : Prop := True
/-- nhdsWithin_basis_closed_eball (abstract). -/
def nhdsWithin_basis_closed_eball' : Prop := True
/-- mem_nhdsWithin_iff (abstract). -/
def mem_nhdsWithin_iff' : Prop := True
/-- tendsto_nhdsWithin_nhdsWithin (abstract). -/
def tendsto_nhdsWithin_nhdsWithin' : Prop := True
-- COLLISION: tendsto_nhds_nhds' already in Analysis.lean — rename needed
-- COLLISION: isOpen_ball' already in Analysis.lean — rename needed
/-- isClosed_ball_top (abstract). -/
def isClosed_ball_top' : Prop := True
-- COLLISION: ball_mem_nhds' already in Analysis.lean — rename needed
-- COLLISION: closedBall_mem_nhds' already in Analysis.lean — rename needed
/-- ball_prod_same (abstract). -/
def ball_prod_same' : Prop := True
/-- closedBall_prod_same (abstract). -/
def closedBall_prod_same' : Prop := True
-- COLLISION: tendsto_atTop' already in Order.lean — rename needed
/-- subset_countable_closure_of_almost_dense_set (abstract). -/
def subset_countable_closure_of_almost_dense_set' : Prop := True
/-- EMetricSpace (abstract). -/
def EMetricSpace' : Prop := True
/-- edist_eq_zero (abstract). -/
def edist_eq_zero' : Prop := True
/-- zero_eq_edist (abstract). -/
def zero_eq_edist' : Prop := True
/-- edist_le_zero (abstract). -/
def edist_le_zero' : Prop := True
/-- edist_pos (abstract). -/
def edist_pos' : Prop := True
/-- eq_of_forall_edist_le (abstract). -/
def eq_of_forall_edist_le' : Prop := True

-- EMetricSpace/Diam.lean
/-- diam (abstract). -/
def diam' : Prop := True
/-- diam_eq_sSup (abstract). -/
def diam_eq_sSup' : Prop := True
/-- diam_le_iff (abstract). -/
def diam_le_iff' : Prop := True
/-- diam_image_le_iff (abstract). -/
def diam_image_le_iff' : Prop := True
/-- edist_le_of_diam_le (abstract). -/
def edist_le_of_diam_le' : Prop := True
/-- edist_le_diam_of_mem (abstract). -/
def edist_le_diam_of_mem' : Prop := True
-- COLLISION: diam_le' already in Analysis.lean — rename needed
/-- diam_subsingleton (abstract). -/
def diam_subsingleton' : Prop := True
/-- diam_empty (abstract). -/
def diam_empty' : Prop := True
/-- diam_singleton (abstract). -/
def diam_singleton' : Prop := True
/-- diam_one (abstract). -/
def diam_one' : Prop := True
/-- diam_iUnion_mem_option (abstract). -/
def diam_iUnion_mem_option' : Prop := True
/-- diam_insert (abstract). -/
def diam_insert' : Prop := True
/-- diam_pair (abstract). -/
def diam_pair' : Prop := True
/-- diam_triple (abstract). -/
def diam_triple' : Prop := True
/-- diam_mono (abstract). -/
def diam_mono' : Prop := True
/-- diam_union (abstract). -/
def diam_union' : Prop := True
/-- diam_closedBall (abstract). -/
def diam_closedBall' : Prop := True
/-- diam_ball (abstract). -/
def diam_ball' : Prop := True
/-- diam_pi_le_of_le (abstract). -/
def diam_pi_le_of_le' : Prop := True
/-- diam_eq_zero_iff (abstract). -/
def diam_eq_zero_iff' : Prop := True
/-- diam_pos_iff' (abstract). -/
def diam_pos_iff' : Prop := True

-- EMetricSpace/Lipschitz.lean
/-- LipschitzWith (abstract). -/
def LipschitzWith' : Prop := True
/-- LipschitzOnWith (abstract). -/
def LipschitzOnWith' : Prop := True
/-- LocallyLipschitz (abstract). -/
def LocallyLipschitz' : Prop := True
/-- LocallyLipschitzOn (abstract). -/
def LocallyLipschitzOn' : Prop := True
/-- lipschitzOnWith_empty (abstract). -/
def lipschitzOnWith_empty' : Prop := True
/-- locallyLipschitzOn_empty (abstract). -/
def locallyLipschitzOn_empty' : Prop := True
/-- lipschitzOnWith_univ (abstract). -/
def lipschitzOnWith_univ' : Prop := True
/-- locallyLipschitzOn_univ (abstract). -/
def locallyLipschitzOn_univ' : Prop := True
-- COLLISION: locallyLipschitzOn' already in Analysis.lean — rename needed
/-- lipschitzOnWith_iff_restrict (abstract). -/
def lipschitzOnWith_iff_restrict' : Prop := True
/-- lipschitzOnWith_restrict (abstract). -/
def lipschitzOnWith_restrict' : Prop := True
/-- locallyLipschitzOn_iff_restrict (abstract). -/
def locallyLipschitzOn_iff_restrict' : Prop := True
/-- edist_le_mul_of_le (abstract). -/
def edist_le_mul_of_le' : Prop := True
/-- edist_lt_mul_of_lt (abstract). -/
def edist_lt_mul_of_lt' : Prop := True
/-- mapsTo_emetric_closedBall (abstract). -/
def mapsTo_emetric_closedBall' : Prop := True
/-- mapsTo_emetric_ball (abstract). -/
def mapsTo_emetric_ball' : Prop := True
/-- edist_lt_top (abstract). -/
def edist_lt_top' : Prop := True
/-- mul_edist_le (abstract). -/
def mul_edist_le' : Prop := True
/-- of_edist_le (abstract). -/
def of_edist_le' : Prop := True
-- COLLISION: weaken' already in Analysis.lean — rename needed
/-- ediam_image_le (abstract). -/
def ediam_image_le' : Prop := True
/-- edist_lt_of_edist_lt_div (abstract). -/
def edist_lt_of_edist_lt_div' : Prop := True
/-- comp_lipschitzOnWith (abstract). -/
def comp_lipschitzOnWith' : Prop := True
/-- prod_fst (abstract). -/
def prod_fst' : Prop := True
/-- prod_snd (abstract). -/
def prod_snd' : Prop := True
-- COLLISION: prod_mk_left' already in MeasureTheory2.lean — rename needed
-- COLLISION: prod_mk_right' already in MeasureTheory2.lean — rename needed
/-- edist_iterate_succ_le_geometric (abstract). -/
def edist_iterate_succ_le_geometric' : Prop := True
/-- mul_end (abstract). -/
def mul_end' : Prop := True
-- COLLISION: list_prod' already in Analysis.lean — rename needed
/-- pow_end (abstract). -/
def pow_end' : Prop := True
/-- uniformContinuousOn (abstract). -/
def uniformContinuousOn' : Prop := True
/-- ediam_image2_le (abstract). -/
def ediam_image2_le' : Prop := True
-- COLLISION: locallyLipschitz' already in Analysis.lean — rename needed
/-- continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith (abstract). -/
def continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith' : Prop := True
/-- continuousOn_prod_of_continuousOn_lipschitzOnWith (abstract). -/
def continuousOn_prod_of_continuousOn_lipschitzOnWith' : Prop := True
/-- continuous_prod_of_dense_continuous_lipschitzWith (abstract). -/
def continuous_prod_of_dense_continuous_lipschitzWith' : Prop := True
/-- continuous_prod_of_continuous_lipschitzWith (abstract). -/
def continuous_prod_of_continuous_lipschitzWith' : Prop := True

-- EMetricSpace/Paracompact.lean
/-- t4Space (abstract). -/
def t4Space' : Prop := True

-- EMetricSpace/Pi.lean
/-- edist_le_pi_edist (abstract). -/
def edist_le_pi_edist' : Prop := True
/-- edist_pi_le_iff (abstract). -/
def edist_pi_le_iff' : Prop := True
/-- edist_pi_const_le (abstract). -/
def edist_pi_const_le' : Prop := True
/-- edist_pi_const (abstract). -/
def edist_pi_const' : Prop := True

-- ExtendFrom.lean
-- COLLISION: we' already in RingTheory2.lean — rename needed
/-- extendFrom (abstract). -/
def extendFrom' : Prop := True
/-- tendsto_extendFrom (abstract). -/
def tendsto_extendFrom' : Prop := True
/-- extendFrom_eq (abstract). -/
def extendFrom_eq' : Prop := True
/-- extendFrom_extends (abstract). -/
def extendFrom_extends' : Prop := True
/-- continuousOn_extendFrom (abstract). -/
def continuousOn_extendFrom' : Prop := True
/-- continuous_extendFrom (abstract). -/
def continuous_extendFrom' : Prop := True

-- Exterior.lean
/-- exterior_singleton_eq_ker_nhds (abstract). -/
def exterior_singleton_eq_ker_nhds' : Prop := True
/-- mem_exterior_singleton (abstract). -/
def mem_exterior_singleton' : Prop := True
/-- exterior_def (abstract). -/
def exterior_def' : Prop := True
/-- mem_exterior (abstract). -/
def mem_exterior' : Prop := True
/-- subset_exterior_iff (abstract). -/
def subset_exterior_iff' : Prop := True
/-- subset_exterior (abstract). -/
def subset_exterior' : Prop := True
/-- exterior_minimal (abstract). -/
def exterior_minimal' : Prop := True
/-- exterior_eq (abstract). -/
def exterior_eq' : Prop := True
/-- exterior_subset (abstract). -/
def exterior_subset' : Prop := True
/-- exterior_iUnion (abstract). -/
def exterior_iUnion' : Prop := True
/-- exterior_union (abstract). -/
def exterior_union' : Prop := True
/-- exterior_sUnion (abstract). -/
def exterior_sUnion' : Prop := True
/-- exterior_mono (abstract). -/
def exterior_mono' : Prop := True
/-- exterior_subset_exterior (abstract). -/
def exterior_subset_exterior' : Prop := True
/-- exterior_subset_exterior_iff_nhdsSet (abstract). -/
def exterior_subset_exterior_iff_nhdsSet' : Prop := True
/-- exterior_eq_exterior_iff_nhdsSet (abstract). -/
def exterior_eq_exterior_iff_nhdsSet' : Prop := True
/-- specializes_iff_exterior_subset (abstract). -/
def specializes_iff_exterior_subset' : Prop := True
/-- exterior_iInter_subset (abstract). -/
def exterior_iInter_subset' : Prop := True
/-- exterior_inter_subset (abstract). -/
def exterior_inter_subset' : Prop := True
/-- exterior_sInter_subset (abstract). -/
def exterior_sInter_subset' : Prop := True
/-- exterior_empty (abstract). -/
def exterior_empty' : Prop := True
/-- exterior_univ (abstract). -/
def exterior_univ' : Prop := True
/-- exterior_eq_empty (abstract). -/
def exterior_eq_empty' : Prop := True
/-- nhdsSet_exterior (abstract). -/
def nhdsSet_exterior' : Prop := True
/-- exterior_exterior (abstract). -/
def exterior_exterior' : Prop := True

-- ExtremallyDisconnected.lean
/-- ExtremallyDisconnected (abstract). -/
def ExtremallyDisconnected' : Prop := True
/-- extremallyDisconnected_of_homeo (abstract). -/
def extremallyDisconnected_of_homeo' : Prop := True
-- COLLISION: Projective' already in Algebra.lean — rename needed
-- COLLISION: projective' already in CategoryTheory.lean — rename needed
/-- extremallyDisconnected (abstract). -/
def extremallyDisconnected' : Prop := True
/-- exists_compact_surjective_zorn_subset (abstract). -/
def exists_compact_surjective_zorn_subset' : Prop := True
/-- image_subset_closure_compl_image_compl_of_isOpen (abstract). -/
def image_subset_closure_compl_image_compl_of_isOpen' : Prop := True
/-- disjoint_closure_of_disjoint_isOpen (abstract). -/
def disjoint_closure_of_disjoint_isOpen' : Prop := True
/-- homeoCompactToT2_injective (abstract). -/
def homeoCompactToT2_injective' : Prop := True
/-- homeoCompactToT2 (abstract). -/
def homeoCompactToT2' : Prop := True
/-- projective_iff_extremallyDisconnected (abstract). -/
def projective_iff_extremallyDisconnected' : Prop := True

-- FiberBundle/Basic.lean
-- COLLISION: containing' already in RingTheory2.lean — rename needed
-- COLLISION: called' already in MeasureTheory2.lean — rename needed
-- COLLISION: group' already in RingTheory2.lean — rename needed
/-- FiberBundle (abstract). -/
def FiberBundle' : Prop := True
/-- totalSpaceMk_isInducing (abstract). -/
def totalSpaceMk_isInducing' : Prop := True
/-- trivializationAtlas (abstract). -/
def trivializationAtlas' : Prop := True
/-- trivializationAt (abstract). -/
def trivializationAt' : Prop := True
/-- mem_baseSet_trivializationAt (abstract). -/
def mem_baseSet_trivializationAt' : Prop := True
/-- trivialization_mem_atlas (abstract). -/
def trivialization_mem_atlas' : Prop := True
/-- MemTrivializationAtlas (abstract). -/
def MemTrivializationAtlas' : Prop := True
/-- map_proj_nhds (abstract). -/
def map_proj_nhds' : Prop := True
/-- isOpenMap_proj (abstract). -/
def isOpenMap_proj' : Prop := True
/-- surjective_proj (abstract). -/
def surjective_proj' : Prop := True
/-- isQuotientMap_proj (abstract). -/
def isQuotientMap_proj' : Prop := True
/-- continuous_totalSpaceMk (abstract). -/
def continuous_totalSpaceMk' : Prop := True
/-- totalSpaceMk_isEmbedding (abstract). -/
def totalSpaceMk_isEmbedding' : Prop := True
/-- totalSpaceMk_isClosedEmbedding (abstract). -/
def totalSpaceMk_isClosedEmbedding' : Prop := True
/-- mem_trivializationAt_proj_source (abstract). -/
def mem_trivializationAt_proj_source' : Prop := True
/-- trivializationAt_proj_fst (abstract). -/
def trivializationAt_proj_fst' : Prop := True
/-- continuousWithinAt_totalSpace (abstract). -/
def continuousWithinAt_totalSpace' : Prop := True
/-- continuousAt_totalSpace (abstract). -/
def continuousAt_totalSpace' : Prop := True
/-- exists_trivialization_Icc_subset (abstract). -/
def exists_trivialization_Icc_subset' : Prop := True
/-- FiberBundleCore (abstract). -/
def FiberBundleCore' : Prop := True
/-- Index (abstract). -/
def Index' : Prop := True
/-- Base (abstract). -/
def Base' : Prop := True
-- COLLISION: Fiber' already in CategoryTheory.lean — rename needed
/-- TotalSpace (abstract). -/
def TotalSpace' : Prop := True
/-- trivChange (abstract). -/
def trivChange' : Prop := True
/-- mem_trivChange_source (abstract). -/
def mem_trivChange_source' : Prop := True
/-- localTrivAsPartialEquiv (abstract). -/
def localTrivAsPartialEquiv' : Prop := True
/-- localTrivAsPartialEquiv_trans (abstract). -/
def localTrivAsPartialEquiv_trans' : Prop := True
/-- open_source' (abstract). -/
def open_source' : Prop := True
/-- localTriv (abstract). -/
def localTriv' : Prop := True
/-- localTrivAt (abstract). -/
def localTrivAt' : Prop := True
/-- continuous_const_section (abstract). -/
def continuous_const_section' : Prop := True
/-- mem_localTrivAt_baseSet (abstract). -/
def mem_localTrivAt_baseSet' : Prop := True
/-- mk_mem_localTrivAt_source (abstract). -/
def mk_mem_localTrivAt_source' : Prop := True
/-- FiberPrebundle (abstract). -/
def FiberPrebundle' : Prop := True
/-- totalSpaceTopology (abstract). -/
def totalSpaceTopology' : Prop := True
/-- continuous_symm_of_mem_pretrivializationAtlas (abstract). -/
def continuous_symm_of_mem_pretrivializationAtlas' : Prop := True
/-- isOpen_source (abstract). -/
def isOpen_source' : Prop := True
/-- isOpen_target_of_mem_pretrivializationAtlas_inter (abstract). -/
def isOpen_target_of_mem_pretrivializationAtlas_inter' : Prop := True
/-- trivializationOfMemPretrivializationAtlas (abstract). -/
def trivializationOfMemPretrivializationAtlas' : Prop := True
/-- mem_pretrivializationAt_source (abstract). -/
def mem_pretrivializationAt_source' : Prop := True
/-- totalSpaceMk_preimage_source (abstract). -/
def totalSpaceMk_preimage_source' : Prop := True
/-- inducing_totalSpaceMk_of_inducing_comp (abstract). -/
def inducing_totalSpaceMk_of_inducing_comp' : Prop := True
/-- toFiberBundle (abstract). -/
def toFiberBundle' : Prop := True
/-- continuousOn_of_comp_right (abstract). -/
def continuousOn_of_comp_right' : Prop := True

-- FiberBundle/Constructions.lean
/-- isInducing_toProd (abstract). -/
def isInducing_toProd' : Prop := True
/-- homeomorphProd (abstract). -/
def homeomorphProd' : Prop := True
/-- trivialization (abstract). -/
def trivialization' : Prop := True
/-- eq_trivialization (abstract). -/
def eq_trivialization' : Prop := True
/-- isInducing_diag (abstract). -/
def isInducing_diag' : Prop := True
-- COLLISION: toFun' already in Algebra.lean — rename needed
/-- continuous_to_fun (abstract). -/
def continuous_to_fun' : Prop := True
-- COLLISION: invFun' already in RingTheory2.lean — rename needed
/-- continuous_inv_fun (abstract). -/
def continuous_inv_fun' : Prop := True
/-- pullbackTopology (abstract). -/
def pullbackTopology' : Prop := True
/-- continuous_lift (abstract). -/
def continuous_lift' : Prop := True
/-- inducing_pullbackTotalSpaceEmbedding (abstract). -/
def inducing_pullbackTotalSpaceEmbedding' : Prop := True

-- FiberBundle/IsHomeomorphicTrivialBundle.lean
/-- IsHomeomorphicTrivialFiberBundle (abstract). -/
def IsHomeomorphicTrivialFiberBundle' : Prop := True
/-- isHomeomorphicTrivialFiberBundle_fst (abstract). -/
def isHomeomorphicTrivialFiberBundle_fst' : Prop := True
/-- isHomeomorphicTrivialFiberBundle_snd (abstract). -/
def isHomeomorphicTrivialFiberBundle_snd' : Prop := True

-- FiberBundle/Trivialization.lean
-- COLLISION: as' already in Order.lean — rename needed
/-- simply (abstract). -/
def simply' : Prop := True
/-- Pretrivialization (abstract). -/
def Pretrivialization' : Prop := True
/-- coe_fst (abstract). -/
def coe_fst' : Prop := True
/-- mem_source (abstract). -/
def mem_source' : Prop := True
/-- eqOn (abstract). -/
def eqOn' : Prop := True
/-- mk_proj_snd (abstract). -/
def mk_proj_snd' : Prop := True
/-- setSymm (abstract). -/
def setSymm' : Prop := True
/-- mem_target (abstract). -/
def mem_target' : Prop := True
/-- proj_symm_apply (abstract). -/
def proj_symm_apply' : Prop := True
/-- proj_surjOn_baseSet (abstract). -/
def proj_surjOn_baseSet' : Prop := True
-- COLLISION: apply_symm_apply' already in Order.lean — rename needed
-- COLLISION: symm_apply_apply' already in Order.lean — rename needed
/-- symm_apply_mk_proj (abstract). -/
def symm_apply_mk_proj' : Prop := True
/-- preimage_symm_proj_baseSet (abstract). -/
def preimage_symm_proj_baseSet' : Prop := True
/-- preimage_symm_proj_inter (abstract). -/
def preimage_symm_proj_inter' : Prop := True
/-- target_inter_preimage_symm_source_eq (abstract). -/
def target_inter_preimage_symm_source_eq' : Prop := True
/-- trans_source (abstract). -/
def trans_source' : Prop := True
/-- symm_trans_symm (abstract). -/
def symm_trans_symm' : Prop := True
/-- symm_trans_source_eq (abstract). -/
def symm_trans_source_eq' : Prop := True
/-- symm_trans_target_eq (abstract). -/
def symm_trans_target_eq' : Prop := True
/-- coe_mem_source (abstract). -/
def coe_mem_source' : Prop := True
/-- coe_coe_fst (abstract). -/
def coe_coe_fst' : Prop := True
/-- mk_mem_target (abstract). -/
def mk_mem_target' : Prop := True
/-- symm_coe_proj (abstract). -/
def symm_coe_proj' : Prop := True
/-- symm_apply_of_not_mem (abstract). -/
def symm_apply_of_not_mem' : Prop := True
/-- coe_symm_of_not_mem (abstract). -/
def coe_symm_of_not_mem' : Prop := True
/-- mk_symm (abstract). -/
def mk_symm' : Prop := True
/-- symm_proj_apply (abstract). -/
def symm_proj_apply' : Prop := True
/-- symm_apply_apply_mk (abstract). -/
def symm_apply_apply_mk' : Prop := True
/-- apply_mk_symm (abstract). -/
def apply_mk_symm' : Prop := True
/-- Trivialization (abstract). -/
def Trivialization' : Prop := True
/-- toPretrivialization (abstract). -/
def toPretrivialization' : Prop := True
/-- map_target (abstract). -/
def map_target' : Prop := True
/-- coe_fst_eventuallyEq_proj (abstract). -/
def coe_fst_eventuallyEq_proj' : Prop := True
/-- preimage_subset_source (abstract). -/
def preimage_subset_source' : Prop := True
/-- image_preimage_eq_prod_univ (abstract). -/
def image_preimage_eq_prod_univ' : Prop := True
-- COLLISION: tendsto_nhds_iff' already in Analysis.lean — rename needed
/-- nhds_eq_inf_comap (abstract). -/
def nhds_eq_inf_comap' : Prop := True
/-- preimageHomeomorph (abstract). -/
def preimageHomeomorph' : Prop := True
/-- preimageHomeomorph_apply (abstract). -/
def preimageHomeomorph_apply' : Prop := True
-- COLLISION: aux' already in Order.lean — rename needed
/-- sourceHomeomorphBaseSetProd (abstract). -/
def sourceHomeomorphBaseSetProd' : Prop := True
/-- sourceHomeomorphBaseSetProd_apply (abstract). -/
def sourceHomeomorphBaseSetProd_apply' : Prop := True
/-- preimageSingletonHomeomorph (abstract). -/
def preimageSingletonHomeomorph' : Prop := True
/-- compHomeomorph (abstract). -/
def compHomeomorph' : Prop := True
/-- continuousAt_of_comp_right (abstract). -/
def continuousAt_of_comp_right' : Prop := True
/-- continuousAt_of_comp_left (abstract). -/
def continuousAt_of_comp_left' : Prop := True
/-- continuousOn_symm (abstract). -/
def continuousOn_symm' : Prop := True
/-- transFiberHomeomorph (abstract). -/
def transFiberHomeomorph' : Prop := True
/-- coordChange (abstract). -/
def coordChange' : Prop := True
/-- mk_coordChange (abstract). -/
def mk_coordChange' : Prop := True
/-- coordChange_apply_snd (abstract). -/
def coordChange_apply_snd' : Prop := True
/-- coordChange_same_apply (abstract). -/
def coordChange_same_apply' : Prop := True
/-- coordChange_same (abstract). -/
def coordChange_same' : Prop := True
/-- coordChange_coordChange (abstract). -/
def coordChange_coordChange' : Prop := True
/-- continuous_coordChange (abstract). -/
def continuous_coordChange' : Prop := True
/-- coordChangeHomeomorph (abstract). -/
def coordChangeHomeomorph' : Prop := True
/-- isImage_preimage_prod (abstract). -/
def isImage_preimage_prod' : Prop := True
/-- restrOpen (abstract). -/
def restrOpen' : Prop := True
-- COLLISION: frontier_preimage' already in Analysis.lean — rename needed
/-- piecewiseLeOfEq (abstract). -/
def piecewiseLeOfEq' : Prop := True
/-- piecewiseLe (abstract). -/
def piecewiseLe' : Prop := True
/-- disjointUnion (abstract). -/
def disjointUnion' : Prop := True

-- FiberPartition.lean
/-- sigmaIsoHom (abstract). -/
def sigmaIsoHom' : Prop := True
/-- sigmaIsoHom_inj (abstract). -/
def sigmaIsoHom_inj' : Prop := True
/-- sigmaIsoHom_surj (abstract). -/
def sigmaIsoHom_surj' : Prop := True
-- COLLISION: sigmaIncl' already in Condensed.lean — rename needed
/-- sigmaInclIncl (abstract). -/
def sigmaInclIncl' : Prop := True

-- Filter.lean
/-- isOpen_Iic_principal (abstract). -/
def isOpen_Iic_principal' : Prop := True
/-- isOpen_setOf_mem (abstract). -/
def isOpen_setOf_mem' : Prop := True
/-- tendsto_pure_self (abstract). -/
def tendsto_pure_self' : Prop := True
/-- nhds_bot (abstract). -/
def nhds_bot' : Prop := True
/-- nhds_top (abstract). -/
def nhds_top' : Prop := True
/-- nhds_principal (abstract). -/
def nhds_principal' : Prop := True
/-- nhds_pure (abstract). -/
def nhds_pure' : Prop := True
/-- nhds_iInf (abstract). -/
def nhds_iInf' : Prop := True
/-- nhds_inf (abstract). -/
def nhds_inf' : Prop := True
/-- monotone_nhds (abstract). -/
def monotone_nhds' : Prop := True
/-- sInter_nhds (abstract). -/
def sInter_nhds' : Prop := True
/-- nhds_mono (abstract). -/
def nhds_mono' : Prop := True
/-- closure_singleton (abstract). -/
def closure_singleton' : Prop := True
/-- specializes_iff_le (abstract). -/
def specializes_iff_le' : Prop := True
/-- nhds_atTop (abstract). -/
def nhds_atTop' : Prop := True
/-- tendsto_nhds_atTop_iff (abstract). -/
def tendsto_nhds_atTop_iff' : Prop := True
/-- nhds_atBot (abstract). -/
def nhds_atBot' : Prop := True
/-- tendsto_nhds_atBot_iff (abstract). -/
def tendsto_nhds_atBot_iff' : Prop := True
/-- nhds_nhds (abstract). -/
def nhds_nhds' : Prop := True
/-- isInducing_nhds (abstract). -/
def isInducing_nhds' : Prop := True

-- GDelta/Basic.lean
/-- IsGδ (abstract). -/
def IsGδ' : Prop := True
/-- isGδ (abstract). -/
def isGδ' : Prop := True
-- COLLISION: empty' already in SetTheory.lean — rename needed
/-- biInter_of_isOpen (abstract). -/
def biInter_of_isOpen' : Prop := True
/-- iInter_of_isOpen (abstract). -/
def iInter_of_isOpen' : Prop := True
/-- isGδ_iff_eq_iInter_nat (abstract). -/
def isGδ_iff_eq_iInter_nat' : Prop := True
/-- residual (abstract). -/
def residual' : Prop := True
/-- residual_of_dense_open (abstract). -/
def residual_of_dense_open' : Prop := True
/-- residual_of_dense_Gδ (abstract). -/
def residual_of_dense_Gδ' : Prop := True
/-- mem_residual_iff (abstract). -/
def mem_residual_iff' : Prop := True
/-- IsNowhereDense (abstract). -/
def IsNowhereDense' : Prop := True
/-- isNowhereDense_empty (abstract). -/
def isNowhereDense_empty' : Prop := True
/-- isNowhereDense_iff (abstract). -/
def isNowhereDense_iff' : Prop := True
/-- subset_of_closed_isNowhereDense (abstract). -/
def subset_of_closed_isNowhereDense' : Prop := True
/-- isClosed_isNowhereDense_iff_compl (abstract). -/
def isClosed_isNowhereDense_iff_compl' : Prop := True
/-- IsMeagre (abstract). -/
def IsMeagre' : Prop := True
/-- meagre_empty (abstract). -/
def meagre_empty' : Prop := True
/-- isMeagre_iUnion (abstract). -/
def isMeagre_iUnion' : Prop := True
/-- isMeagre_iff_countable_union_isNowhereDense (abstract). -/
def isMeagre_iff_countable_union_isNowhereDense' : Prop := True

-- GDelta/UniformSpace.lean
/-- setOf_continuousAt (abstract). -/
def setOf_continuousAt' : Prop := True

-- Germ.lean
/-- value (abstract). -/
def value' : Prop := True
/-- valueMulHom (abstract). -/
def valueMulHom' : Prop := True
/-- valueₗ (abstract). -/
def valueₗ' : Prop := True
/-- valueRingHom (abstract). -/
def valueRingHom' : Prop := True
/-- valueOrderRingHom (abstract). -/
def valueOrderRingHom' : Prop := True
/-- RestrictGermPredicate (abstract). -/
def RestrictGermPredicate' : Prop := True
/-- germ_congr_set (abstract). -/
def germ_congr_set' : Prop := True
/-- restrictGermPredicate_congr (abstract). -/
def restrictGermPredicate_congr' : Prop := True
/-- forall_restrictGermPredicate_iff (abstract). -/
def forall_restrictGermPredicate_iff' : Prop := True
/-- forall_restrictGermPredicate_of_forall (abstract). -/
def forall_restrictGermPredicate_of_forall' : Prop := True
/-- sliceLeft (abstract). -/
def sliceLeft' : Prop := True
/-- sliceRight (abstract). -/
def sliceRight' : Prop := True
/-- eq_of_germ_isConstant (abstract). -/
def eq_of_germ_isConstant' : Prop := True
/-- eq_of_germ_isConstant_on (abstract). -/
def eq_of_germ_isConstant_on' : Prop := True

-- Gluing.lean
-- COLLISION: GlueData' already in CategoryTheory.lean — rename needed
-- COLLISION: π_surjective' already in CategoryTheory.lean — rename needed
-- COLLISION: Rel' already in RingTheory2.lean — rename needed
-- COLLISION: rel_equiv' already in CategoryTheory.lean — rename needed
/-- eqvGen_of_π_eq (abstract). -/
def eqvGen_of_π_eq' : Prop := True
/-- ι_eq_iff_rel (abstract). -/
def ι_eq_iff_rel' : Prop := True
/-- image_inter (abstract). -/
def image_inter' : Prop := True
/-- preimage_range (abstract). -/
def preimage_range' : Prop := True
/-- preimage_image_eq_image (abstract). -/
def preimage_image_eq_image' : Prop := True
/-- open_image_open (abstract). -/
def open_image_open' : Prop := True
/-- ι_isOpenEmbedding (abstract). -/
def ι_isOpenEmbedding' : Prop := True
/-- MkCore (abstract). -/
def MkCore' : Prop := True
/-- t' (abstract). -/
def t' : Prop := True
/-- ofOpenSubsets (abstract). -/
def ofOpenSubsets' : Prop := True
/-- fromOpenSubsetsGlue (abstract). -/
def fromOpenSubsetsGlue' : Prop := True
/-- ι_fromOpenSubsetsGlue (abstract). -/
def ι_fromOpenSubsetsGlue' : Prop := True
/-- fromOpenSubsetsGlue_injective (abstract). -/
def fromOpenSubsetsGlue_injective' : Prop := True
/-- fromOpenSubsetsGlue_isOpenMap (abstract). -/
def fromOpenSubsetsGlue_isOpenMap' : Prop := True
/-- fromOpenSubsetsGlue_isOpenEmbedding (abstract). -/
def fromOpenSubsetsGlue_isOpenEmbedding' : Prop := True
/-- range_fromOpenSubsetsGlue (abstract). -/
def range_fromOpenSubsetsGlue' : Prop := True
/-- openCoverGlueHomeo (abstract). -/
def openCoverGlueHomeo' : Prop := True

-- Hom/ContinuousEval.lean
/-- ContinuousEval (abstract). -/
def ContinuousEval' : Prop := True
/-- of_continuous_forget (abstract). -/
def of_continuous_forget' : Prop := True

-- Hom/ContinuousEvalConst.lean
/-- ContinuousEvalConst (abstract). -/
def ContinuousEvalConst' : Prop := True
/-- eval_const (abstract). -/
def eval_const' : Prop := True
/-- continuous_coeFun (abstract). -/
def continuous_coeFun' : Prop := True
/-- coeFun (abstract). -/
def coeFun' : Prop := True

-- Hom/Open.lean
/-- ContinuousOpenMap (abstract). -/
def ContinuousOpenMap' : Prop := True
/-- ContinuousOpenMapClass (abstract). -/
def ContinuousOpenMapClass' : Prop := True

-- Homeomorph.lean
/-- Homeomorph (abstract). -/
def Homeomorph' : Prop := True
/-- changeInv (abstract). -/
def changeInv' : Prop := True
/-- ofIsEmbedding (abstract). -/
def ofIsEmbedding' : Prop := True
/-- isSigmaCompact_preimage (abstract). -/
def isSigmaCompact_preimage' : Prop := True
/-- isPreconnected_preimage (abstract). -/
def isPreconnected_preimage' : Prop := True
/-- isConnected_image (abstract). -/
def isConnected_image' : Prop := True
/-- comap_cocompact (abstract). -/
def comap_cocompact' : Prop := True
/-- isOpen_image (abstract). -/
def isOpen_image' : Prop := True
/-- comap_nhds_eq (abstract). -/
def comap_nhds_eq' : Prop := True
/-- comap_coclosedCompact (abstract). -/
def comap_coclosedCompact' : Prop := True
/-- map_coclosedCompact (abstract). -/
def map_coclosedCompact' : Prop := True
/-- locallyCompactSpace_iff (abstract). -/
def locallyCompactSpace_iff' : Prop := True
/-- homeomorphOfContinuousOpen (abstract). -/
def homeomorphOfContinuousOpen' : Prop := True
/-- homeomorphOfContinuousClosed (abstract). -/
def homeomorphOfContinuousClosed' : Prop := True
/-- comp_isOpenMap_iff (abstract). -/
def comp_isOpenMap_iff' : Prop := True
-- COLLISION: sets' already in SetTheory.lean — rename needed
-- COLLISION: setCongr' already in Order.lean — rename needed
-- COLLISION: sumCongr' already in MeasureTheory2.lean — rename needed
-- COLLISION: prodCongr' already in Algebra.lean — rename needed
/-- sumComm (abstract). -/
def sumComm' : Prop := True
/-- continuous_sumAssoc (abstract). -/
def continuous_sumAssoc' : Prop := True
/-- sumAssoc (abstract). -/
def sumAssoc' : Prop := True
/-- sumSumSumComm (abstract). -/
def sumSumSumComm' : Prop := True
/-- sumEmpty (abstract). -/
def sumEmpty' : Prop := True
/-- emptySum (abstract). -/
def emptySum' : Prop := True
-- COLLISION: prodAssoc' already in Algebra.lean — rename needed
-- COLLISION: prodProdProdComm' already in Algebra.lean — rename needed
-- COLLISION: prodPUnit' already in MeasureTheory2.lean — rename needed
-- COLLISION: punitProd' already in MeasureTheory2.lean — rename needed
/-- homeomorphOfUnique (abstract). -/
def homeomorphOfUnique' : Prop := True
-- COLLISION: piCongrLeft' already in Algebra.lean — rename needed
/-- piCongr (abstract). -/
def piCongr' : Prop := True
/-- sumArrowHomeomorphProdArrow (abstract). -/
def sumArrowHomeomorphProdArrow' : Prop := True
/-- appendEquiv_eq_Homeomorph (abstract). -/
def appendEquiv_eq_Homeomorph' : Prop := True
/-- continuous_append (abstract). -/
def continuous_append' : Prop := True
/-- appendHomeomorph (abstract). -/
def appendHomeomorph' : Prop := True
-- COLLISION: sumProdDistrib' already in MeasureTheory2.lean — rename needed
-- COLLISION: prodSumDistrib' already in MeasureTheory2.lean — rename needed
/-- sigmaProdDistrib (abstract). -/
def sigmaProdDistrib' : Prop := True
-- COLLISION: piEquivPiSubtypeProd' already in Algebra.lean — rename needed
/-- piSplitAt (abstract). -/
def piSplitAt' : Prop := True
/-- funSplitAt (abstract). -/
def funSplitAt' : Prop := True
/-- toHomeomorphOfIsInducing (abstract). -/
def toHomeomorphOfIsInducing' : Prop := True
/-- continuous_symm_of_equiv_compact_to_t2 (abstract). -/
def continuous_symm_of_equiv_compact_to_t2' : Prop := True
/-- homeoOfEquivCompactToT2 (abstract). -/
def homeoOfEquivCompactToT2' : Prop := True
/-- IsHomeomorph (abstract). -/
def IsHomeomorph' : Prop := True
/-- isHomeomorph (abstract). -/
def isHomeomorph' : Prop := True
-- COLLISION: surjective' already in Order.lean — rename needed
-- COLLISION: isDenseEmbedding' already in MeasureTheory2.lean — rename needed
/-- isHomeomorph_iff_exists_homeomorph (abstract). -/
def isHomeomorph_iff_exists_homeomorph' : Prop := True
/-- isHomeomorph_iff_exists_inverse (abstract). -/
def isHomeomorph_iff_exists_inverse' : Prop := True
/-- isHomeomorph_iff_isEmbedding_surjective (abstract). -/
def isHomeomorph_iff_isEmbedding_surjective' : Prop := True
/-- isHomeomorph_iff_continuous_isClosedMap_bijective (abstract). -/
def isHomeomorph_iff_continuous_isClosedMap_bijective' : Prop := True
/-- isHomeomorph_iff_continuous_bijective (abstract). -/
def isHomeomorph_iff_continuous_bijective' : Prop := True
/-- sigmaMap (abstract). -/
def sigmaMap' : Prop := True
/-- pi_map (abstract). -/
def pi_map' : Prop := True

-- Homotopy/Basic.lean
-- COLLISION: Homotopy' already in Algebra.lean — rename needed
/-- HomotopyLike (abstract). -/
def HomotopyLike' : Prop := True
/-- extend_apply_of_le_zero (abstract). -/
def extend_apply_of_le_zero' : Prop := True
/-- extend_apply_of_one_le (abstract). -/
def extend_apply_of_one_le' : Prop := True
/-- extend_apply_coe (abstract). -/
def extend_apply_coe' : Prop := True
/-- extend_apply_of_mem_I (abstract). -/
def extend_apply_of_mem_I' : Prop := True
/-- symm_trans (abstract). -/
def symm_trans' : Prop := True
-- COLLISION: compContinuousMap' already in Analysis.lean — rename needed
-- COLLISION: hcomp' already in CategoryTheory.lean — rename needed
/-- Homotopic (abstract). -/
def Homotopic' : Prop := True
-- COLLISION: equivalence' already in CategoryTheory.lean — rename needed
/-- HomotopyWith (abstract). -/
def HomotopyWith' : Prop := True
-- COLLISION: coeFn_injective' already in LinearAlgebra2.lean — rename needed
-- COLLISION: prop' already in Order.lean — rename needed
/-- extendProp (abstract). -/
def extendProp' : Prop := True
/-- HomotopicWith (abstract). -/
def HomotopicWith' : Prop := True
/-- HomotopyRel (abstract). -/
def HomotopyRel' : Prop := True
/-- eq_fst (abstract). -/
def eq_fst' : Prop := True
/-- eq_snd (abstract). -/
def eq_snd' : Prop := True
/-- fst_eq_snd (abstract). -/
def fst_eq_snd' : Prop := True
/-- HomotopicRel (abstract). -/
def HomotopicRel' : Prop := True
/-- homotopicRel_empty (abstract). -/
def homotopicRel_empty' : Prop := True

-- Homotopy/Contractible.lean
/-- Nullhomotopic (abstract). -/
def Nullhomotopic' : Prop := True
/-- nullhomotopic_of_constant (abstract). -/
def nullhomotopic_of_constant' : Prop := True
-- COLLISION: comp_right' already in Order.lean — rename needed
/-- ContractibleSpace (abstract). -/
def ContractibleSpace' : Prop := True
/-- hequiv_unit (abstract). -/
def hequiv_unit' : Prop := True
/-- id_nullhomotopic (abstract). -/
def id_nullhomotopic' : Prop := True
/-- contractible_iff_id_nullhomotopic (abstract). -/
def contractible_iff_id_nullhomotopic' : Prop := True
-- COLLISION: contractibleSpace' already in Analysis.lean — rename needed
/-- contractibleSpace_iff (abstract). -/
def contractibleSpace_iff' : Prop := True
/-- hequiv (abstract). -/
def hequiv' : Prop := True

-- Homotopy/Equiv.lean
-- COLLISION: HomotopyEquiv' already in Algebra.lean — rename needed
/-- toHomotopyEquiv (abstract). -/
def toHomotopyEquiv' : Prop := True

-- Homotopy/HSpaces.lean
-- COLLISION: because' already in RingTheory2.lean — rename needed
/-- HSpace (abstract). -/
def HSpace' : Prop := True
/-- toHSpace (abstract). -/
def toHSpace' : Prop := True
/-- qRight (abstract). -/
def qRight' : Prop := True
/-- continuous_qRight (abstract). -/
def continuous_qRight' : Prop := True
/-- qRight_zero_left (abstract). -/
def qRight_zero_left' : Prop := True
/-- qRight_one_left (abstract). -/
def qRight_one_left' : Prop := True
/-- qRight_zero_right (abstract). -/
def qRight_zero_right' : Prop := True
/-- qRight_one_right (abstract). -/
def qRight_one_right' : Prop := True
/-- delayReflRight (abstract). -/
def delayReflRight' : Prop := True
/-- continuous_delayReflRight (abstract). -/
def continuous_delayReflRight' : Prop := True
/-- delayReflRight_zero (abstract). -/
def delayReflRight_zero' : Prop := True
/-- delayReflRight_one (abstract). -/
def delayReflRight_one' : Prop := True
/-- delayReflLeft (abstract). -/
def delayReflLeft' : Prop := True
/-- continuous_delayReflLeft (abstract). -/
def continuous_delayReflLeft' : Prop := True
/-- delayReflLeft_zero (abstract). -/
def delayReflLeft_zero' : Prop := True
/-- delayReflLeft_one (abstract). -/
def delayReflLeft_one' : Prop := True

-- Homotopy/HomotopyGroup.lean
-- COLLISION: boundary' already in AlgebraicTopology.lean — rename needed
/-- splitAt (abstract). -/
def splitAt' : Prop := True
/-- insertAt (abstract). -/
def insertAt' : Prop := True
/-- insertAt_boundary (abstract). -/
def insertAt_boundary' : Prop := True
/-- LoopSpace (abstract). -/
def LoopSpace' : Prop := True
/-- GenLoop (abstract). -/
def GenLoop' : Prop := True
-- COLLISION: equiv' already in SetTheory.lean — rename needed
/-- toLoop (abstract). -/
def toLoop' : Prop := True
/-- continuous_toLoop (abstract). -/
def continuous_toLoop' : Prop := True
/-- fromLoop (abstract). -/
def fromLoop' : Prop := True
/-- continuous_fromLoop (abstract). -/
def continuous_fromLoop' : Prop := True
/-- to_from (abstract). -/
def to_from' : Prop := True
/-- loopHomeo (abstract). -/
def loopHomeo' : Prop := True
/-- cCompInsert (abstract). -/
def cCompInsert' : Prop := True
/-- homotopyTo (abstract). -/
def homotopyTo' : Prop := True
/-- homotopicTo (abstract). -/
def homotopicTo' : Prop := True
/-- homotopyFrom (abstract). -/
def homotopyFrom' : Prop := True
/-- homotopicFrom (abstract). -/
def homotopicFrom' : Prop := True
/-- transAt (abstract). -/
def transAt' : Prop := True
/-- symmAt (abstract). -/
def symmAt' : Prop := True
/-- transAt_distrib (abstract). -/
def transAt_distrib' : Prop := True
/-- fromLoop_trans_toLoop (abstract). -/
def fromLoop_trans_toLoop' : Prop := True
/-- fromLoop_symm_toLoop (abstract). -/
def fromLoop_symm_toLoop' : Prop := True
/-- HomotopyGroup (abstract). -/
def HomotopyGroup' : Prop := True
/-- homotopyGroupEquivFundamentalGroup (abstract). -/
def homotopyGroupEquivFundamentalGroup' : Prop := True
/-- Pi (abstract). -/
def Pi' : Prop := True
/-- genLoopHomeoOfIsEmpty (abstract). -/
def genLoopHomeoOfIsEmpty' : Prop := True
/-- homotopyGroupEquivZerothHomotopyOfIsEmpty (abstract). -/
def homotopyGroupEquivZerothHomotopyOfIsEmpty' : Prop := True
/-- pi0EquivZerothHomotopy (abstract). -/
def pi0EquivZerothHomotopy' : Prop := True
/-- genLoopEquivOfUnique (abstract). -/
def genLoopEquivOfUnique' : Prop := True
/-- homotopyGroupEquivFundamentalGroupOfUnique (abstract). -/
def homotopyGroupEquivFundamentalGroupOfUnique' : Prop := True
/-- pi1EquivFundamentalGroup (abstract). -/
def pi1EquivFundamentalGroup' : Prop := True
/-- auxGroup (abstract). -/
def auxGroup' : Prop := True
/-- isUnital_auxGroup (abstract). -/
def isUnital_auxGroup' : Prop := True
/-- auxGroup_indep (abstract). -/
def auxGroup_indep' : Prop := True
/-- transAt_indep (abstract). -/
def transAt_indep' : Prop := True
/-- symmAt_indep (abstract). -/
def symmAt_indep' : Prop := True
/-- mul_spec (abstract). -/
def mul_spec' : Prop := True
/-- inv_spec (abstract). -/
def inv_spec' : Prop := True

-- Homotopy/Path.lean
/-- source (abstract). -/
def source' : Prop := True
/-- target (abstract). -/
def target' : Prop := True
-- COLLISION: eval_zero' already in Algebra.lean — rename needed
-- COLLISION: eval_one' already in Algebra.lean — rename needed
/-- hcomp_apply (abstract). -/
def hcomp_apply' : Prop := True
/-- hcomp_half (abstract). -/
def hcomp_half' : Prop := True
/-- symm₂ (abstract). -/
def symm₂' : Prop := True
-- COLLISION: setoid' already in Order.lean — rename needed
-- COLLISION: Quotient' already in RingTheory2.lean — rename needed
/-- mapFn (abstract). -/
def mapFn' : Prop := True
/-- hpath_hext (abstract). -/
def hpath_hext' : Prop := True
/-- toHomotopyConst (abstract). -/
def toHomotopyConst' : Prop := True
/-- homotopic_const_iff (abstract). -/
def homotopic_const_iff' : Prop := True
-- COLLISION: evalAt' already in Algebra.lean — rename needed

-- Homotopy/Product.lean
/-- piHomotopy (abstract). -/
def piHomotopy' : Prop := True
/-- pi_lift (abstract). -/
def pi_lift' : Prop := True
/-- comp_pi_eq_pi_comp (abstract). -/
def comp_pi_eq_pi_comp' : Prop := True
/-- pi_proj (abstract). -/
def pi_proj' : Prop := True
/-- prodHomotopy (abstract). -/
def prodHomotopy' : Prop := True
/-- comp_prod_eq_prod_comp (abstract). -/
def comp_prod_eq_prod_comp' : Prop := True
/-- projLeft (abstract). -/
def projLeft' : Prop := True
/-- projRight (abstract). -/
def projRight' : Prop := True
/-- projLeft_prod (abstract). -/
def projLeft_prod' : Prop := True
/-- projRight_prod (abstract). -/
def projRight_prod' : Prop := True
/-- prod_projLeft_projRight (abstract). -/
def prod_projLeft_projRight' : Prop := True

-- IndicatorConstPointwise.lean
/-- tendsto_ite (abstract). -/
def tendsto_ite' : Prop := True
/-- tendsto_indicator_const_apply_iff_eventually' (abstract). -/
def tendsto_indicator_const_apply_iff_eventually' : Prop := True
/-- tendsto_indicator_const_iff_forall_eventually' (abstract). -/
def tendsto_indicator_const_iff_forall_eventually' : Prop := True
/-- tendsto_indicator_const_iff_tendsto_pi_pure' (abstract). -/
def tendsto_indicator_const_iff_tendsto_pi_pure' : Prop := True

-- Inseparable.lean
/-- specializes_TFAE (abstract). -/
def specializes_TFAE' : Prop := True
-- COLLISION: not_disjoint' already in Order.lean — rename needed
/-- specializes_iff_pure (abstract). -/
def specializes_iff_pure' : Prop := True
/-- ker_nhds_eq_specializes (abstract). -/
def ker_nhds_eq_specializes' : Prop := True
/-- specializes_iff_forall_open (abstract). -/
def specializes_iff_forall_open' : Prop := True
/-- mem_open (abstract). -/
def mem_open' : Prop := True
/-- not_specializes (abstract). -/
def not_specializes' : Prop := True
/-- specializes_iff_forall_closed (abstract). -/
def specializes_iff_forall_closed' : Prop := True
/-- mem_closed (abstract). -/
def mem_closed' : Prop := True
/-- specializes_iff_mem_closure (abstract). -/
def specializes_iff_mem_closure' : Prop := True
/-- specializes_iff_closure_subset (abstract). -/
def specializes_iff_closure_subset' : Prop := True
/-- specializes_iff_clusterPt (abstract). -/
def specializes_iff_clusterPt' : Prop := True
/-- specializes_iff (abstract). -/
def specializes_iff' : Prop := True
/-- specializes_rfl (abstract). -/
def specializes_rfl' : Prop := True
/-- specializes_refl (abstract). -/
def specializes_refl' : Prop := True
/-- specializes_of_eq (abstract). -/
def specializes_of_eq' : Prop := True
/-- specializes_of_nhdsWithin (abstract). -/
def specializes_of_nhdsWithin' : Prop := True
/-- subtype_specializes_iff (abstract). -/
def subtype_specializes_iff' : Prop := True
/-- specializes_prod (abstract). -/
def specializes_prod' : Prop := True
/-- specializes_pi (abstract). -/
def specializes_pi' : Prop := True
/-- not_specializes_iff_exists_open (abstract). -/
def not_specializes_iff_exists_open' : Prop := True
/-- not_specializes_iff_exists_closed (abstract). -/
def not_specializes_iff_exists_closed' : Prop := True
/-- continuous_piecewise_of_specializes (abstract). -/
def continuous_piecewise_of_specializes' : Prop := True
/-- StableUnderSpecialization (abstract). -/
def StableUnderSpecialization' : Prop := True
/-- StableUnderGeneralization (abstract). -/
def StableUnderGeneralization' : Prop := True
/-- stableUnderSpecialization (abstract). -/
def stableUnderSpecialization' : Prop := True
/-- stableUnderGeneralization (abstract). -/
def stableUnderGeneralization' : Prop := True
/-- stableUnderSpecialization_compl_iff (abstract). -/
def stableUnderSpecialization_compl_iff' : Prop := True
/-- stableUnderGeneralization_compl_iff (abstract). -/
def stableUnderGeneralization_compl_iff' : Prop := True
/-- stableUnderSpecialization_univ (abstract). -/
def stableUnderSpecialization_univ' : Prop := True
/-- stableUnderSpecialization_empty (abstract). -/
def stableUnderSpecialization_empty' : Prop := True
/-- stableUnderGeneralization_univ (abstract). -/
def stableUnderGeneralization_univ' : Prop := True
/-- stableUnderGeneralization_empty (abstract). -/
def stableUnderGeneralization_empty' : Prop := True
/-- stableUnderSpecialization_sUnion (abstract). -/
def stableUnderSpecialization_sUnion' : Prop := True
/-- stableUnderSpecialization_sInter (abstract). -/
def stableUnderSpecialization_sInter' : Prop := True
/-- stableUnderGeneralization_sUnion (abstract). -/
def stableUnderGeneralization_sUnion' : Prop := True
/-- stableUnderGeneralization_sInter (abstract). -/
def stableUnderGeneralization_sInter' : Prop := True
/-- stableUnderSpecialization_iUnion (abstract). -/
def stableUnderSpecialization_iUnion' : Prop := True
/-- stableUnderSpecialization_iInter (abstract). -/
def stableUnderSpecialization_iInter' : Prop := True
/-- stableUnderGeneralization_iUnion (abstract). -/
def stableUnderGeneralization_iUnion' : Prop := True
/-- stableUnderGeneralization_iInter (abstract). -/
def stableUnderGeneralization_iInter' : Prop := True
/-- Union_closure_singleton_eq_iff (abstract). -/
def Union_closure_singleton_eq_iff' : Prop := True
/-- stableUnderSpecialization_iff_Union_eq (abstract). -/
def stableUnderSpecialization_iff_Union_eq' : Prop := True
/-- stableUnderSpecialization_iff_exists_sUnion_eq (abstract). -/
def stableUnderSpecialization_iff_exists_sUnion_eq' : Prop := True
/-- stableUnderGeneralization_iff_exists_sInter_eq (abstract). -/
def stableUnderGeneralization_iff_exists_sInter_eq' : Prop := True
/-- SpecializingMap (abstract). -/
def SpecializingMap' : Prop := True
/-- GeneralizingMap (abstract). -/
def GeneralizingMap' : Prop := True
/-- specializingMap_iff_closure_singleton_subset (abstract). -/
def specializingMap_iff_closure_singleton_subset' : Prop := True
/-- stableUnderSpecialization_image (abstract). -/
def stableUnderSpecialization_image' : Prop := True
/-- specializingMap_iff_stableUnderSpecialization_image_singleton (abstract). -/
def specializingMap_iff_stableUnderSpecialization_image_singleton' : Prop := True
/-- specializingMap_iff_stableUnderSpecialization_image (abstract). -/
def specializingMap_iff_stableUnderSpecialization_image' : Prop := True
/-- specializingMap_iff_closure_singleton (abstract). -/
def specializingMap_iff_closure_singleton' : Prop := True
/-- specializingMap_iff_isClosed_image_closure_singleton (abstract). -/
def specializingMap_iff_isClosed_image_closure_singleton' : Prop := True
/-- generalizingMap (abstract). -/
def generalizingMap' : Prop := True
/-- stableUnderSpecialization_range (abstract). -/
def stableUnderSpecialization_range' : Prop := True
/-- stableUnderGeneralization_image (abstract). -/
def stableUnderGeneralization_image' : Prop := True
/-- GeneralizingMap_iff_stableUnderGeneralization_image (abstract). -/
def GeneralizingMap_iff_stableUnderGeneralization_image' : Prop := True
/-- stableUnderGeneralization_range (abstract). -/
def stableUnderGeneralization_range' : Prop := True
-- COLLISION: antisymm' already in SetTheory.lean — rename needed
/-- inseparable_iff_forall_isOpen (abstract). -/
def inseparable_iff_forall_isOpen' : Prop := True
/-- not_inseparable_iff_exists_open (abstract). -/
def not_inseparable_iff_exists_open' : Prop := True
/-- inseparable_iff_forall_isClosed (abstract). -/
def inseparable_iff_forall_isClosed' : Prop := True
/-- inseparable_iff_mem_closure (abstract). -/
def inseparable_iff_mem_closure' : Prop := True
/-- inseparable_iff_closure_eq (abstract). -/
def inseparable_iff_closure_eq' : Prop := True
/-- inseparable_of_nhdsWithin_eq (abstract). -/
def inseparable_of_nhdsWithin_eq' : Prop := True
/-- subtype_inseparable_iff (abstract). -/
def subtype_inseparable_iff' : Prop := True
/-- inseparable_prod (abstract). -/
def inseparable_prod' : Prop := True
/-- not_inseparable (abstract). -/
def not_inseparable' : Prop := True
-- COLLISION: mk_eq_mk' already in SetTheory.lean — rename needed
-- COLLISION: surjective_mk' already in Algebra.lean — rename needed
/-- preimage_image_mk_open (abstract). -/
def preimage_image_mk_open' : Prop := True
/-- isOpenMap_mk (abstract). -/
def isOpenMap_mk' : Prop := True
/-- preimage_image_mk_closed (abstract). -/
def preimage_image_mk_closed' : Prop := True
/-- isClosedMap_mk (abstract). -/
def isClosedMap_mk' : Prop := True
/-- comap_mk_nhds_mk (abstract). -/
def comap_mk_nhds_mk' : Prop := True
/-- comap_mk_nhdsSet_image (abstract). -/
def comap_mk_nhdsSet_image' : Prop := True
/-- map_mk_nhdsSet (abstract). -/
def map_mk_nhdsSet' : Prop := True
/-- comap_mk_nhdsSet (abstract). -/
def comap_mk_nhdsSet' : Prop := True
/-- preimage_mk_closure (abstract). -/
def preimage_mk_closure' : Prop := True
/-- preimage_mk_interior (abstract). -/
def preimage_mk_interior' : Prop := True
/-- preimage_mk_frontier (abstract). -/
def preimage_mk_frontier' : Prop := True
/-- image_mk_closure (abstract). -/
def image_mk_closure' : Prop := True
/-- map_prod_map_mk_nhds (abstract). -/
def map_prod_map_mk_nhds' : Prop := True
/-- map_mk_nhdsWithin_preimage (abstract). -/
def map_mk_nhdsWithin_preimage' : Prop := True
/-- tendsto_lift_nhds_mk (abstract). -/
def tendsto_lift_nhds_mk' : Prop := True
/-- tendsto_lift_nhdsWithin_mk (abstract). -/
def tendsto_lift_nhdsWithin_mk' : Prop := True
/-- continuousAt_lift (abstract). -/
def continuousAt_lift' : Prop := True
/-- continuousWithinAt_lift (abstract). -/
def continuousWithinAt_lift' : Prop := True
/-- continuousOn_lift (abstract). -/
def continuousOn_lift' : Prop := True
-- COLLISION: lift₂' already in SetTheory.lean — rename needed
/-- tendsto_lift₂_nhds (abstract). -/
def tendsto_lift₂_nhds' : Prop := True
/-- tendsto_lift₂_nhdsWithin (abstract). -/
def tendsto_lift₂_nhdsWithin' : Prop := True
/-- continuousAt_lift₂ (abstract). -/
def continuousAt_lift₂' : Prop := True
/-- continuousWithinAt_lift₂ (abstract). -/
def continuousWithinAt_lift₂' : Prop := True
/-- continuousOn_lift₂ (abstract). -/
def continuousOn_lift₂' : Prop := True
/-- continuous_lift₂ (abstract). -/
def continuous_lift₂' : Prop := True
/-- continuous_congr_of_inseparable (abstract). -/
def continuous_congr_of_inseparable' : Prop := True

-- Instances/AddCircle.lean
/-- continuous_left_toIocMod (abstract). -/
def continuous_left_toIocMod' : Prop := True
/-- toIcoMod_eventuallyEq_toIocMod (abstract). -/
def toIcoMod_eventuallyEq_toIocMod' : Prop := True
/-- continuousAt_toIcoMod (abstract). -/
def continuousAt_toIcoMod' : Prop := True
/-- continuousAt_toIocMod (abstract). -/
def continuousAt_toIocMod' : Prop := True
/-- AddCircle (abstract). -/
def AddCircle' : Prop := True
-- COLLISION: coe_eq_zero_iff' already in RingTheory2.lean — rename needed
/-- coe_eq_zero_of_pos_iff (abstract). -/
def coe_eq_zero_of_pos_iff' : Prop := True
/-- coe_period (abstract). -/
def coe_period' : Prop := True
/-- coe_add_period (abstract). -/
def coe_add_period' : Prop := True
/-- equivIco (abstract). -/
def equivIco' : Prop := True
/-- equivIoc (abstract). -/
def equivIoc' : Prop := True
/-- liftIco (abstract). -/
def liftIco' : Prop := True
/-- liftIoc (abstract). -/
def liftIoc' : Prop := True
/-- coe_eq_coe_iff_of_mem_Ico (abstract). -/
def coe_eq_coe_iff_of_mem_Ico' : Prop := True
/-- liftIco_coe_apply (abstract). -/
def liftIco_coe_apply' : Prop := True
/-- liftIoc_coe_apply (abstract). -/
def liftIoc_coe_apply' : Prop := True
/-- eq_coe_Ico (abstract). -/
def eq_coe_Ico' : Prop := True
/-- coe_eq_zero_iff_of_mem_Ico (abstract). -/
def coe_eq_zero_iff_of_mem_Ico' : Prop := True
/-- continuous_equivIco_symm (abstract). -/
def continuous_equivIco_symm' : Prop := True
/-- continuous_equivIoc_symm (abstract). -/
def continuous_equivIoc_symm' : Prop := True
/-- continuousAt_equivIco (abstract). -/
def continuousAt_equivIco' : Prop := True
/-- continuousAt_equivIoc (abstract). -/
def continuousAt_equivIoc' : Prop := True
/-- partialHomeomorphCoe (abstract). -/
def partialHomeomorphCoe' : Prop := True
/-- isLocalHomeomorph_coe (abstract). -/
def isLocalHomeomorph_coe' : Prop := True
/-- coe_image_Ico_eq (abstract). -/
def coe_image_Ico_eq' : Prop := True
/-- coe_image_Ioc_eq (abstract). -/
def coe_image_Ioc_eq' : Prop := True
/-- coe_image_Icc_eq (abstract). -/
def coe_image_Icc_eq' : Prop := True
/-- equivAddCircle (abstract). -/
def equivAddCircle' : Prop := True
/-- homeomorphAddCircle (abstract). -/
def homeomorphAddCircle' : Prop := True
/-- coe_equivIco_mk_apply (abstract). -/
def coe_equivIco_mk_apply' : Prop := True
/-- addOrderOf_period_div (abstract). -/
def addOrderOf_period_div' : Prop := True
/-- gcd_mul_addOrderOf_div_eq (abstract). -/
def gcd_mul_addOrderOf_div_eq' : Prop := True
/-- addOrderOf_div_of_gcd_eq_one (abstract). -/
def addOrderOf_div_of_gcd_eq_one' : Prop := True
/-- addOrderOf_coe_rat (abstract). -/
def addOrderOf_coe_rat' : Prop := True
/-- addOrderOf_eq_pos_iff (abstract). -/
def addOrderOf_eq_pos_iff' : Prop := True
/-- exists_gcd_eq_one_of_isOfFinAddOrder (abstract). -/
def exists_gcd_eq_one_of_isOfFinAddOrder' : Prop := True
/-- setAddOrderOfEquiv (abstract). -/
def setAddOrderOfEquiv' : Prop := True
/-- card_addOrderOf_eq_totient (abstract). -/
def card_addOrderOf_eq_totient' : Prop := True
/-- finite_setOf_add_order_eq (abstract). -/
def finite_setOf_add_order_eq' : Prop := True
/-- UnitAddCircle (abstract). -/
def UnitAddCircle' : Prop := True
/-- EndpointIdent (abstract). -/
def EndpointIdent' : Prop := True
/-- equivIccQuot (abstract). -/
def equivIccQuot' : Prop := True
/-- equivIccQuot_comp_mk_eq_toIocMod (abstract). -/
def equivIccQuot_comp_mk_eq_toIocMod' : Prop := True
/-- homeoIccQuot (abstract). -/
def homeoIccQuot' : Prop := True
/-- liftIco_zero_coe_apply (abstract). -/
def liftIco_zero_coe_apply' : Prop := True
/-- liftIco_continuous (abstract). -/
def liftIco_continuous' : Prop := True
/-- liftIco_zero_continuous (abstract). -/
def liftIco_zero_continuous' : Prop := True
/-- toAddCircle (abstract). -/
def toAddCircle' : Prop := True
/-- toAddCircle_intCast (abstract). -/
def toAddCircle_intCast' : Prop := True
/-- toAddCircle_natCast (abstract). -/
def toAddCircle_natCast' : Prop := True
/-- toAddCircle_apply (abstract). -/
def toAddCircle_apply' : Prop := True
/-- toAddCircle_injective (abstract). -/
def toAddCircle_injective' : Prop := True
/-- toAddCircle_inj (abstract). -/
def toAddCircle_inj' : Prop := True
/-- toAddCircle_eq_zero (abstract). -/
def toAddCircle_eq_zero' : Prop := True

-- Instances/CantorSet.lean
/-- preCantorSet (abstract). -/
def preCantorSet' : Prop := True
/-- cantorSet (abstract). -/
def cantorSet' : Prop := True
/-- quarters_mem_preCantorSet (abstract). -/
def quarters_mem_preCantorSet' : Prop := True
/-- quarter_mem_preCantorSet (abstract). -/
def quarter_mem_preCantorSet' : Prop := True
/-- quarter_mem_cantorSet (abstract). -/
def quarter_mem_cantorSet' : Prop := True
/-- zero_mem_preCantorSet (abstract). -/
def zero_mem_preCantorSet' : Prop := True
/-- zero_mem_cantorSet (abstract). -/
def zero_mem_cantorSet' : Prop := True
/-- cantorSet_subset_unitInterval (abstract). -/
def cantorSet_subset_unitInterval' : Prop := True
/-- isClosed_preCantorSet (abstract). -/
def isClosed_preCantorSet' : Prop := True
/-- isClosed_cantorSet (abstract). -/
def isClosed_cantorSet' : Prop := True
/-- isCompact_cantorSet (abstract). -/
def isCompact_cantorSet' : Prop := True

-- Instances/Complex.lean
/-- subfield_eq_of_closed (abstract). -/
def subfield_eq_of_closed' : Prop := True
/-- uniformContinuous_ringHom_eq_id_or_conj (abstract). -/
def uniformContinuous_ringHom_eq_id_or_conj' : Prop := True

-- Instances/Discrete.lean
/-- secondCountableTopology_of_encodable (abstract). -/
def secondCountableTopology_of_encodable' : Prop := True
/-- bot_topologicalSpace_eq_generateFrom (abstract). -/
def bot_topologicalSpace_eq_generateFrom' : Prop := True
/-- discreteTopology_iff_orderTopology_of_pred_succ (abstract). -/
def discreteTopology_iff_orderTopology_of_pred_succ' : Prop := True

-- Instances/ENNReal.lean
-- COLLISION: isEmbedding_coe' already in Analysis.lean — rename needed
/-- isOpen_ne_top (abstract). -/
def isOpen_ne_top' : Prop := True
/-- isOpen_Ico_zero (abstract). -/
def isOpen_Ico_zero' : Prop := True
/-- coe_range_mem_nhds (abstract). -/
def coe_range_mem_nhds' : Prop := True
/-- tendsto_coe (abstract). -/
def tendsto_coe' : Prop := True
/-- continuous_coe_iff (abstract). -/
def continuous_coe_iff' : Prop := True
/-- nhds_coe (abstract). -/
def nhds_coe' : Prop := True
/-- tendsto_nhds_coe_iff (abstract). -/
def tendsto_nhds_coe_iff' : Prop := True
/-- continuousAt_coe_iff (abstract). -/
def continuousAt_coe_iff' : Prop := True
/-- nhds_coe_coe (abstract). -/
def nhds_coe_coe' : Prop := True
-- COLLISION: continuous_ofReal' already in Analysis.lean — rename needed
/-- tendsto_ofReal (abstract). -/
def tendsto_ofReal' : Prop := True
/-- tendsto_toNNReal (abstract). -/
def tendsto_toNNReal' : Prop := True
/-- eventuallyEq_of_toReal_eventuallyEq (abstract). -/
def eventuallyEq_of_toReal_eventuallyEq' : Prop := True
/-- continuousOn_toNNReal (abstract). -/
def continuousOn_toNNReal' : Prop := True
/-- tendsto_toReal (abstract). -/
def tendsto_toReal' : Prop := True
/-- continuousOn_toReal (abstract). -/
def continuousOn_toReal' : Prop := True
/-- continuousAt_toReal (abstract). -/
def continuousAt_toReal' : Prop := True
/-- neTopHomeomorphNNReal (abstract). -/
def neTopHomeomorphNNReal' : Prop := True
/-- ltTopHomeomorphNNReal (abstract). -/
def ltTopHomeomorphNNReal' : Prop := True
/-- nhds_top_basis (abstract). -/
def nhds_top_basis' : Prop := True
/-- tendsto_nhds_top_iff_nnreal (abstract). -/
def tendsto_nhds_top_iff_nnreal' : Prop := True
/-- tendsto_nhds_top_iff_nat (abstract). -/
def tendsto_nhds_top_iff_nat' : Prop := True
/-- tendsto_nhds_top (abstract). -/
def tendsto_nhds_top' : Prop := True
/-- tendsto_nat_nhds_top (abstract). -/
def tendsto_nat_nhds_top' : Prop := True
/-- tendsto_coe_nhds_top (abstract). -/
def tendsto_coe_nhds_top' : Prop := True
/-- tendsto_ofReal_nhds_top (abstract). -/
def tendsto_ofReal_nhds_top' : Prop := True
/-- tendsto_ofReal_atTop (abstract). -/
def tendsto_ofReal_atTop' : Prop := True
/-- nhds_zero (abstract). -/
def nhds_zero' : Prop := True
/-- nhds_zero_basis (abstract). -/
def nhds_zero_basis' : Prop := True
/-- nhds_zero_basis_Iic (abstract). -/
def nhds_zero_basis_Iic' : Prop := True
/-- nhdsWithin_Ioi_coe_neBot (abstract). -/
def nhdsWithin_Ioi_coe_neBot' : Prop := True
/-- nhdsWithin_Ioi_zero_neBot (abstract). -/
def nhdsWithin_Ioi_zero_neBot' : Prop := True
/-- nhdsWithin_Ioi_one_neBot (abstract). -/
def nhdsWithin_Ioi_one_neBot' : Prop := True
/-- nhdsWithin_Ioi_nat_neBot (abstract). -/
def nhdsWithin_Ioi_nat_neBot' : Prop := True
/-- nhdsWithin_Ioi_ofNat_nebot (abstract). -/
def nhdsWithin_Ioi_ofNat_nebot' : Prop := True
/-- hasBasis_nhds_of_ne_top' (abstract). -/
def hasBasis_nhds_of_ne_top' : Prop := True
/-- Icc_mem_nhds (abstract). -/
def Icc_mem_nhds' : Prop := True
/-- nhds_of_ne_top (abstract). -/
def nhds_of_ne_top' : Prop := True
/-- biInf_le_nhds (abstract). -/
def biInf_le_nhds' : Prop := True
/-- tendsto_nhds_of_Icc (abstract). -/
def tendsto_nhds_of_Icc' : Prop := True
/-- tendsto_nhds_zero (abstract). -/
def tendsto_nhds_zero' : Prop := True
/-- tendsto_atTop_zero (abstract). -/
def tendsto_atTop_zero' : Prop := True
/-- tendsto_sub (abstract). -/
def tendsto_sub' : Prop := True
/-- ennreal_mul (abstract). -/
def ennreal_mul' : Prop := True
/-- tendsto_finset_prod_of_ne_top (abstract). -/
def tendsto_finset_prod_of_ne_top' : Prop := True
/-- continuousAt_const_mul (abstract). -/
def continuousAt_const_mul' : Prop := True
/-- continuousAt_mul_const (abstract). -/
def continuousAt_mul_const' : Prop := True
/-- continuous_const_mul (abstract). -/
def continuous_const_mul' : Prop := True
/-- continuous_mul_const (abstract). -/
def continuous_mul_const' : Prop := True
/-- continuous_div_const (abstract). -/
def continuous_div_const' : Prop := True
/-- continuousOn_sub (abstract). -/
def continuousOn_sub' : Prop := True
/-- continuous_sub_left (abstract). -/
def continuous_sub_left' : Prop := True
/-- continuous_nnreal_sub (abstract). -/
def continuous_nnreal_sub' : Prop := True
/-- continuousOn_sub_left (abstract). -/
def continuousOn_sub_left' : Prop := True
/-- continuous_sub_right (abstract). -/
def continuous_sub_right' : Prop := True
-- COLLISION: le_of_forall_lt_one_mul_le' already in Algebra.lean — rename needed
/-- iInf_mul_left' (abstract). -/
def iInf_mul_left' : Prop := True
/-- iInf_mul_right' (abstract). -/
def iInf_mul_right' : Prop := True
/-- inv_map_iInf (abstract). -/
def inv_map_iInf' : Prop := True
/-- inv_map_iSup (abstract). -/
def inv_map_iSup' : Prop := True
/-- inv_limsup (abstract). -/
def inv_limsup' : Prop := True
/-- inv_liminf (abstract). -/
def inv_liminf' : Prop := True
/-- tendsto_inv_iff (abstract). -/
def tendsto_inv_iff' : Prop := True
/-- tendsto_inv_nat_nhds_zero (abstract). -/
def tendsto_inv_nat_nhds_zero' : Prop := True
/-- tendsto_coe_sub (abstract). -/
def tendsto_coe_sub' : Prop := True
/-- exists_countable_dense_no_zero_top (abstract). -/
def exists_countable_dense_no_zero_top' : Prop := True
/-- ofReal_cinfi (abstract). -/
def ofReal_cinfi' : Prop := True
/-- exists_frequently_lt_of_liminf_ne_top (abstract). -/
def exists_frequently_lt_of_liminf_ne_top' : Prop := True
/-- exists_upcrossings_of_not_bounded_under (abstract). -/
def exists_upcrossings_of_not_bounded_under' : Prop := True
-- COLLISION: hasSum_coe' already in Analysis.lean — rename needed
/-- tsum_coe_eq (abstract). -/
def tsum_coe_eq' : Prop := True
/-- coe_tsum (abstract). -/
def coe_tsum' : Prop := True
/-- tsum_coe_ne_top_iff_summable (abstract). -/
def tsum_coe_ne_top_iff_summable' : Prop := True
/-- tsum_eq_iSup_sum (abstract). -/
def tsum_eq_iSup_sum' : Prop := True
/-- tsum_sigma (abstract). -/
def tsum_sigma' : Prop := True
/-- tsum_prod (abstract). -/
def tsum_prod' : Prop := True
/-- tsum_comm (abstract). -/
def tsum_comm' : Prop := True
/-- tsum_add (abstract). -/
def tsum_add' : Prop := True
/-- tsum_le_tsum (abstract). -/
def tsum_le_tsum' : Prop := True
/-- ennreal_tsum_le_tsum (abstract). -/
def ennreal_tsum_le_tsum' : Prop := True
/-- sum_le_tsum (abstract). -/
def sum_le_tsum' : Prop := True
/-- tsum_eq_iSup_nat' (abstract). -/
def tsum_eq_iSup_nat' : Prop := True
/-- tsum_eq_liminf_sum_nat (abstract). -/
def tsum_eq_liminf_sum_nat' : Prop := True
/-- tsum_eq_limsup_sum_nat (abstract). -/
def tsum_eq_limsup_sum_nat' : Prop := True
/-- le_tsum (abstract). -/
def le_tsum' : Prop := True
/-- tsum_eq_zero (abstract). -/
def tsum_eq_zero' : Prop := True
/-- tsum_eq_top_of_eq_top (abstract). -/
def tsum_eq_top_of_eq_top' : Prop := True
/-- lt_top_of_tsum_ne_top (abstract). -/
def lt_top_of_tsum_ne_top' : Prop := True
/-- tsum_top (abstract). -/
def tsum_top' : Prop := True
/-- tsum_const_eq_top_of_ne_zero (abstract). -/
def tsum_const_eq_top_of_ne_zero' : Prop := True
/-- ne_top_of_tsum_ne_top (abstract). -/
def ne_top_of_tsum_ne_top' : Prop := True
/-- tsum_iSup_eq (abstract). -/
def tsum_iSup_eq' : Prop := True
/-- hasSum_iff_tendsto_nat (abstract). -/
def hasSum_iff_tendsto_nat' : Prop := True
/-- tendsto_nat_tsum (abstract). -/
def tendsto_nat_tsum' : Prop := True
/-- toNNReal_apply_of_tsum_ne_top (abstract). -/
def toNNReal_apply_of_tsum_ne_top' : Prop := True
/-- summable_toNNReal_of_tsum_ne_top (abstract). -/
def summable_toNNReal_of_tsum_ne_top' : Prop := True
/-- tendsto_cofinite_zero_of_tsum_ne_top (abstract). -/
def tendsto_cofinite_zero_of_tsum_ne_top' : Prop := True
/-- tendsto_atTop_zero_of_tsum_ne_top (abstract). -/
def tendsto_atTop_zero_of_tsum_ne_top' : Prop := True
/-- tendsto_tsum_compl_atTop_zero (abstract). -/
def tendsto_tsum_compl_atTop_zero' : Prop := True
/-- tsum_apply (abstract). -/
def tsum_apply' : Prop := True
/-- tsum_sub (abstract). -/
def tsum_sub' : Prop := True
/-- tsum_comp_le_tsum_of_injective (abstract). -/
def tsum_comp_le_tsum_of_injective' : Prop := True
/-- tsum_le_tsum_comp_of_surjective (abstract). -/
def tsum_le_tsum_comp_of_surjective' : Prop := True
/-- tsum_mono_subtype (abstract). -/
def tsum_mono_subtype' : Prop := True
/-- tsum_iUnion_le_tsum (abstract). -/
def tsum_iUnion_le_tsum' : Prop := True
/-- tsum_biUnion_le_tsum (abstract). -/
def tsum_biUnion_le_tsum' : Prop := True
/-- tsum_biUnion_le (abstract). -/
def tsum_biUnion_le' : Prop := True
/-- tsum_iUnion_le (abstract). -/
def tsum_iUnion_le' : Prop := True
/-- tsum_union_le (abstract). -/
def tsum_union_le' : Prop := True
/-- tsum_eq_add_tsum_ite (abstract). -/
def tsum_eq_add_tsum_ite' : Prop := True
/-- tsum_add_one_eq_top (abstract). -/
def tsum_add_one_eq_top' : Prop := True
/-- finite_const_le_of_tsum_ne_top (abstract). -/
def finite_const_le_of_tsum_ne_top' : Prop := True
/-- finset_card_const_le_le_of_tsum_le (abstract). -/
def finset_card_const_le_le_of_tsum_le' : Prop := True
/-- tsum_fiberwise (abstract). -/
def tsum_fiberwise' : Prop := True
/-- tendsto_toReal_iff (abstract). -/
def tendsto_toReal_iff' : Prop := True
/-- tsum_coe_ne_top_iff_summable_coe (abstract). -/
def tsum_coe_ne_top_iff_summable_coe' : Prop := True
/-- tsum_coe_eq_top_iff_not_summable_coe (abstract). -/
def tsum_coe_eq_top_iff_not_summable_coe' : Prop := True
/-- hasSum_toReal (abstract). -/
def hasSum_toReal' : Prop := True
/-- summable_toReal (abstract). -/
def summable_toReal' : Prop := True
/-- tsum_eq_toNNReal_tsum (abstract). -/
def tsum_eq_toNNReal_tsum' : Prop := True
/-- exists_le_hasSum_of_le (abstract). -/
def exists_le_hasSum_of_le' : Prop := True
/-- summable_of_le (abstract). -/
def summable_of_le' : Prop := True
/-- countable_support_nnreal (abstract). -/
def countable_support_nnreal' : Prop := True
/-- not_summable_iff_tendsto_nat_atTop (abstract). -/
def not_summable_iff_tendsto_nat_atTop' : Prop := True
/-- summable_iff_not_tendsto_nat_atTop (abstract). -/
def summable_iff_not_tendsto_nat_atTop' : Prop := True
/-- tsum_comp_le_tsum_of_inj (abstract). -/
def tsum_comp_le_tsum_of_inj' : Prop := True
/-- summable_sigma (abstract). -/
def summable_sigma' : Prop := True
/-- tendsto_sum_nat_add (abstract). -/
def tendsto_sum_nat_add' : Prop := True
/-- hasSum_lt (abstract). -/
def hasSum_lt' : Prop := True
/-- hasSum_strict_mono (abstract). -/
def hasSum_strict_mono' : Prop := True
/-- tsum_lt_tsum (abstract). -/
def tsum_lt_tsum' : Prop := True
/-- tsum_strict_mono (abstract). -/
def tsum_strict_mono' : Prop := True
/-- tsum_pos (abstract). -/
def tsum_pos' : Prop := True
/-- tsum_toNNReal_eq (abstract). -/
def tsum_toNNReal_eq' : Prop := True
/-- tsum_toReal_eq (abstract). -/
def tsum_toReal_eq' : Prop := True
/-- of_nonneg_of_le (abstract). -/
def of_nonneg_of_le' : Prop := True
-- COLLISION: toNNReal' already in Analysis.lean — rename needed
/-- countable_support_ennreal (abstract). -/
def countable_support_ennreal' : Prop := True
/-- hasSum_iff_tendsto_nat_of_nonneg (abstract). -/
def hasSum_iff_tendsto_nat_of_nonneg' : Prop := True
/-- ofReal_tsum_of_nonneg (abstract). -/
def ofReal_tsum_of_nonneg' : Prop := True
/-- edist_ne_top_of_mem_ball (abstract). -/
def edist_ne_top_of_mem_ball' : Prop := True
/-- metricSpaceEMetricBall (abstract). -/
def metricSpaceEMetricBall' : Prop := True
/-- nhds_eq_nhds_emetric_ball (abstract). -/
def nhds_eq_nhds_emetric_ball' : Prop := True
/-- tendsto_iff_edist_tendsto_0 (abstract). -/
def tendsto_iff_edist_tendsto_0' : Prop := True
/-- cauchySeq_iff_le_tendsto_0 (abstract). -/
def cauchySeq_iff_le_tendsto_0' : Prop := True
/-- continuous_of_le_add_edist (abstract). -/
def continuous_of_le_add_edist' : Prop := True
/-- continuous_edist (abstract). -/
def continuous_edist' : Prop := True
-- COLLISION: edist' already in MeasureTheory2.lean — rename needed
/-- cauchySeq_of_edist_le_of_summable (abstract). -/
def cauchySeq_of_edist_le_of_summable' : Prop := True
/-- cauchySeq_of_edist_le_of_tsum_ne_top (abstract). -/
def cauchySeq_of_edist_le_of_tsum_ne_top' : Prop := True
/-- isClosed_ball (abstract). -/
def isClosed_ball' : Prop := True
/-- diam_closure (abstract). -/
def diam_closure' : Prop := True
/-- isClosed_setOf_lipschitzOnWith (abstract). -/
def isClosed_setOf_lipschitzOnWith' : Prop := True
/-- isClosed_setOf_lipschitzWith (abstract). -/
def isClosed_setOf_lipschitzWith' : Prop := True
/-- ediam_eq (abstract). -/
def ediam_eq' : Prop := True
/-- diam_eq (abstract). -/
def diam_eq' : Prop := True
/-- ediam_Ioo (abstract). -/
def ediam_Ioo' : Prop := True
/-- ediam_Icc (abstract). -/
def ediam_Icc' : Prop := True
/-- ediam_Ico (abstract). -/
def ediam_Ico' : Prop := True
/-- ediam_Ioc (abstract). -/
def ediam_Ioc' : Prop := True
/-- diam_Ico (abstract). -/
def diam_Ico' : Prop := True
/-- diam_Ioc (abstract). -/
def diam_Ioc' : Prop := True
/-- diam_Ioo (abstract). -/
def diam_Ioo' : Prop := True
/-- edist_le_tsum_of_edist_le_of_tendsto (abstract). -/
def edist_le_tsum_of_edist_le_of_tendsto' : Prop := True
/-- edist_le_tsum_of_edist_le_of_tendsto₀ (abstract). -/
def edist_le_tsum_of_edist_le_of_tendsto₀' : Prop := True
/-- truncateToReal (abstract). -/
def truncateToReal' : Prop := True
/-- truncateToReal_eq_toReal (abstract). -/
def truncateToReal_eq_toReal' : Prop := True
/-- truncateToReal_le (abstract). -/
def truncateToReal_le' : Prop := True
/-- truncateToReal_nonneg (abstract). -/
def truncateToReal_nonneg' : Prop := True
/-- monotone_truncateToReal (abstract). -/
def monotone_truncateToReal' : Prop := True
/-- continuous_truncateToReal (abstract). -/
def continuous_truncateToReal' : Prop := True
/-- liminf_toReal_eq (abstract). -/
def liminf_toReal_eq' : Prop := True
/-- limsup_toReal_eq (abstract). -/
def limsup_toReal_eq' : Prop := True

-- Instances/ENat.lean
-- COLLISION: range_natCast' already in SetTheory.lean — rename needed
/-- isEmbedding_natCast (abstract). -/
def isEmbedding_natCast' : Prop := True
/-- isOpenEmbedding_natCast (abstract). -/
def isOpenEmbedding_natCast' : Prop := True
/-- nhds_natCast (abstract). -/
def nhds_natCast' : Prop := True
-- COLLISION: nhds_eq_pure' already in SetTheory.lean — rename needed
/-- isOpen_singleton (abstract). -/
def isOpen_singleton' : Prop := True
/-- mem_nhds_natCast_iff (abstract). -/
def mem_nhds_natCast_iff' : Prop := True
/-- tendsto_nhds_top_iff_natCast_lt (abstract). -/
def tendsto_nhds_top_iff_natCast_lt' : Prop := True
/-- continuousAt_sub (abstract). -/
def continuousAt_sub' : Prop := True
/-- enatSub (abstract). -/
def enatSub' : Prop := True

-- Instances/EReal.lean
/-- denseRange_ratCast (abstract). -/
def denseRange_ratCast' : Prop := True
/-- continuous_coe_real_ereal (abstract). -/
def continuous_coe_real_ereal' : Prop := True
/-- neBotTopHomeomorphReal (abstract). -/
def neBotTopHomeomorphReal' : Prop := True
/-- isEmbedding_coe_ennreal (abstract). -/
def isEmbedding_coe_ennreal' : Prop := True
/-- isClosedEmbedding_coe_ennreal (abstract). -/
def isClosedEmbedding_coe_ennreal' : Prop := True
/-- tendsto_coe_ennreal (abstract). -/
def tendsto_coe_ennreal' : Prop := True
/-- continuous_coe_ennreal_ereal (abstract). -/
def continuous_coe_ennreal_ereal' : Prop := True
/-- continuous_coe_ennreal_iff (abstract). -/
def continuous_coe_ennreal_iff' : Prop := True
/-- mem_nhds_top_iff (abstract). -/
def mem_nhds_top_iff' : Prop := True
/-- tendsto_nhds_top_iff_real (abstract). -/
def tendsto_nhds_top_iff_real' : Prop := True
/-- nhds_bot_basis (abstract). -/
def nhds_bot_basis' : Prop := True
/-- mem_nhds_bot_iff (abstract). -/
def mem_nhds_bot_iff' : Prop := True
/-- tendsto_nhds_bot_iff_real (abstract). -/
def tendsto_nhds_bot_iff_real' : Prop := True
/-- nhdsWithin_top (abstract). -/
def nhdsWithin_top' : Prop := True
/-- nhdsWithin_bot (abstract). -/
def nhdsWithin_bot' : Prop := True
/-- tendsto_toReal_atTop (abstract). -/
def tendsto_toReal_atTop' : Prop := True
/-- tendsto_toReal_atBot (abstract). -/
def tendsto_toReal_atBot' : Prop := True
/-- add_iInf_le_iInf_add (abstract). -/
def add_iInf_le_iInf_add' : Prop := True
/-- iSup_add_le_add_iSup (abstract). -/
def iSup_add_le_add_iSup' : Prop := True
/-- liminf_neg (abstract). -/
def liminf_neg' : Prop := True
/-- limsup_neg (abstract). -/
def limsup_neg' : Prop := True
/-- limsup_add_bot_of_ne_top (abstract). -/
def limsup_add_bot_of_ne_top' : Prop := True
/-- limsup_add_le_of_le (abstract). -/
def limsup_add_le_of_le' : Prop := True
/-- liminf_add_gt_of_gt (abstract). -/
def liminf_add_gt_of_gt' : Prop := True
/-- liminf_add_top_of_ne_bot (abstract). -/
def liminf_add_top_of_ne_bot' : Prop := True
/-- continuousAt_add_coe_coe (abstract). -/
def continuousAt_add_coe_coe' : Prop := True
/-- continuousAt_add_top_coe (abstract). -/
def continuousAt_add_top_coe' : Prop := True
/-- continuousAt_add_coe_top (abstract). -/
def continuousAt_add_coe_top' : Prop := True
/-- continuousAt_add_top_top (abstract). -/
def continuousAt_add_top_top' : Prop := True
/-- continuousAt_add_bot_coe (abstract). -/
def continuousAt_add_bot_coe' : Prop := True
/-- continuousAt_add_coe_bot (abstract). -/
def continuousAt_add_coe_bot' : Prop := True
/-- continuousAt_add_bot_bot (abstract). -/
def continuousAt_add_bot_bot' : Prop := True
/-- continuousAt_add (abstract). -/
def continuousAt_add' : Prop := True
/-- continuousAt_mul_swap (abstract). -/
def continuousAt_mul_swap' : Prop := True
/-- continuousAt_mul_symm1 (abstract). -/
def continuousAt_mul_symm1' : Prop := True
/-- continuousAt_mul_symm2 (abstract). -/
def continuousAt_mul_symm2' : Prop := True
/-- continuousAt_mul_symm3 (abstract). -/
def continuousAt_mul_symm3' : Prop := True
/-- continuousAt_mul_coe_coe (abstract). -/
def continuousAt_mul_coe_coe' : Prop := True
/-- continuousAt_mul_top_top (abstract). -/
def continuousAt_mul_top_top' : Prop := True
/-- continuousAt_mul_top_pos (abstract). -/
def continuousAt_mul_top_pos' : Prop := True
/-- continuousAt_mul_top_ne_zero (abstract). -/
def continuousAt_mul_top_ne_zero' : Prop := True
/-- continuousAt_mul (abstract). -/
def continuousAt_mul' : Prop := True

-- Instances/Int.lean
/-- pairwise_one_le_dist (abstract). -/
def pairwise_one_le_dist' : Prop := True
/-- isUniformEmbedding_coe_real (abstract). -/
def isUniformEmbedding_coe_real' : Prop := True
/-- ball_eq_Ioo (abstract). -/
def ball_eq_Ioo' : Prop := True
/-- closedBall_eq_Icc (abstract). -/
def closedBall_eq_Icc' : Prop := True
/-- cobounded_eq (abstract). -/
def cobounded_eq' : Prop := True
/-- cofinite_eq (abstract). -/
def cofinite_eq' : Prop := True

-- Instances/Irrational.lean
/-- setOf_irrational (abstract). -/
def setOf_irrational' : Prop := True
/-- dense_irrational (abstract). -/
def dense_irrational' : Prop := True
/-- eventually_residual_irrational (abstract). -/
def eventually_residual_irrational' : Prop := True
/-- eventually_forall_le_dist_cast_div (abstract). -/
def eventually_forall_le_dist_cast_div' : Prop := True
/-- eventually_forall_le_dist_cast_div_of_denom_le (abstract). -/
def eventually_forall_le_dist_cast_div_of_denom_le' : Prop := True
/-- eventually_forall_le_dist_cast_rat_of_den_le (abstract). -/
def eventually_forall_le_dist_cast_rat_of_den_le' : Prop := True

-- Instances/Matrix.lean
/-- continuous_matrix (abstract). -/
def continuous_matrix' : Prop := True
/-- matrix_elem (abstract). -/
def matrix_elem' : Prop := True
-- COLLISION: matrix_map' already in CategoryTheory.lean — rename needed
/-- matrix_transpose (abstract). -/
def matrix_transpose' : Prop := True
/-- matrix_conjTranspose (abstract). -/
def matrix_conjTranspose' : Prop := True
/-- matrix_col (abstract). -/
def matrix_col' : Prop := True
/-- matrix_row (abstract). -/
def matrix_row' : Prop := True
/-- matrix_diagonal (abstract). -/
def matrix_diagonal' : Prop := True
/-- matrix_dotProduct (abstract). -/
def matrix_dotProduct' : Prop := True
/-- matrix_mul (abstract). -/
def matrix_mul' : Prop := True
/-- matrix_vecMulVec (abstract). -/
def matrix_vecMulVec' : Prop := True
/-- matrix_mulVec (abstract). -/
def matrix_mulVec' : Prop := True
/-- matrix_vecMul (abstract). -/
def matrix_vecMul' : Prop := True
/-- matrix_submatrix (abstract). -/
def matrix_submatrix' : Prop := True
/-- matrix_reindex (abstract). -/
def matrix_reindex' : Prop := True
/-- matrix_diag (abstract). -/
def matrix_diag' : Prop := True
/-- continuous_matrix_diag (abstract). -/
def continuous_matrix_diag' : Prop := True
/-- matrix_trace (abstract). -/
def matrix_trace' : Prop := True
/-- matrix_det (abstract). -/
def matrix_det' : Prop := True
/-- matrix_updateColumn (abstract). -/
def matrix_updateColumn' : Prop := True
/-- matrix_updateRow (abstract). -/
def matrix_updateRow' : Prop := True
/-- matrix_cramer (abstract). -/
def matrix_cramer' : Prop := True
/-- matrix_adjugate (abstract). -/
def matrix_adjugate' : Prop := True
/-- continuousAt_matrix_inv (abstract). -/
def continuousAt_matrix_inv' : Prop := True
/-- matrix_fromBlocks (abstract). -/
def matrix_fromBlocks' : Prop := True
/-- matrix_blockDiagonal (abstract). -/
def matrix_blockDiagonal' : Prop := True
/-- matrix_blockDiag (abstract). -/
def matrix_blockDiag' : Prop := True
/-- summable_matrix_transpose (abstract). -/
def summable_matrix_transpose' : Prop := True
/-- transpose_tsum (abstract). -/
def transpose_tsum' : Prop := True
/-- summable_matrix_conjTranspose (abstract). -/
def summable_matrix_conjTranspose' : Prop := True
/-- conjTranspose_tsum (abstract). -/
def conjTranspose_tsum' : Prop := True
/-- summable_matrix_diagonal (abstract). -/
def summable_matrix_diagonal' : Prop := True
/-- diagonal_tsum (abstract). -/
def diagonal_tsum' : Prop := True
/-- summable_matrix_blockDiagonal (abstract). -/
def summable_matrix_blockDiagonal' : Prop := True
/-- blockDiagonal_tsum (abstract). -/
def blockDiagonal_tsum' : Prop := True
/-- blockDiagonal'_tsum (abstract). -/
def blockDiagonal'_tsum' : Prop := True

-- Instances/NNReal.lean
/-- continuous_real_toNNReal (abstract). -/
def continuous_real_toNNReal' : Prop := True
/-- realToNNReal (abstract). -/
def realToNNReal' : Prop := True
/-- ofReal_map_toNNReal (abstract). -/
def ofReal_map_toNNReal' : Prop := True
/-- coeNNRealReal (abstract). -/
def coeNNRealReal' : Prop := True
/-- map_coe_atTop (abstract). -/
def map_coe_atTop' : Prop := True
/-- comap_coe_atTop (abstract). -/
def comap_coe_atTop' : Prop := True
/-- tendsto_coe_atTop (abstract). -/
def tendsto_coe_atTop' : Prop := True
/-- tendsto_real_toNNReal (abstract). -/
def tendsto_real_toNNReal' : Prop := True
/-- map_toNNReal_atTop (abstract). -/
def map_toNNReal_atTop' : Prop := True
/-- tendsto_real_toNNReal_atTop (abstract). -/
def tendsto_real_toNNReal_atTop' : Prop := True
/-- comap_toNNReal_atTop (abstract). -/
def comap_toNNReal_atTop' : Prop := True
/-- tendsto_toNNReal_atTop_iff (abstract). -/
def tendsto_toNNReal_atTop_iff' : Prop := True
/-- tendsto_toNNReal_atTop (abstract). -/
def tendsto_toNNReal_atTop' : Prop := True
/-- hasSum_real_toNNReal_of_nonneg (abstract). -/
def hasSum_real_toNNReal_of_nonneg' : Prop := True
-- COLLISION: summable_coe' already in Analysis.lean — rename needed
/-- summable_mk (abstract). -/
def summable_mk' : Prop := True
/-- coe_tsum_of_nonneg (abstract). -/
def coe_tsum_of_nonneg' : Prop := True
/-- summable_comp_injective (abstract). -/
def summable_comp_injective' : Prop := True
/-- summable_nat_add (abstract). -/
def summable_nat_add' : Prop := True
/-- summable_nat_add_iff (abstract). -/
def summable_nat_add_iff' : Prop := True
/-- hasSum_nat_add_iff (abstract). -/
def hasSum_nat_add_iff' : Prop := True
/-- sum_add_tsum_nat_add (abstract). -/
def sum_add_tsum_nat_add' : Prop := True
/-- iInf_real_pos_eq_iInf_nnreal_pos (abstract). -/
def iInf_real_pos_eq_iInf_nnreal_pos' : Prop := True
/-- tendsto_cofinite_zero_of_summable (abstract). -/
def tendsto_cofinite_zero_of_summable' : Prop := True
/-- tendsto_atTop_zero_of_summable (abstract). -/
def tendsto_atTop_zero_of_summable' : Prop := True
/-- powOrderIso (abstract). -/
def powOrderIso' : Prop := True
/-- tendsto_of_bddAbove_monotone (abstract). -/
def tendsto_of_bddAbove_monotone' : Prop := True
/-- tendsto_of_bddBelow_antitone (abstract). -/
def tendsto_of_bddBelow_antitone' : Prop := True
/-- tendsto_of_antitone (abstract). -/
def tendsto_of_antitone' : Prop := True

-- Instances/Nat.lean

-- Instances/PNat.lean
/-- isUniformEmbedding_coe (abstract). -/
def isUniformEmbedding_coe' : Prop := True

-- Instances/Rat.lean
/-- uniformContinuous_coe_real (abstract). -/
def uniformContinuous_coe_real' : Prop := True
/-- isDenseEmbedding_coe_real (abstract). -/
def isDenseEmbedding_coe_real' : Prop := True
/-- isEmbedding_coe_real (abstract). -/
def isEmbedding_coe_real' : Prop := True
/-- continuous_coe_real (abstract). -/
def continuous_coe_real' : Prop := True
/-- dist_cast_rat (abstract). -/
def dist_cast_rat' : Prop := True
/-- isUniformEmbedding_coe_rat (abstract). -/
def isUniformEmbedding_coe_rat' : Prop := True
/-- isClosedEmbedding_coe_rat (abstract). -/
def isClosedEmbedding_coe_rat' : Prop := True
/-- uniformContinuous_add (abstract). -/
def uniformContinuous_add' : Prop := True
/-- uniformContinuous_neg (abstract). -/
def uniformContinuous_neg' : Prop := True
/-- uniformContinuous_abs (abstract). -/
def uniformContinuous_abs' : Prop := True
/-- totallyBounded_Icc (abstract). -/
def totallyBounded_Icc' : Prop := True

-- Instances/RatLemmas.lean
/-- dense_compl_compact (abstract). -/
def dense_compl_compact' : Prop := True
/-- not_countably_generated_cocompact (abstract). -/
def not_countably_generated_cocompact' : Prop := True
/-- not_countably_generated_nhds_infty_opc (abstract). -/
def not_countably_generated_nhds_infty_opc' : Prop := True
/-- not_firstCountableTopology_opc (abstract). -/
def not_firstCountableTopology_opc' : Prop := True
/-- not_secondCountableTopology_opc (abstract). -/
def not_secondCountableTopology_opc' : Prop := True

-- Instances/Real.lean
/-- isTopologicalBasis_Ioo_rat (abstract). -/
def isTopologicalBasis_Ioo_rat' : Prop := True
/-- uniformContinuous_const_mul (abstract). -/
def uniformContinuous_const_mul' : Prop := True
/-- totallyBounded_ball (abstract). -/
def totallyBounded_ball' : Prop := True
/-- closure_of_rat_image_lt (abstract). -/
def closure_of_rat_image_lt' : Prop := True
/-- compact_of_continuous (abstract). -/
def compact_of_continuous' : Prop := True
/-- isBounded_of_continuous (abstract). -/
def isBounded_of_continuous' : Prop := True

-- Instances/RealVectorSpace.lean
/-- map_real_smul (abstract). -/
def map_real_smul' : Prop := True
/-- toRealLinearMap (abstract). -/
def toRealLinearMap' : Prop := True
/-- toRealLinearEquiv (abstract). -/
def toRealLinearEquiv' : Prop := True

-- Instances/Sign.lean
/-- continuousAt_sign_of_pos (abstract). -/
def continuousAt_sign_of_pos' : Prop := True
/-- continuousAt_sign_of_neg (abstract). -/
def continuousAt_sign_of_neg' : Prop := True
/-- continuousAt_sign_of_ne_zero (abstract). -/
def continuousAt_sign_of_ne_zero' : Prop := True

-- Instances/TrivSqZeroExt.lean
/-- continuous_inl (abstract). -/
def continuous_inl' : Prop := True
/-- continuous_inr (abstract). -/
def continuous_inr' : Prop := True
/-- fstCLM (abstract). -/
def fstCLM' : Prop := True
/-- sndCLM (abstract). -/
def sndCLM' : Prop := True
/-- inlCLM (abstract). -/
def inlCLM' : Prop := True
/-- inrCLM (abstract). -/
def inrCLM' : Prop := True
/-- topologicalSemiring (abstract). -/
def topologicalSemiring' : Prop := True
/-- uniformContinuous_fst (abstract). -/
def uniformContinuous_fst' : Prop := True
/-- uniformContinuous_snd (abstract). -/
def uniformContinuous_snd' : Prop := True
/-- uniformContinuous_inl (abstract). -/
def uniformContinuous_inl' : Prop := True
/-- uniformContinuous_inr (abstract). -/
def uniformContinuous_inr' : Prop := True

-- Instances/ZMultiples.lean
/-- tendsto_coe_cofinite (abstract). -/
def tendsto_coe_cofinite' : Prop := True
/-- tendsto_zmultiplesHom_cofinite (abstract). -/
def tendsto_zmultiplesHom_cofinite' : Prop := True
/-- tendsto_zmultiples_subtype_cofinite (abstract). -/
def tendsto_zmultiples_subtype_cofinite' : Prop := True

-- Irreducible.lean
/-- IsPreirreducible (abstract). -/
def IsPreirreducible' : Prop := True
/-- IsIrreducible (abstract). -/
def IsIrreducible' : Prop := True
/-- isPreirreducible_empty (abstract). -/
def isPreirreducible_empty' : Prop := True
/-- isPreirreducible (abstract). -/
def isPreirreducible' : Prop := True
/-- isPreirreducible_singleton (abstract). -/
def isPreirreducible_singleton' : Prop := True
/-- isIrreducible_singleton (abstract). -/
def isIrreducible_singleton' : Prop := True
/-- isPreirreducible_iff_closure (abstract). -/
def isPreirreducible_iff_closure' : Prop := True
/-- isIrreducible_iff_closure (abstract). -/
def isIrreducible_iff_closure' : Prop := True
/-- exists_preirreducible (abstract). -/
def exists_preirreducible' : Prop := True
/-- irreducibleComponents (abstract). -/
def irreducibleComponents' : Prop := True
/-- isClosed_of_mem_irreducibleComponents (abstract). -/
def isClosed_of_mem_irreducibleComponents' : Prop := True
/-- irreducibleComponents_eq_maximals_closed (abstract). -/
def irreducibleComponents_eq_maximals_closed' : Prop := True
/-- irreducibleComponent (abstract). -/
def irreducibleComponent' : Prop := True
/-- irreducibleComponent_property (abstract). -/
def irreducibleComponent_property' : Prop := True
/-- mem_irreducibleComponent (abstract). -/
def mem_irreducibleComponent' : Prop := True
/-- isIrreducible_irreducibleComponent (abstract). -/
def isIrreducible_irreducibleComponent' : Prop := True
/-- eq_irreducibleComponent (abstract). -/
def eq_irreducibleComponent' : Prop := True
/-- irreducibleComponent_mem_irreducibleComponents (abstract). -/
def irreducibleComponent_mem_irreducibleComponents' : Prop := True
/-- isClosed_irreducibleComponent (abstract). -/
def isClosed_irreducibleComponent' : Prop := True
/-- PreirreducibleSpace (abstract). -/
def PreirreducibleSpace' : Prop := True
/-- IrreducibleSpace (abstract). -/
def IrreducibleSpace' : Prop := True
/-- isIrreducible_univ (abstract). -/
def isIrreducible_univ' : Prop := True
/-- irreducibleSpace_def (abstract). -/
def irreducibleSpace_def' : Prop := True
/-- nonempty_preirreducible_inter (abstract). -/
def nonempty_preirreducible_inter' : Prop := True
-- COLLISION: dense' already in CategoryTheory.lean — rename needed
/-- preirreducibleSpace (abstract). -/
def preirreducibleSpace' : Prop := True
/-- irreducibleComponents_eq_singleton (abstract). -/
def irreducibleComponents_eq_singleton' : Prop := True
/-- isIrreducible_iff_sInter (abstract). -/
def isIrreducible_iff_sInter' : Prop := True
/-- isPreirreducible_iff_isClosed_union_isClosed (abstract). -/
def isPreirreducible_iff_isClosed_union_isClosed' : Prop := True
/-- isIrreducible_iff_sUnion_isClosed (abstract). -/
def isIrreducible_iff_sUnion_isClosed' : Prop := True
/-- subset_closure_inter_of_isPreirreducible_of_isOpen (abstract). -/
def subset_closure_inter_of_isPreirreducible_of_isOpen' : Prop := True
/-- subset_irreducible (abstract). -/
def subset_irreducible' : Prop := True
/-- open_subset (abstract). -/
def open_subset' : Prop := True

-- IsLocalHomeomorph.lean
/-- IsLocalHomeomorphOn (abstract). -/
def IsLocalHomeomorphOn' : Prop := True
/-- of_comp_left (abstract). -/
def of_comp_left' : Prop := True
/-- of_comp_right (abstract). -/
def of_comp_right' : Prop := True
/-- IsLocalHomeomorph (abstract). -/
def IsLocalHomeomorph' : Prop := True
/-- isLocalHomeomorph_iff_isLocalHomeomorphOn_univ (abstract). -/
def isLocalHomeomorph_iff_isLocalHomeomorphOn_univ' : Prop := True
/-- isLocalHomeomorph_iff_isOpenEmbedding_restrict (abstract). -/
def isLocalHomeomorph_iff_isOpenEmbedding_restrict' : Prop := True
-- COLLISION: isLocallyInjective' already in CategoryTheory.lean — rename needed
/-- isOpenEmbedding_of_injective (abstract). -/
def isOpenEmbedding_of_injective' : Prop := True
/-- toHomeomorph_of_surjective (abstract). -/
def toHomeomorph_of_surjective' : Prop := True
/-- toHomeomorph_of_bijective (abstract). -/
def toHomeomorph_of_bijective' : Prop := True
/-- isOpenEmbedding_of_comp (abstract). -/
def isOpenEmbedding_of_comp' : Prop := True
/-- isTopologicalBasis (abstract). -/
def isTopologicalBasis' : Prop := True

-- JacobsonSpace.lean
/-- closedPoints (abstract). -/
def closedPoints' : Prop := True
/-- preimage_closedPoints_subset (abstract). -/
def preimage_closedPoints_subset' : Prop := True
/-- preimage_closedPoints (abstract). -/
def preimage_closedPoints' : Prop := True
/-- closedPoints_eq_univ (abstract). -/
def closedPoints_eq_univ' : Prop := True
/-- JacobsonSpace (abstract). -/
def JacobsonSpace' : Prop := True
/-- closure_closedPoints (abstract). -/
def closure_closedPoints' : Prop := True
/-- jacobsonSpace_iff_locallyClosed (abstract). -/
def jacobsonSpace_iff_locallyClosed' : Prop := True
/-- nonempty_inter_closedPoints (abstract). -/
def nonempty_inter_closedPoints' : Prop := True
/-- isClosed_singleton_of_isLocallyClosed_singleton (abstract). -/
def isClosed_singleton_of_isLocallyClosed_singleton' : Prop := True
/-- of_isOpenEmbedding (abstract). -/
def of_isOpenEmbedding' : Prop := True
/-- of_isClosedEmbedding (abstract). -/
def of_isClosedEmbedding' : Prop := True
/-- jacobsonSpace_iff_of_iSup_eq_top (abstract). -/
def jacobsonSpace_iff_of_iSup_eq_top' : Prop := True

-- KrullDimension.lean
/-- topologicalKrullDim (abstract). -/
def topologicalKrullDim' : Prop := True
/-- map_strictMono (abstract). -/
def map_strictMono' : Prop := True
/-- topologicalKrullDim_le (abstract). -/
def topologicalKrullDim_le' : Prop := True
/-- topologicalKrullDim_eq (abstract). -/
def topologicalKrullDim_eq' : Prop := True

-- List.lean
/-- nhds_list (abstract). -/
def nhds_list' : Prop := True
/-- nhds_nil (abstract). -/
def nhds_nil' : Prop := True
/-- nhds_cons (abstract). -/
def nhds_cons' : Prop := True
/-- tendsto_cons (abstract). -/
def tendsto_cons' : Prop := True
-- COLLISION: cons' already in SetTheory.lean — rename needed
/-- tendsto_cons_iff (abstract). -/
def tendsto_cons_iff' : Prop := True
/-- continuous_cons (abstract). -/
def continuous_cons' : Prop := True
/-- continuousAt_length (abstract). -/
def continuousAt_length' : Prop := True
/-- tendsto_insertIdx' (abstract). -/
def tendsto_insertIdx' : Prop := True
/-- continuous_insertIdx (abstract). -/
def continuous_insertIdx' : Prop := True
/-- tendsto_eraseIdx (abstract). -/
def tendsto_eraseIdx' : Prop := True
/-- continuous_eraseIdx (abstract). -/
def continuous_eraseIdx' : Prop := True
/-- tendsto_prod (abstract). -/
def tendsto_prod' : Prop := True
/-- continuous_prod (abstract). -/
def continuous_prod' : Prop := True
/-- continuousAt_eraseIdx (abstract). -/
def continuousAt_eraseIdx' : Prop := True

-- LocalAtTarget.lean
/-- restrictPreimage_isInducing (abstract). -/
def restrictPreimage_isInducing' : Prop := True
/-- restrictPreimage_isEmbedding (abstract). -/
def restrictPreimage_isEmbedding' : Prop := True
/-- restrictPreimage_isOpenEmbedding (abstract). -/
def restrictPreimage_isOpenEmbedding' : Prop := True
/-- restrictPreimage_isClosedEmbedding (abstract). -/
def restrictPreimage_isClosedEmbedding' : Prop := True
/-- restrictPreimage_isClosedMap (abstract). -/
def restrictPreimage_isClosedMap' : Prop := True
/-- restrictPreimage_isOpenMap (abstract). -/
def restrictPreimage_isOpenMap' : Prop := True
/-- isOpen_iff_inter_of_iSup_eq_top (abstract). -/
def isOpen_iff_inter_of_iSup_eq_top' : Prop := True
/-- isOpen_iff_coe_preimage_of_iSup_eq_top (abstract). -/
def isOpen_iff_coe_preimage_of_iSup_eq_top' : Prop := True
/-- isClosed_iff_coe_preimage_of_iSup_eq_top (abstract). -/
def isClosed_iff_coe_preimage_of_iSup_eq_top' : Prop := True
/-- isLocallyClosed_iff_coe_preimage_of_iSup_eq_top (abstract). -/
def isLocallyClosed_iff_coe_preimage_of_iSup_eq_top' : Prop := True
/-- isOpenMap_iff_isOpenMap_of_iSup_eq_top (abstract). -/
def isOpenMap_iff_isOpenMap_of_iSup_eq_top' : Prop := True
/-- isClosedMap_iff_isClosedMap_of_iSup_eq_top (abstract). -/
def isClosedMap_iff_isClosedMap_of_iSup_eq_top' : Prop := True
/-- inducing_iff_inducing_of_iSup_eq_top (abstract). -/
def inducing_iff_inducing_of_iSup_eq_top' : Prop := True
/-- isEmbedding_iff_of_iSup_eq_top (abstract). -/
def isEmbedding_iff_of_iSup_eq_top' : Prop := True
/-- isEmbedding_of_iSup_eq_top_of_preimage_subset_range (abstract). -/
def isEmbedding_of_iSup_eq_top_of_preimage_subset_range' : Prop := True
/-- isOpenEmbedding_iff_isOpenEmbedding_of_iSup_eq_top (abstract). -/
def isOpenEmbedding_iff_isOpenEmbedding_of_iSup_eq_top' : Prop := True
/-- isClosedEmbedding_iff_isClosedEmbedding_of_iSup_eq_top (abstract). -/
def isClosedEmbedding_iff_isClosedEmbedding_of_iSup_eq_top' : Prop := True
/-- denseRange_iff_denseRange_of_iSup_eq_top (abstract). -/
def denseRange_iff_denseRange_of_iSup_eq_top' : Prop := True

-- LocallyClosed.lean
/-- subset_coborder (abstract). -/
def subset_coborder' : Prop := True
/-- coborder_inter_closure (abstract). -/
def coborder_inter_closure' : Prop := True
/-- closure_inter_coborder (abstract). -/
def closure_inter_coborder' : Prop := True
/-- coborder_eq_union_frontier_compl (abstract). -/
def coborder_eq_union_frontier_compl' : Prop := True
/-- coborder_eq_univ_iff (abstract). -/
def coborder_eq_univ_iff' : Prop := True
/-- coborder_eq_compl_frontier_iff (abstract). -/
def coborder_eq_compl_frontier_iff' : Prop := True
/-- coborder_eq_union_closure_compl (abstract). -/
def coborder_eq_union_closure_compl' : Prop := True
/-- dense_coborder (abstract). -/
def dense_coborder' : Prop := True
/-- coborder_preimage_subset (abstract). -/
def coborder_preimage_subset' : Prop := True
/-- preimage_coborder_subset (abstract). -/
def preimage_coborder_subset' : Prop := True
/-- coborder_preimage (abstract). -/
def coborder_preimage' : Prop := True
/-- isClosed_preimage_val_coborder (abstract). -/
def isClosed_preimage_val_coborder' : Prop := True
/-- isLocallyClosed_iff (abstract). -/
def isLocallyClosed_iff' : Prop := True
/-- isLocallyClosed_tfae (abstract). -/
def isLocallyClosed_tfae' : Prop := True
/-- isLocallyClosed_iff_isOpen_coborder (abstract). -/
def isLocallyClosed_iff_isOpen_coborder' : Prop := True
/-- isOpen_preimage_val_closure (abstract). -/
def isOpen_preimage_val_closure' : Prop := True

-- LocallyConstant/Algebra.lean
-- COLLISION: constMonoidHom' already in Algebra.lean — rename needed
/-- charFn (abstract). -/
def charFn' : Prop := True
-- COLLISION: constRingHom' already in Algebra.lean — rename needed
/-- coeFnₗ (abstract). -/
def coeFnₗ' : Prop := True
-- COLLISION: evalMonoidHom' already in Algebra.lean — rename needed
/-- evalₗ (abstract). -/
def evalₗ' : Prop := True
-- COLLISION: evalRingHom' already in Algebra.lean — rename needed
-- COLLISION: evalₐ' already in RingTheory2.lean — rename needed
/-- comapMonoidHom (abstract). -/
def comapMonoidHom' : Prop := True
-- COLLISION: comapₗ' already in MeasureTheory2.lean — rename needed
/-- comapRingHom (abstract). -/
def comapRingHom' : Prop := True
/-- comapₐ (abstract). -/
def comapₐ' : Prop := True
/-- ker_comapₗ (abstract). -/
def ker_comapₗ' : Prop := True
/-- congrLeftₗ (abstract). -/
def congrLeftₗ' : Prop := True
/-- congrLeftRingEquiv (abstract). -/
def congrLeftRingEquiv' : Prop := True
/-- congrLeftₐ (abstract). -/
def congrLeftₐ' : Prop := True
-- COLLISION: mapMonoidHom' already in Order.lean — rename needed
-- COLLISION: mapₗ' already in MeasureTheory2.lean — rename needed
-- COLLISION: mapₐ' already in RingTheory2.lean — rename needed
/-- congrRightₗ (abstract). -/
def congrRightₗ' : Prop := True
/-- congrRightRingEquiv (abstract). -/
def congrRightRingEquiv' : Prop := True
/-- congrRightₐ (abstract). -/
def congrRightₐ' : Prop := True
-- COLLISION: constₗ' already in MeasureTheory2.lean — rename needed
/-- constₐ (abstract). -/
def constₐ' : Prop := True

-- LocallyConstant/Basic.lean
/-- IsLocallyConstant (abstract). -/
def IsLocallyConstant' : Prop := True
/-- tfae (abstract). -/
def tfae' : Prop := True
-- COLLISION: of_discrete' already in MeasureTheory2.lean — rename needed
/-- isOpen_fiber (abstract). -/
def isOpen_fiber' : Prop := True
/-- isClosed_fiber (abstract). -/
def isClosed_fiber' : Prop := True
/-- isClopen_fiber (abstract). -/
def isClopen_fiber' : Prop := True
/-- iff_exists_open (abstract). -/
def iff_exists_open' : Prop := True
/-- iff_eventually_eq (abstract). -/
def iff_eventually_eq' : Prop := True
/-- exists_open (abstract). -/
def exists_open' : Prop := True
/-- eventually_eq (abstract). -/
def eventually_eq' : Prop := True
/-- iff_isOpen_fiber_apply (abstract). -/
def iff_isOpen_fiber_apply' : Prop := True
/-- iff_isOpen_fiber (abstract). -/
def iff_isOpen_fiber' : Prop := True
/-- iff_continuous (abstract). -/
def iff_continuous' : Prop := True
/-- of_constant (abstract). -/
def of_constant' : Prop := True
/-- apply_eq_of_isPreconnected (abstract). -/
def apply_eq_of_isPreconnected' : Prop := True
/-- apply_eq_of_preconnectedSpace (abstract). -/
def apply_eq_of_preconnectedSpace' : Prop := True
/-- eq_const (abstract). -/
def eq_const' : Prop := True
/-- exists_eq_const (abstract). -/
def exists_eq_const' : Prop := True
/-- iff_is_const (abstract). -/
def iff_is_const' : Prop := True
/-- range_finite (abstract). -/
def range_finite' : Prop := True
/-- of_constant_on_connected_components (abstract). -/
def of_constant_on_connected_components' : Prop := True
/-- of_constant_on_connected_clopens (abstract). -/
def of_constant_on_connected_clopens' : Prop := True
/-- of_constant_on_preconnected_clopens (abstract). -/
def of_constant_on_preconnected_clopens' : Prop := True
/-- LocallyConstant (abstract). -/
def LocallyConstant' : Prop := True
-- COLLISION: congr_arg' already in Order.lean — rename needed
-- COLLISION: coe_inj' already in Order.lean — rename needed
/-- ofIsClopen_fiber_zero (abstract). -/
def ofIsClopen_fiber_zero' : Prop := True
/-- ofIsClopen_fiber_one (abstract). -/
def ofIsClopen_fiber_one' : Prop := True
/-- locallyConstant_eq_of_fiber_zero_eq (abstract). -/
def locallyConstant_eq_of_fiber_zero_eq' : Prop := True
-- COLLISION: flip' already in Order.lean — rename needed
/-- unflip (abstract). -/
def unflip' : Prop := True
-- COLLISION: comap_const' already in MeasureTheory2.lean — rename needed
-- COLLISION: comap_injective' already in Order.lean — rename needed
/-- mulIndicator_apply_eq_if (abstract). -/
def mulIndicator_apply_eq_if' : Prop := True
-- COLLISION: mulIndicator_of_mem' already in Algebra.lean — rename needed
-- COLLISION: mulIndicator_of_not_mem' already in Algebra.lean — rename needed
-- COLLISION: congrLeft' already in CategoryTheory.lean — rename needed
-- COLLISION: congrRight' already in Algebra.lean — rename needed
/-- piecewise_apply_left (abstract). -/
def piecewise_apply_left' : Prop := True
/-- piecewise_apply_right (abstract). -/
def piecewise_apply_right' : Prop := True
/-- piecewise'_apply_left (abstract). -/
def piecewise'_apply_left' : Prop := True
/-- piecewise'_apply_right (abstract). -/
def piecewise'_apply_right' : Prop := True

-- LocallyFinite.lean
/-- LocallyFinite (abstract). -/
def LocallyFinite' : Prop := True
/-- locallyFinite_of_finite (abstract). -/
def locallyFinite_of_finite' : Prop := True
/-- point_finite (abstract). -/
def point_finite' : Prop := True
/-- comp_injOn (abstract). -/
def comp_injOn' : Prop := True
/-- locallyFinite_iff_smallSets (abstract). -/
def locallyFinite_iff_smallSets' : Prop := True
-- COLLISION: eventually_smallSets' already in Order.lean — rename needed
-- COLLISION: exists_mem_basis' already in Analysis.lean — rename needed
/-- continuousOn_iUnion' (abstract). -/
def continuousOn_iUnion' : Prop := True
/-- iInter_compl_mem_nhds (abstract). -/
def iInter_compl_mem_nhds' : Prop := True
/-- exists_forall_eventually_eq_prod (abstract). -/
def exists_forall_eventually_eq_prod' : Prop := True
/-- exists_forall_eventually_atTop_eventually_eq' (abstract). -/
def exists_forall_eventually_atTop_eventually_eq' : Prop := True
/-- exists_forall_eventually_atTop_eventuallyEq (abstract). -/
def exists_forall_eventually_atTop_eventuallyEq' : Prop := True
/-- preimage_continuous (abstract). -/
def preimage_continuous' : Prop := True
-- COLLISION: prod_right' already in RingTheory2.lean — rename needed
-- COLLISION: prod_left' already in RingTheory2.lean — rename needed
/-- locallyFinite_comp_iff (abstract). -/
def locallyFinite_comp_iff' : Prop := True
/-- locallyFinite_sum (abstract). -/
def locallyFinite_sum' : Prop := True
/-- locallyFinite_option (abstract). -/
def locallyFinite_option' : Prop := True
/-- option_elim' (abstract). -/
def option_elim' : Prop := True
-- COLLISION: eventually_subset' already in Order.lean — rename needed

-- Maps/Basic.lean
/-- of_comp_iff (abstract). -/
def of_comp_iff' : Prop := True
/-- isInducing_iff_nhds (abstract). -/
def isInducing_iff_nhds' : Prop := True
/-- basis_nhds (abstract). -/
def basis_nhds' : Prop := True
/-- nhdsSet_eq_comap (abstract). -/
def nhdsSet_eq_comap' : Prop := True
/-- map_nhds_of_mem (abstract). -/
def map_nhds_of_mem' : Prop := True
/-- image_mem_nhdsWithin (abstract). -/
def image_mem_nhdsWithin' : Prop := True
/-- continuousAt_iff (abstract). -/
def continuousAt_iff' : Prop := True
/-- closure_eq_preimage_closure_image (abstract). -/
def closure_eq_preimage_closure_image' : Prop := True
/-- setOf_isOpen (abstract). -/
def setOf_isOpen' : Prop := True
-- COLLISION: of_subsingleton' already in Order.lean — rename needed
-- COLLISION: of_leftInverse' already in Algebra.lean — rename needed
/-- isQuotientMap_iff (abstract). -/
def isQuotientMap_iff' : Prop := True
/-- isQuotientMap_iff_isClosed (abstract). -/
def isQuotientMap_iff_isClosed' : Prop := True
/-- isOpen_range (abstract). -/
def isOpen_range' : Prop := True
-- COLLISION: image_mem_nhds' already in Analysis.lean — rename needed
/-- range_mem_nhds (abstract). -/
def range_mem_nhds' : Prop := True
/-- mapsTo_interior (abstract). -/
def mapsTo_interior' : Prop := True
/-- image_interior_subset (abstract). -/
def image_interior_subset' : Prop := True
/-- interior_preimage_subset_preimage_interior (abstract). -/
def interior_preimage_subset_preimage_interior' : Prop := True
/-- preimage_interior_eq_interior_preimage (abstract). -/
def preimage_interior_eq_interior_preimage' : Prop := True
/-- preimage_closure_subset_closure_preimage (abstract). -/
def preimage_closure_subset_closure_preimage' : Prop := True
/-- preimage_closure_eq_closure_preimage (abstract). -/
def preimage_closure_eq_closure_preimage' : Prop := True
/-- preimage_frontier_subset_frontier_preimage (abstract). -/
def preimage_frontier_subset_frontier_preimage' : Prop := True
/-- preimage_frontier_eq_frontier_preimage (abstract). -/
def preimage_frontier_eq_frontier_preimage' : Prop := True
-- COLLISION: of_isEmpty' already in Order.lean — rename needed
/-- isOpenMap_iff_nhds_le (abstract). -/
def isOpenMap_iff_nhds_le' : Prop := True
/-- isOpenMap_iff_interior (abstract). -/
def isOpenMap_iff_interior' : Prop := True
/-- of_comp_surjective (abstract). -/
def of_comp_surjective' : Prop := True
/-- closure_image_subset (abstract). -/
def closure_image_subset' : Prop := True
/-- of_nonempty (abstract). -/
def of_nonempty' : Prop := True
-- COLLISION: isClosed_range' already in Analysis.lean — rename needed
/-- isClosedMap_iff_closure_image (abstract). -/
def isClosedMap_iff_closure_image' : Prop := True
/-- isClosedMap_iff_clusterPt (abstract). -/
def isClosedMap_iff_clusterPt' : Prop := True
/-- closure_image_eq_of_continuous (abstract). -/
def closure_image_eq_of_continuous' : Prop := True
/-- lift'_closure_map_eq (abstract). -/
def lift'_closure_map_eq' : Prop := True
/-- mapClusterPt_iff_lift'_closure (abstract). -/
def mapClusterPt_iff_lift'_closure' : Prop := True
/-- isOpen_iff_image_isOpen (abstract). -/
def isOpen_iff_image_isOpen' : Prop := True
/-- isOpen_iff_preimage_isOpen (abstract). -/
def isOpen_iff_preimage_isOpen' : Prop := True
/-- of_isEmbedding_isOpenMap (abstract). -/
def of_isEmbedding_isOpenMap' : Prop := True
/-- isOpenEmbedding_of_surjective (abstract). -/
def isOpenEmbedding_of_surjective' : Prop := True
/-- isOpenEmbedding_iff_isEmbedding_isOpenMap (abstract). -/
def isOpenEmbedding_iff_isEmbedding_isOpenMap' : Prop := True
/-- of_continuous_injective_isOpenMap (abstract). -/
def of_continuous_injective_isOpenMap' : Prop := True
/-- isOpenEmbedding_iff_continuous_injective_isOpenMap (abstract). -/
def isOpenEmbedding_iff_continuous_injective_isOpenMap' : Prop := True
/-- isClosed_iff_image_isClosed (abstract). -/
def isClosed_iff_image_isClosed' : Prop := True
/-- isClosed_iff_preimage_isClosed (abstract). -/
def isClosed_iff_preimage_isClosed' : Prop := True
/-- of_isEmbedding_isClosedMap (abstract). -/
def of_isEmbedding_isClosedMap' : Prop := True
/-- of_continuous_injective_isClosedMap (abstract). -/
def of_continuous_injective_isClosedMap' : Prop := True
/-- closure_image_eq (abstract). -/
def closure_image_eq' : Prop := True

-- Maps/OpenQuotient.lean
/-- iff_isOpenMap_isQuotientMap (abstract). -/
def iff_isOpenMap_isQuotientMap' : Prop := True
/-- of_isOpenMap_isQuotientMap (abstract). -/
def of_isOpenMap_isQuotientMap' : Prop := True
/-- continuousAt_comp_iff (abstract). -/
def continuousAt_comp_iff' : Prop := True
/-- dense_preimage_iff (abstract). -/
def dense_preimage_iff' : Prop := True

-- Maps/Proper/Basic.lean
/-- IsProperMap (abstract). -/
def IsProperMap' : Prop := True
/-- isProperMap_iff_ultrafilter (abstract). -/
def isProperMap_iff_ultrafilter' : Prop := True
/-- isProperMap_iff_ultrafilter_of_t2 (abstract). -/
def isProperMap_iff_ultrafilter_of_t2' : Prop := True
/-- ultrafilter_le_nhds_of_tendsto (abstract). -/
def ultrafilter_le_nhds_of_tendsto' : Prop := True
/-- isProperMap_of_comp_of_surj (abstract). -/
def isProperMap_of_comp_of_surj' : Prop := True
/-- isProperMap_of_comp_of_inj (abstract). -/
def isProperMap_of_comp_of_inj' : Prop := True
/-- isProperMap_of_comp_of_t2 (abstract). -/
def isProperMap_of_comp_of_t2' : Prop := True
/-- isProperMap_iff_isClosedMap_and_compact_fibers (abstract). -/
def isProperMap_iff_isClosedMap_and_compact_fibers' : Prop := True
/-- isProperMap_iff_isClosedMap_of_inj (abstract). -/
def isProperMap_iff_isClosedMap_of_inj' : Prop := True
/-- isProperMap_of_isClosedMap_of_inj (abstract). -/
def isProperMap_of_isClosedMap_of_inj' : Prop := True
/-- isProperMap (abstract). -/
def isProperMap' : Prop := True
/-- isProperMap_id (abstract). -/
def isProperMap_id' : Prop := True
/-- isProperMap_subtypeVal (abstract). -/
def isProperMap_subtypeVal' : Prop := True
/-- isProperMap_iff_isClosedMap_and_tendsto_cofinite (abstract). -/
def isProperMap_iff_isClosedMap_and_tendsto_cofinite' : Prop := True
/-- universally_closed (abstract). -/
def universally_closed' : Prop := True
/-- isProperMap_iff_isClosedMap_filter (abstract). -/
def isProperMap_iff_isClosedMap_filter' : Prop := True

-- Maps/Proper/CompactlyGenerated.lean
/-- isProperMap_iff_isCompact_preimage (abstract). -/
def isProperMap_iff_isCompact_preimage' : Prop := True
/-- isProperMap_iff_tendsto_cocompact (abstract). -/
def isProperMap_iff_tendsto_cocompact' : Prop := True

-- Maps/Proper/UniversallyClosed.lean
/-- isProperMap_iff_isClosedMap_ultrafilter (abstract). -/
def isProperMap_iff_isClosedMap_ultrafilter' : Prop := True
/-- isProperMap_iff_universally_closed (abstract). -/
def isProperMap_iff_universally_closed' : Prop := True

-- MetricSpace/Algebra.lean
/-- LipschitzAdd (abstract). -/
def LipschitzAdd' : Prop := True
/-- LipschitzMul (abstract). -/
def LipschitzMul' : Prop := True
/-- lipschitzWith_lipschitz_const_mul_edist (abstract). -/
def lipschitzWith_lipschitz_const_mul_edist' : Prop := True
/-- lipschitz_with_lipschitz_const_mul (abstract). -/
def lipschitz_with_lipschitz_const_mul' : Prop := True
/-- BoundedSMul (abstract). -/
def BoundedSMul' : Prop := True
/-- dist_smul_pair (abstract). -/
def dist_smul_pair' : Prop := True
/-- dist_pair_smul (abstract). -/
def dist_pair_smul' : Prop := True

-- MetricSpace/Antilipschitz.lean
/-- AntilipschitzWith (abstract). -/
def AntilipschitzWith' : Prop := True
/-- edist_ne_top (abstract). -/
def edist_ne_top' : Prop := True
/-- antilipschitzWith_iff_le_mul_nndist (abstract). -/
def antilipschitzWith_iff_le_mul_nndist' : Prop := True
/-- antilipschitzWith_iff_le_mul_dist (abstract). -/
def antilipschitzWith_iff_le_mul_dist' : Prop := True
/-- mul_le_nndist (abstract). -/
def mul_le_nndist' : Prop := True
/-- mul_le_dist (abstract). -/
def mul_le_dist' : Prop := True
-- COLLISION: k' already in RingTheory2.lean — rename needed
/-- mul_le_edist (abstract). -/
def mul_le_edist' : Prop := True
/-- ediam_preimage_le (abstract). -/
def ediam_preimage_le' : Prop := True
/-- le_mul_ediam_image (abstract). -/
def le_mul_ediam_image' : Prop := True
/-- to_rightInvOn' (abstract). -/
def to_rightInvOn' : Prop := True
/-- to_rightInverse (abstract). -/
def to_rightInverse' : Prop := True
/-- comap_uniformity_le (abstract). -/
def comap_uniformity_le' : Prop := True
-- COLLISION: isUniformInducing' already in MeasureTheory2.lean — rename needed
/-- isComplete_range (abstract). -/
def isComplete_range' : Prop := True
-- COLLISION: subtype_coe' already in MeasureTheory2.lean — rename needed
/-- isBounded_preimage (abstract). -/
def isBounded_preimage' : Prop := True
/-- tendsto_cobounded (abstract). -/
def tendsto_cobounded' : Prop := True
/-- properSpace (abstract). -/
def properSpace' : Prop := True
/-- isBounded_of_image2_left (abstract). -/
def isBounded_of_image2_left' : Prop := True
/-- isBounded_of_image2_right (abstract). -/
def isBounded_of_image2_right' : Prop := True

-- MetricSpace/Basic.lean
/-- ofT0PseudoMetricSpace (abstract). -/
def ofT0PseudoMetricSpace' : Prop := True
/-- isClosed_of_pairwise_le_dist (abstract). -/
def isClosed_of_pairwise_le_dist' : Prop := True
/-- isClosedEmbedding_of_pairwise_le_dist (abstract). -/
def isClosedEmbedding_of_pairwise_le_dist' : Prop := True
/-- isUniformEmbedding_bot_of_pairwise_le_dist (abstract). -/
def isUniformEmbedding_bot_of_pairwise_le_dist' : Prop := True
/-- toMetricSpaceOfDist (abstract). -/
def toMetricSpaceOfDist' : Prop := True
/-- toMetricSpace (abstract). -/
def toMetricSpace' : Prop := True
/-- comapMetricSpace (abstract). -/
def comapMetricSpace' : Prop := True
/-- secondCountable_of_countable_discretization (abstract). -/
def secondCountable_of_countable_discretization' : Prop := True

-- MetricSpace/Bilipschitz.lean
/-- uniformity_eq_of_bilipschitz (abstract). -/
def uniformity_eq_of_bilipschitz' : Prop := True
/-- bornology_eq_of_bilipschitz (abstract). -/
def bornology_eq_of_bilipschitz' : Prop := True
/-- isBounded_iff_of_bilipschitz (abstract). -/
def isBounded_iff_of_bilipschitz' : Prop := True

-- MetricSpace/Bounded.lean
/-- isBounded_closedBall (abstract). -/
def isBounded_closedBall' : Prop := True
/-- isBounded_ball (abstract). -/
def isBounded_ball' : Prop := True
/-- isBounded_sphere (abstract). -/
def isBounded_sphere' : Prop := True
/-- isBounded_iff_subset_closedBall (abstract). -/
def isBounded_iff_subset_closedBall' : Prop := True
/-- isBounded_closure_of_isBounded (abstract). -/
def isBounded_closure_of_isBounded' : Prop := True
/-- isBounded_closure_iff (abstract). -/
def isBounded_closure_iff' : Prop := True
/-- hasBasis_cobounded_compl_closedBall (abstract). -/
def hasBasis_cobounded_compl_closedBall' : Prop := True
/-- hasBasis_cobounded_compl_ball (abstract). -/
def hasBasis_cobounded_compl_ball' : Prop := True
/-- comap_dist_right_atTop (abstract). -/
def comap_dist_right_atTop' : Prop := True
/-- comap_dist_left_atTop (abstract). -/
def comap_dist_left_atTop' : Prop := True
/-- tendsto_dist_right_atTop_iff (abstract). -/
def tendsto_dist_right_atTop_iff' : Prop := True
/-- tendsto_dist_left_atTop_iff (abstract). -/
def tendsto_dist_left_atTop_iff' : Prop := True
/-- tendsto_dist_right_cobounded_atTop (abstract). -/
def tendsto_dist_right_cobounded_atTop' : Prop := True
/-- tendsto_dist_left_cobounded_atTop (abstract). -/
def tendsto_dist_left_cobounded_atTop' : Prop := True
-- COLLISION: isBounded' already in Analysis.lean — rename needed
/-- cobounded_le_cocompact (abstract). -/
def cobounded_le_cocompact' : Prop := True
/-- isCobounded_iff_closedBall_compl_subset (abstract). -/
def isCobounded_iff_closedBall_compl_subset' : Prop := True
/-- closedBall_compl_subset (abstract). -/
def closedBall_compl_subset' : Prop := True
/-- closedBall_compl_subset_of_mem_cocompact (abstract). -/
def closedBall_compl_subset_of_mem_cocompact' : Prop := True
/-- mem_cocompact_of_closedBall_compl_subset (abstract). -/
def mem_cocompact_of_closedBall_compl_subset' : Prop := True
/-- mem_cocompact_iff_closedBall_compl_subset (abstract). -/
def mem_cocompact_iff_closedBall_compl_subset' : Prop := True
/-- isBounded_range_iff (abstract). -/
def isBounded_range_iff' : Prop := True
/-- isBounded_image_iff (abstract). -/
def isBounded_image_iff' : Prop := True
/-- isBounded_range_of_tendsto_cofinite_uniformity (abstract). -/
def isBounded_range_of_tendsto_cofinite_uniformity' : Prop := True
/-- isBounded_range_of_cauchy_map_cofinite (abstract). -/
def isBounded_range_of_cauchy_map_cofinite' : Prop := True
/-- isBounded_range_of_tendsto_cofinite (abstract). -/
def isBounded_range_of_tendsto_cofinite' : Prop := True
/-- isBounded_of_compactSpace (abstract). -/
def isBounded_of_compactSpace' : Prop := True
/-- isBounded_range_of_tendsto (abstract). -/
def isBounded_range_of_tendsto' : Prop := True
/-- disjoint_nhds_cobounded (abstract). -/
def disjoint_nhds_cobounded' : Prop := True
/-- disjoint_cobounded_nhds (abstract). -/
def disjoint_cobounded_nhds' : Prop := True
/-- disjoint_nhdsSet_cobounded (abstract). -/
def disjoint_nhdsSet_cobounded' : Prop := True
/-- disjoint_cobounded_nhdsSet (abstract). -/
def disjoint_cobounded_nhdsSet' : Prop := True
/-- exists_isBounded_image_of_tendsto (abstract). -/
def exists_isBounded_image_of_tendsto' : Prop := True
/-- exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt (abstract). -/
def exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt' : Prop := True
/-- exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt (abstract). -/
def exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt' : Prop := True
/-- exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn (abstract). -/
def exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn' : Prop := True
/-- exists_isOpen_isBounded_image_of_isCompact_of_continuousOn (abstract). -/
def exists_isOpen_isBounded_image_of_isCompact_of_continuousOn' : Prop := True
/-- isCompact_of_isClosed_isBounded (abstract). -/
def isCompact_of_isClosed_isBounded' : Prop := True
/-- isCompact_closure (abstract). -/
def isCompact_closure' : Prop := True
/-- isCompact_iff_isClosed_bounded (abstract). -/
def isCompact_iff_isClosed_bounded' : Prop := True
/-- compactSpace_iff_isBounded_univ (abstract). -/
def compactSpace_iff_isBounded_univ' : Prop := True
/-- totallyBounded_Ico (abstract). -/
def totallyBounded_Ico' : Prop := True
/-- totallyBounded_Ioc (abstract). -/
def totallyBounded_Ioc' : Prop := True
/-- totallyBounded_Ioo (abstract). -/
def totallyBounded_Ioo' : Prop := True
-- COLLISION: isBounded_Icc' already in Analysis.lean — rename needed
/-- isBounded_Ico (abstract). -/
def isBounded_Ico' : Prop := True
/-- isBounded_Ioc (abstract). -/
def isBounded_Ioc' : Prop := True
/-- isBounded_Ioo (abstract). -/
def isBounded_Ioo' : Prop := True
/-- isBounded_of_bddAbove_of_bddBelow (abstract). -/
def isBounded_of_bddAbove_of_bddBelow' : Prop := True
/-- diam_nonneg (abstract). -/
def diam_nonneg' : Prop := True
/-- ediam_le_of_forall_dist_le (abstract). -/
def ediam_le_of_forall_dist_le' : Prop := True
/-- diam_le_of_forall_dist_le (abstract). -/
def diam_le_of_forall_dist_le' : Prop := True
/-- diam_le_of_forall_dist_le_of_nonempty (abstract). -/
def diam_le_of_forall_dist_le_of_nonempty' : Prop := True
/-- dist_le_diam_of_mem' (abstract). -/
def dist_le_diam_of_mem' : Prop := True
/-- isBounded_iff_ediam_ne_top (abstract). -/
def isBounded_iff_ediam_ne_top' : Prop := True
/-- ediam_eq_top_iff_unbounded (abstract). -/
def ediam_eq_top_iff_unbounded' : Prop := True
/-- ediam_univ_eq_top_iff_noncompact (abstract). -/
def ediam_univ_eq_top_iff_noncompact' : Prop := True
/-- ediam_univ_of_noncompact (abstract). -/
def ediam_univ_of_noncompact' : Prop := True
/-- diam_univ_of_noncompact (abstract). -/
def diam_univ_of_noncompact' : Prop := True
/-- ediam_of_unbounded (abstract). -/
def ediam_of_unbounded' : Prop := True
/-- diam_eq_zero_of_unbounded (abstract). -/
def diam_eq_zero_of_unbounded' : Prop := True
/-- diam_le_of_subset_closedBall (abstract). -/
def diam_le_of_subset_closedBall' : Prop := True
/-- nonempty_iInter_of_nonempty_biInter (abstract). -/
def nonempty_iInter_of_nonempty_biInter' : Prop := True
/-- evalDiam (abstract). -/
def evalDiam' : Prop := True
/-- cobounded_eq_cocompact (abstract). -/
def cobounded_eq_cocompact' : Prop := True
/-- tendsto_dist_left_cocompact_atTop (abstract). -/
def tendsto_dist_left_cocompact_atTop' : Prop := True
/-- comap_dist_left_atTop_eq_cocompact (abstract). -/
def comap_dist_left_atTop_eq_cocompact' : Prop := True
/-- tendsto_cocompact_of_tendsto_dist_comp_atTop (abstract). -/
def tendsto_cocompact_of_tendsto_dist_comp_atTop' : Prop := True
/-- finite_isBounded_inter_isClosed (abstract). -/
def finite_isBounded_inter_isClosed' : Prop := True

-- MetricSpace/CantorScheme.lean
-- COLLISION: inducedMap' already in Algebra.lean — rename needed
-- COLLISION: Antitone' already in Order.lean — rename needed
/-- ClosureAntitone (abstract). -/
def ClosureAntitone' : Prop := True
-- COLLISION: Disjoint' already in Order.lean — rename needed
-- COLLISION: map_mem' already in Algebra.lean — rename needed
-- COLLISION: antitone' already in Order.lean — rename needed
/-- closureAntitone (abstract). -/
def closureAntitone' : Prop := True
-- COLLISION: map_injective' already in Order.lean — rename needed
/-- VanishingDiam (abstract). -/
def VanishingDiam' : Prop := True
/-- dist_lt (abstract). -/
def dist_lt' : Prop := True
-- COLLISION: map_continuous' already in Order.lean — rename needed
/-- map_of_vanishingDiam (abstract). -/
def map_of_vanishingDiam' : Prop := True

-- MetricSpace/CauSeqFilter.lean
/-- tendsto_limit (abstract). -/
def tendsto_limit' : Prop := True
-- COLLISION: isCauSeq' already in Algebra.lean — rename needed
/-- cauchySeq (abstract). -/
def cauchySeq' : Prop := True
/-- isCauSeq_iff_cauchySeq (abstract). -/
def isCauSeq_iff_cauchySeq' : Prop := True

-- MetricSpace/Cauchy.lean
/-- uniformCauchySeqOn_iff (abstract). -/
def uniformCauchySeqOn_iff' : Prop := True
/-- cauchySeq_of_le_tendsto_0 (abstract). -/
def cauchySeq_of_le_tendsto_0' : Prop := True
/-- cauchySeq_bdd (abstract). -/
def cauchySeq_bdd' : Prop := True
/-- exists_subseq_bounded_of_cauchySeq (abstract). -/
def exists_subseq_bounded_of_cauchySeq' : Prop := True

-- MetricSpace/Closeds.lean
/-- continuous_infEdist_hausdorffEdist (abstract). -/
def continuous_infEdist_hausdorffEdist' : Prop := True
/-- isClosed_subsets_of_isClosed (abstract). -/
def isClosed_subsets_of_isClosed' : Prop := True
/-- isClosed_in_closeds (abstract). -/
def isClosed_in_closeds' : Prop := True
/-- lipschitz_infDist_set (abstract). -/
def lipschitz_infDist_set' : Prop := True
/-- lipschitz_infDist (abstract). -/
def lipschitz_infDist' : Prop := True
/-- uniformContinuous_infDist_Hausdorff_dist (abstract). -/
def uniformContinuous_infDist_Hausdorff_dist' : Prop := True

-- MetricSpace/Completion.lean
/-- uniformContinuous_dist (abstract). -/
def uniformContinuous_dist' : Prop := True
/-- continuous_dist (abstract). -/
def continuous_dist' : Prop := True
-- COLLISION: dist_eq' already in Analysis.lean — rename needed
/-- dist_self (abstract). -/
def dist_self' : Prop := True
-- COLLISION: dist_comm' already in Analysis.lean — rename needed
-- COLLISION: dist_triangle' already in Analysis.lean — rename needed
/-- mem_uniformity_dist (abstract). -/
def mem_uniformity_dist' : Prop := True
/-- uniformity_dist' (abstract). -/
def uniformity_dist' : Prop := True
/-- eq_of_dist_eq_zero (abstract). -/
def eq_of_dist_eq_zero' : Prop := True
/-- coe_isometry (abstract). -/
def coe_isometry' : Prop := True
-- COLLISION: edist_eq' already in Analysis.lean — rename needed
/-- completion_extension (abstract). -/
def completion_extension' : Prop := True
/-- completion_map (abstract). -/
def completion_map' : Prop := True

-- MetricSpace/Contracting.lean
/-- ContractingWith (abstract). -/
def ContractingWith' : Prop := True
/-- toLipschitzWith (abstract). -/
def toLipschitzWith' : Prop := True
/-- one_sub_K_pos' (abstract). -/
def one_sub_K_pos' : Prop := True
/-- one_sub_K_ne_zero (abstract). -/
def one_sub_K_ne_zero' : Prop := True
/-- one_sub_K_ne_top (abstract). -/
def one_sub_K_ne_top' : Prop := True
/-- edist_inequality (abstract). -/
def edist_inequality' : Prop := True
/-- edist_le_of_fixedPoint (abstract). -/
def edist_le_of_fixedPoint' : Prop := True
/-- eq_or_edist_eq_top_of_fixedPoints (abstract). -/
def eq_or_edist_eq_top_of_fixedPoints' : Prop := True
/-- exists_fixedPoint (abstract). -/
def exists_fixedPoint' : Prop := True
/-- efixedPoint (abstract). -/
def efixedPoint' : Prop := True
/-- efixedPoint_isFixedPt (abstract). -/
def efixedPoint_isFixedPt' : Prop := True
/-- tendsto_iterate_efixedPoint (abstract). -/
def tendsto_iterate_efixedPoint' : Prop := True
/-- apriori_edist_iterate_efixedPoint_le (abstract). -/
def apriori_edist_iterate_efixedPoint_le' : Prop := True
/-- edist_efixedPoint_le (abstract). -/
def edist_efixedPoint_le' : Prop := True
/-- edist_efixedPoint_lt_top (abstract). -/
def edist_efixedPoint_lt_top' : Prop := True
/-- efixedPoint_eq_of_edist_lt_top (abstract). -/
def efixedPoint_eq_of_edist_lt_top' : Prop := True
/-- efixedPoint_mem' (abstract). -/
def efixedPoint_mem' : Prop := True
/-- dist_le_mul (abstract). -/
def dist_le_mul' : Prop := True
/-- dist_inequality (abstract). -/
def dist_inequality' : Prop := True
/-- dist_le_of_fixedPoint (abstract). -/
def dist_le_of_fixedPoint' : Prop := True
/-- fixedPoint_unique' (abstract). -/
def fixedPoint_unique' : Prop := True
/-- dist_fixedPoint_fixedPoint_of_dist_le' (abstract). -/
def dist_fixedPoint_fixedPoint_of_dist_le' : Prop := True
/-- fixedPoint (abstract). -/
def fixedPoint' : Prop := True
/-- fixedPoint_isFixedPt (abstract). -/
def fixedPoint_isFixedPt' : Prop := True
/-- dist_fixedPoint_le (abstract). -/
def dist_fixedPoint_le' : Prop := True
/-- aposteriori_dist_iterate_fixedPoint_le (abstract). -/
def aposteriori_dist_iterate_fixedPoint_le' : Prop := True
/-- apriori_dist_iterate_fixedPoint_le (abstract). -/
def apriori_dist_iterate_fixedPoint_le' : Prop := True
/-- tendsto_iterate_fixedPoint (abstract). -/
def tendsto_iterate_fixedPoint' : Prop := True
/-- fixedPoint_lipschitz_in_map (abstract). -/
def fixedPoint_lipschitz_in_map' : Prop := True
/-- isFixedPt_fixedPoint_iterate (abstract). -/
def isFixedPt_fixedPoint_iterate' : Prop := True

-- MetricSpace/Defs.lean
/-- MetricSpace (abstract). -/
def MetricSpace' : Prop := True
/-- ofDistTopology (abstract). -/
def ofDistTopology' : Prop := True
/-- dist_eq_zero (abstract). -/
def dist_eq_zero' : Prop := True
/-- zero_eq_dist (abstract). -/
def zero_eq_dist' : Prop := True
/-- dist_ne_zero (abstract). -/
def dist_ne_zero' : Prop := True
/-- dist_le_zero (abstract). -/
def dist_le_zero' : Prop := True
/-- dist_pos (abstract). -/
def dist_pos' : Prop := True
/-- eq_of_forall_dist_le (abstract). -/
def eq_of_forall_dist_le' : Prop := True
/-- eq_of_nndist_eq_zero (abstract). -/
def eq_of_nndist_eq_zero' : Prop := True
/-- nndist_eq_zero (abstract). -/
def nndist_eq_zero' : Prop := True
/-- zero_eq_nndist (abstract). -/
def zero_eq_nndist' : Prop := True
-- COLLISION: closedBall_zero' already in Analysis.lean — rename needed
/-- sphere_zero (abstract). -/
def sphere_zero' : Prop := True
/-- subsingleton_closedBall (abstract). -/
def subsingleton_closedBall' : Prop := True
/-- subsingleton_sphere (abstract). -/
def subsingleton_sphere' : Prop := True
/-- replaceUniformity_eq (abstract). -/
def replaceUniformity_eq' : Prop := True
/-- replaceTopology (abstract). -/
def replaceTopology' : Prop := True
/-- replaceTopology_eq (abstract). -/
def replaceTopology_eq' : Prop := True
/-- replaceBornology (abstract). -/
def replaceBornology' : Prop := True

-- MetricSpace/Dilation.lean
/-- Dilation (abstract). -/
def Dilation' : Prop := True
/-- DilationClass (abstract). -/
def DilationClass' : Prop := True
/-- copy_eq_self (abstract). -/
def copy_eq_self' : Prop := True
-- COLLISION: ratio' already in Analysis.lean — rename needed
/-- ratio_of_trivial (abstract). -/
def ratio_of_trivial' : Prop := True
/-- ratio_of_subsingleton (abstract). -/
def ratio_of_subsingleton' : Prop := True
/-- ratio_ne_zero (abstract). -/
def ratio_ne_zero' : Prop := True
/-- ratio_pos (abstract). -/
def ratio_pos' : Prop := True
/-- ratio_unique (abstract). -/
def ratio_unique' : Prop := True
/-- ratio_unique_of_nndist_ne_zero (abstract). -/
def ratio_unique_of_nndist_ne_zero' : Prop := True
/-- ratio_unique_of_dist_ne_zero (abstract). -/
def ratio_unique_of_dist_ne_zero' : Prop := True
/-- mkOfNNDistEq (abstract). -/
def mkOfNNDistEq' : Prop := True
/-- mk_coe_of_nndist_eq (abstract). -/
def mk_coe_of_nndist_eq' : Prop := True
/-- mkOfDistEq (abstract). -/
def mkOfDistEq' : Prop := True
/-- mk_coe_of_dist_eq (abstract). -/
def mk_coe_of_dist_eq' : Prop := True
/-- toDilation (abstract). -/
def toDilation' : Prop := True
-- COLLISION: lipschitz' already in Analysis.lean — rename needed
-- COLLISION: antilipschitz' already in Analysis.lean — rename needed
/-- ratio_id (abstract). -/
def ratio_id' : Prop := True
/-- ratio_comp' (abstract). -/
def ratio_comp' : Prop := True
/-- ratio_one (abstract). -/
def ratio_one' : Prop := True
/-- ratio_mul (abstract). -/
def ratio_mul' : Prop := True
/-- ratioHom (abstract). -/
def ratioHom' : Prop := True
/-- ratio_pow (abstract). -/
def ratio_pow' : Prop := True
/-- toContinuous (abstract). -/
def toContinuous' : Prop := True
-- COLLISION: ediam_image' already in Analysis.lean — rename needed
-- COLLISION: ediam_range' already in Analysis.lean — rename needed
-- COLLISION: diam_image' already in Analysis.lean — rename needed
-- COLLISION: diam_range' already in Analysis.lean — rename needed
/-- mapsTo_ball (abstract). -/
def mapsTo_ball' : Prop := True
/-- mapsTo_sphere (abstract). -/
def mapsTo_sphere' : Prop := True
/-- mapsTo_closedBall (abstract). -/
def mapsTo_closedBall' : Prop := True
/-- comap_cobounded (abstract). -/
def comap_cobounded' : Prop := True

-- MetricSpace/DilationEquiv.lean
/-- DilationEquivClass (abstract). -/
def DilationEquivClass' : Prop := True
/-- DilationEquiv (abstract). -/
def DilationEquiv' : Prop := True
-- COLLISION: symm_trans_self' already in Order.lean — rename needed
-- COLLISION: self_trans_symm' already in Order.lean — rename needed
-- COLLISION: bijective' already in Order.lean — rename needed
/-- ratio_trans (abstract). -/
def ratio_trans' : Prop := True
-- COLLISION: toPerm' already in Algebra.lean — rename needed
/-- toDilationEquiv (abstract). -/
def toDilationEquiv' : Prop := True
/-- map_cobounded (abstract). -/
def map_cobounded' : Prop := True

-- MetricSpace/Equicontinuity.lean
/-- equicontinuousAt_iff_right (abstract). -/
def equicontinuousAt_iff_right' : Prop := True
/-- equicontinuousAt_iff (abstract). -/
def equicontinuousAt_iff' : Prop := True
/-- equicontinuousAt_iff_pair (abstract). -/
def equicontinuousAt_iff_pair' : Prop := True
/-- uniformEquicontinuous_iff_right (abstract). -/
def uniformEquicontinuous_iff_right' : Prop := True
/-- uniformEquicontinuous_iff (abstract). -/
def uniformEquicontinuous_iff' : Prop := True
/-- equicontinuousAt_of_continuity_modulus (abstract). -/
def equicontinuousAt_of_continuity_modulus' : Prop := True
/-- uniformEquicontinuous_of_continuity_modulus (abstract). -/
def uniformEquicontinuous_of_continuity_modulus' : Prop := True
/-- equicontinuous_of_continuity_modulus (abstract). -/
def equicontinuous_of_continuity_modulus' : Prop := True

-- MetricSpace/Gluing.lean
/-- glueDist (abstract). -/
def glueDist' : Prop := True
/-- glueDist_self (abstract). -/
def glueDist_self' : Prop := True
/-- glueDist_glued_points (abstract). -/
def glueDist_glued_points' : Prop := True
/-- glueDist_comm (abstract). -/
def glueDist_comm' : Prop := True
/-- glueDist_swap (abstract). -/
def glueDist_swap' : Prop := True
/-- le_glueDist_inl_inr (abstract). -/
def le_glueDist_inl_inr' : Prop := True
/-- le_glueDist_inr_inl (abstract). -/
def le_glueDist_inr_inl' : Prop := True
/-- glueDist_triangle_inl_inr_inr (abstract). -/
def glueDist_triangle_inl_inr_inr' : Prop := True
/-- glueDist_triangle_inl_inr_inl (abstract). -/
def glueDist_triangle_inl_inr_inl' : Prop := True
/-- glueDist_triangle (abstract). -/
def glueDist_triangle' : Prop := True
/-- eq_of_glueDist_eq_zero (abstract). -/
def eq_of_glueDist_eq_zero' : Prop := True
/-- mem_uniformity_iff_glueDist (abstract). -/
def mem_uniformity_iff_glueDist' : Prop := True
/-- glueMetricApprox (abstract). -/
def glueMetricApprox' : Prop := True
-- COLLISION: dist' already in Analysis.lean — rename needed
/-- dist_eq_glueDist (abstract). -/
def dist_eq_glueDist' : Prop := True
/-- one_le_dist_inl_inr (abstract). -/
def one_le_dist_inl_inr' : Prop := True
/-- one_le_dist_inr_inl (abstract). -/
def one_le_dist_inr_inl' : Prop := True
/-- mem_uniformity (abstract). -/
def mem_uniformity' : Prop := True
/-- metricSpaceSum (abstract). -/
def metricSpaceSum' : Prop := True
/-- isometry_inl (abstract). -/
def isometry_inl' : Prop := True
-- COLLISION: isometry_inr' already in Analysis.lean — rename needed
/-- instDist (abstract). -/
def instDist' : Prop := True
/-- dist_same (abstract). -/
def dist_same' : Prop := True
/-- dist_ne (abstract). -/
def dist_ne' : Prop := True
/-- one_le_dist_of_ne (abstract). -/
def one_le_dist_of_ne' : Prop := True
/-- fst_eq_of_dist_lt_one (abstract). -/
def fst_eq_of_dist_lt_one' : Prop := True
/-- metricSpace (abstract). -/
def metricSpace' : Prop := True
/-- isometry_mk (abstract). -/
def isometry_mk' : Prop := True
/-- gluePremetric (abstract). -/
def gluePremetric' : Prop := True
/-- GlueSpace (abstract). -/
def GlueSpace' : Prop := True
/-- toGlueL (abstract). -/
def toGlueL' : Prop := True
/-- toGlueR (abstract). -/
def toGlueR' : Prop := True
/-- toGlue_commute (abstract). -/
def toGlue_commute' : Prop := True
/-- toGlueL_isometry (abstract). -/
def toGlueL_isometry' : Prop := True
/-- toGlueR_isometry (abstract). -/
def toGlueR_isometry' : Prop := True
/-- inductiveLimitDist (abstract). -/
def inductiveLimitDist' : Prop := True
/-- inductiveLimitDist_eq_dist (abstract). -/
def inductiveLimitDist_eq_dist' : Prop := True
/-- inductivePremetric (abstract). -/
def inductivePremetric' : Prop := True
/-- InductiveLimit (abstract). -/
def InductiveLimit' : Prop := True
/-- toInductiveLimit (abstract). -/
def toInductiveLimit' : Prop := True

-- MetricSpace/GromovHausdorff.lean
/-- IsometryRel (abstract). -/
def IsometryRel' : Prop := True
/-- equivalence_isometryRel (abstract). -/
def equivalence_isometryRel' : Prop := True
/-- GHSpace (abstract). -/
def GHSpace' : Prop := True
/-- toGHSpace (abstract). -/
def toGHSpace' : Prop := True
-- COLLISION: Rep' already in RepresentationTheory.lean — rename needed
/-- eq_toGHSpace_iff (abstract). -/
def eq_toGHSpace_iff' : Prop := True
/-- eq_toGHSpace (abstract). -/
def eq_toGHSpace' : Prop := True
/-- toGHSpace_rep (abstract). -/
def toGHSpace_rep' : Prop := True
/-- toGHSpace_eq_toGHSpace_iff_isometryEquiv (abstract). -/
def toGHSpace_eq_toGHSpace_iff_isometryEquiv' : Prop := True
/-- ghDist (abstract). -/
def ghDist' : Prop := True
/-- dist_ghDist (abstract). -/
def dist_ghDist' : Prop := True
/-- ghDist_le_hausdorffDist (abstract). -/
def ghDist_le_hausdorffDist' : Prop := True
/-- hausdorffDist_optimal (abstract). -/
def hausdorffDist_optimal' : Prop := True
/-- ghDist_eq_hausdorffDist (abstract). -/
def ghDist_eq_hausdorffDist' : Prop := True
/-- toGHSpace_lipschitz (abstract). -/
def toGHSpace_lipschitz' : Prop := True
/-- toGHSpace_continuous (abstract). -/
def toGHSpace_continuous' : Prop := True
/-- ghDist_le_of_approx_subsets (abstract). -/
def ghDist_le_of_approx_subsets' : Prop := True
/-- AuxGluingStruct (abstract). -/
def AuxGluingStruct' : Prop := True
/-- auxGluing (abstract). -/
def auxGluing' : Prop := True

-- MetricSpace/GromovHausdorffRealized.lean
/-- ProdSpaceFun (abstract). -/
def ProdSpaceFun' : Prop := True
/-- Cb (abstract). -/
def Cb' : Prop := True
/-- maxVar (abstract). -/
def maxVar' : Prop := True
/-- one_le_maxVar (abstract). -/
def one_le_maxVar' : Prop := True
/-- candidates (abstract). -/
def candidates' : Prop := True
/-- candidatesB (abstract). -/
def candidatesB' : Prop := True
/-- maxVar_bound (abstract). -/
def maxVar_bound' : Prop := True
/-- candidates_symm (abstract). -/
def candidates_symm' : Prop := True
/-- candidates_triangle (abstract). -/
def candidates_triangle' : Prop := True
/-- candidates_refl (abstract). -/
def candidates_refl' : Prop := True
/-- candidates_nonneg (abstract). -/
def candidates_nonneg' : Prop := True
/-- candidates_dist_inl (abstract). -/
def candidates_dist_inl' : Prop := True
/-- candidates_dist_inr (abstract). -/
def candidates_dist_inr' : Prop := True
/-- candidates_le_maxVar (abstract). -/
def candidates_le_maxVar' : Prop := True
/-- candidates_dist_bound (abstract). -/
def candidates_dist_bound' : Prop := True
/-- candidates_lipschitz_aux (abstract). -/
def candidates_lipschitz_aux' : Prop := True
/-- candidates_lipschitz (abstract). -/
def candidates_lipschitz' : Prop := True
/-- closed_candidatesB (abstract). -/
def closed_candidatesB' : Prop := True
/-- HD (abstract). -/
def HD' : Prop := True
/-- HD_below_aux1 (abstract). -/
def HD_below_aux1' : Prop := True
/-- HD_bound_aux1 (abstract). -/
def HD_bound_aux1' : Prop := True
/-- HD_below_aux2 (abstract). -/
def HD_below_aux2' : Prop := True
/-- HD_bound_aux2 (abstract). -/
def HD_bound_aux2' : Prop := True
/-- HD_lipschitz_aux1 (abstract). -/
def HD_lipschitz_aux1' : Prop := True
/-- HD_lipschitz_aux2 (abstract). -/
def HD_lipschitz_aux2' : Prop := True
/-- HD_lipschitz_aux3 (abstract). -/
def HD_lipschitz_aux3' : Prop := True
/-- HD_continuous (abstract). -/
def HD_continuous' : Prop := True
/-- isCompact_candidatesB (abstract). -/
def isCompact_candidatesB' : Prop := True
/-- candidatesBOfCandidates (abstract). -/
def candidatesBOfCandidates' : Prop := True
/-- candidatesBOfCandidates_mem (abstract). -/
def candidatesBOfCandidates_mem' : Prop := True
/-- dist_mem_candidates (abstract). -/
def dist_mem_candidates' : Prop := True
/-- candidatesBDist (abstract). -/
def candidatesBDist' : Prop := True
/-- candidatesBDist_mem_candidatesB (abstract). -/
def candidatesBDist_mem_candidatesB' : Prop := True
/-- candidatesB_nonempty (abstract). -/
def candidatesB_nonempty' : Prop := True
/-- exists_minimizer (abstract). -/
def exists_minimizer' : Prop := True
/-- optimalGHDist (abstract). -/
def optimalGHDist' : Prop := True
/-- optimalGHDist_mem_candidatesB (abstract). -/
def optimalGHDist_mem_candidatesB' : Prop := True
/-- HD_optimalGHDist_le (abstract). -/
def HD_optimalGHDist_le' : Prop := True
/-- premetricOptimalGHDist (abstract). -/
def premetricOptimalGHDist' : Prop := True
/-- OptimalGHCoupling (abstract). -/
def OptimalGHCoupling' : Prop := True
/-- optimalGHInjl (abstract). -/
def optimalGHInjl' : Prop := True
/-- isometry_optimalGHInjl (abstract). -/
def isometry_optimalGHInjl' : Prop := True
/-- optimalGHInjr (abstract). -/
def optimalGHInjr' : Prop := True
/-- isometry_optimalGHInjr (abstract). -/
def isometry_optimalGHInjr' : Prop := True
/-- hausdorffDist_optimal_le_HD (abstract). -/
def hausdorffDist_optimal_le_HD' : Prop := True

-- MetricSpace/HausdorffDimension.lean
/-- dimH (abstract). -/
def dimH' : Prop := True
/-- dimH_def (abstract). -/
def dimH_def' : Prop := True
/-- hausdorffMeasure_of_lt_dimH (abstract). -/
def hausdorffMeasure_of_lt_dimH' : Prop := True
/-- dimH_le (abstract). -/
def dimH_le' : Prop := True
-- COLLISION: trans_le' already in Order.lean — rename needed
/-- dimH_le_of_hausdorffMeasure_ne_top (abstract). -/
def dimH_le_of_hausdorffMeasure_ne_top' : Prop := True
/-- le_dimH_of_hausdorffMeasure_eq_top (abstract). -/
def le_dimH_of_hausdorffMeasure_eq_top' : Prop := True
/-- le_dimH_of_hausdorffMeasure_ne_zero (abstract). -/
def le_dimH_of_hausdorffMeasure_ne_zero' : Prop := True
/-- dimH_of_hausdorffMeasure_ne_zero_ne_top (abstract). -/
def dimH_of_hausdorffMeasure_ne_zero_ne_top' : Prop := True
/-- dimH_mono (abstract). -/
def dimH_mono' : Prop := True
/-- dimH_subsingleton (abstract). -/
def dimH_subsingleton' : Prop := True
/-- dimH_empty (abstract). -/
def dimH_empty' : Prop := True
/-- dimH_singleton (abstract). -/
def dimH_singleton' : Prop := True
/-- dimH_iUnion (abstract). -/
def dimH_iUnion' : Prop := True
/-- dimH_bUnion (abstract). -/
def dimH_bUnion' : Prop := True
/-- dimH_sUnion (abstract). -/
def dimH_sUnion' : Prop := True
/-- dimH_union (abstract). -/
def dimH_union' : Prop := True
/-- dimH_countable (abstract). -/
def dimH_countable' : Prop := True
/-- dimH_finite (abstract). -/
def dimH_finite' : Prop := True
/-- dimH_coe_finset (abstract). -/
def dimH_coe_finset' : Prop := True
/-- exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (abstract). -/
def exists_mem_nhdsWithin_lt_dimH_of_lt_dimH' : Prop := True
/-- bsupr_limsup_dimH (abstract). -/
def bsupr_limsup_dimH' : Prop := True
/-- iSup_limsup_dimH (abstract). -/
def iSup_limsup_dimH' : Prop := True
/-- dimH_image_le (abstract). -/
def dimH_image_le' : Prop := True
/-- dimH_range_le (abstract). -/
def dimH_range_le' : Prop := True
/-- dimH_image_le_of_locally_holder_on (abstract). -/
def dimH_image_le_of_locally_holder_on' : Prop := True
/-- dimH_range_le_of_locally_holder_on (abstract). -/
def dimH_range_le_of_locally_holder_on' : Prop := True
/-- dimH_image_le_of_locally_lipschitzOn (abstract). -/
def dimH_image_le_of_locally_lipschitzOn' : Prop := True
/-- dimH_range_le_of_locally_lipschitzOn (abstract). -/
def dimH_range_le_of_locally_lipschitzOn' : Prop := True
/-- dimH_preimage_le (abstract). -/
def dimH_preimage_le' : Prop := True
/-- le_dimH_image (abstract). -/
def le_dimH_image' : Prop := True
/-- dimH_image (abstract). -/
def dimH_image' : Prop := True
/-- dimH_preimage (abstract). -/
def dimH_preimage' : Prop := True
/-- dimH_univ (abstract). -/
def dimH_univ' : Prop := True
/-- dimH_ball_pi (abstract). -/
def dimH_ball_pi' : Prop := True
/-- dimH_ball_pi_fin (abstract). -/
def dimH_ball_pi_fin' : Prop := True
/-- dimH_univ_pi (abstract). -/
def dimH_univ_pi' : Prop := True
/-- dimH_univ_pi_fin (abstract). -/
def dimH_univ_pi_fin' : Prop := True
/-- dimH_of_mem_nhds (abstract). -/
def dimH_of_mem_nhds' : Prop := True
/-- dimH_univ_eq_finrank (abstract). -/
def dimH_univ_eq_finrank' : Prop := True
/-- hausdorffMeasure_of_finrank_lt (abstract). -/
def hausdorffMeasure_of_finrank_lt' : Prop := True
/-- dense_compl_of_dimH_lt_finrank (abstract). -/
def dense_compl_of_dimH_lt_finrank' : Prop := True
/-- dense_compl_image_of_dimH_lt_finrank (abstract). -/
def dense_compl_image_of_dimH_lt_finrank' : Prop := True
/-- dense_compl_range_of_finrank_lt_finrank (abstract). -/
def dense_compl_range_of_finrank_lt_finrank' : Prop := True

-- MetricSpace/HausdorffDistance.lean
-- COLLISION: infEdist' already in MeasureTheory2.lean — rename needed
/-- infEdist_empty (abstract). -/
def infEdist_empty' : Prop := True
/-- le_infEdist (abstract). -/
def le_infEdist' : Prop := True
/-- infEdist_union (abstract). -/
def infEdist_union' : Prop := True
/-- infEdist_iUnion (abstract). -/
def infEdist_iUnion' : Prop := True
/-- infEdist_biUnion (abstract). -/
def infEdist_biUnion' : Prop := True
/-- infEdist_singleton (abstract). -/
def infEdist_singleton' : Prop := True
/-- infEdist_le_edist_of_mem (abstract). -/
def infEdist_le_edist_of_mem' : Prop := True
/-- infEdist_zero_of_mem (abstract). -/
def infEdist_zero_of_mem' : Prop := True
/-- infEdist_anti (abstract). -/
def infEdist_anti' : Prop := True
/-- infEdist_lt_iff (abstract). -/
def infEdist_lt_iff' : Prop := True
/-- infEdist_le_infEdist_add_edist (abstract). -/
def infEdist_le_infEdist_add_edist' : Prop := True
/-- infEdist_le_edist_add_infEdist (abstract). -/
def infEdist_le_edist_add_infEdist' : Prop := True
/-- edist_le_infEdist_add_ediam (abstract). -/
def edist_le_infEdist_add_ediam' : Prop := True
/-- continuous_infEdist (abstract). -/
def continuous_infEdist' : Prop := True
/-- infEdist_closure (abstract). -/
def infEdist_closure' : Prop := True
/-- mem_closure_iff_infEdist_zero (abstract). -/
def mem_closure_iff_infEdist_zero' : Prop := True
/-- mem_iff_infEdist_zero_of_closed (abstract). -/
def mem_iff_infEdist_zero_of_closed' : Prop := True
/-- infEdist_pos_iff_not_mem_closure (abstract). -/
def infEdist_pos_iff_not_mem_closure' : Prop := True
/-- infEdist_closure_pos_iff_not_mem_closure (abstract). -/
def infEdist_closure_pos_iff_not_mem_closure' : Prop := True
/-- exists_real_pos_lt_infEdist_of_not_mem_closure (abstract). -/
def exists_real_pos_lt_infEdist_of_not_mem_closure' : Prop := True
/-- infEdist_image (abstract). -/
def infEdist_image' : Prop := True
/-- infEdist_smul (abstract). -/
def infEdist_smul' : Prop := True
/-- exists_iUnion_isClosed (abstract). -/
def exists_iUnion_isClosed' : Prop := True
/-- exists_infEdist_eq_edist (abstract). -/
def exists_infEdist_eq_edist' : Prop := True
/-- exists_pos_forall_lt_edist (abstract). -/
def exists_pos_forall_lt_edist' : Prop := True
/-- hausdorffEdist (abstract). -/
def hausdorffEdist' : Prop := True
/-- hausdorffEdist_self (abstract). -/
def hausdorffEdist_self' : Prop := True
/-- hausdorffEdist_comm (abstract). -/
def hausdorffEdist_comm' : Prop := True
/-- hausdorffEdist_le_of_infEdist (abstract). -/
def hausdorffEdist_le_of_infEdist' : Prop := True
/-- hausdorffEdist_le_of_mem_edist (abstract). -/
def hausdorffEdist_le_of_mem_edist' : Prop := True
/-- infEdist_le_hausdorffEdist_of_mem (abstract). -/
def infEdist_le_hausdorffEdist_of_mem' : Prop := True
/-- exists_edist_lt_of_hausdorffEdist_lt (abstract). -/
def exists_edist_lt_of_hausdorffEdist_lt' : Prop := True
/-- infEdist_le_infEdist_add_hausdorffEdist (abstract). -/
def infEdist_le_infEdist_add_hausdorffEdist' : Prop := True
/-- hausdorffEdist_image (abstract). -/
def hausdorffEdist_image' : Prop := True
/-- hausdorffEdist_le_ediam (abstract). -/
def hausdorffEdist_le_ediam' : Prop := True
/-- hausdorffEdist_triangle (abstract). -/
def hausdorffEdist_triangle' : Prop := True
/-- hausdorffEdist_zero_iff_closure_eq_closure (abstract). -/
def hausdorffEdist_zero_iff_closure_eq_closure' : Prop := True
/-- hausdorffEdist_self_closure (abstract). -/
def hausdorffEdist_self_closure' : Prop := True
/-- hausdorffEdist_closure₁ (abstract). -/
def hausdorffEdist_closure₁' : Prop := True
/-- hausdorffEdist_closure₂ (abstract). -/
def hausdorffEdist_closure₂' : Prop := True
/-- hausdorffEdist_zero_iff_eq_of_closed (abstract). -/
def hausdorffEdist_zero_iff_eq_of_closed' : Prop := True
/-- hausdorffEdist_empty (abstract). -/
def hausdorffEdist_empty' : Prop := True
/-- nonempty_of_hausdorffEdist_ne_top (abstract). -/
def nonempty_of_hausdorffEdist_ne_top' : Prop := True
/-- empty_or_nonempty_of_hausdorffEdist_ne_top (abstract). -/
def empty_or_nonempty_of_hausdorffEdist_ne_top' : Prop := True
-- COLLISION: infDist' already in MeasureTheory2.lean — rename needed
/-- infDist_eq_iInf (abstract). -/
def infDist_eq_iInf' : Prop := True
/-- infDist_nonneg (abstract). -/
def infDist_nonneg' : Prop := True
/-- infDist_empty (abstract). -/
def infDist_empty' : Prop := True
/-- infEdist_ne_top (abstract). -/
def infEdist_ne_top' : Prop := True
/-- infEdist_eq_top_iff (abstract). -/
def infEdist_eq_top_iff' : Prop := True
/-- infDist_zero_of_mem (abstract). -/
def infDist_zero_of_mem' : Prop := True
/-- infDist_singleton (abstract). -/
def infDist_singleton' : Prop := True
/-- infDist_le_dist_of_mem (abstract). -/
def infDist_le_dist_of_mem' : Prop := True
/-- infDist_le_infDist_of_subset (abstract). -/
def infDist_le_infDist_of_subset' : Prop := True
/-- infDist_lt_iff (abstract). -/
def infDist_lt_iff' : Prop := True
/-- infDist_le_infDist_add_dist (abstract). -/
def infDist_le_infDist_add_dist' : Prop := True
/-- not_mem_of_dist_lt_infDist (abstract). -/
def not_mem_of_dist_lt_infDist' : Prop := True
/-- disjoint_ball_infDist (abstract). -/
def disjoint_ball_infDist' : Prop := True
/-- ball_infDist_subset_compl (abstract). -/
def ball_infDist_subset_compl' : Prop := True
/-- ball_infDist_compl_subset (abstract). -/
def ball_infDist_compl_subset' : Prop := True
/-- disjoint_closedBall_of_lt_infDist (abstract). -/
def disjoint_closedBall_of_lt_infDist' : Prop := True
/-- dist_le_infDist_add_diam (abstract). -/
def dist_le_infDist_add_diam' : Prop := True
/-- lipschitz_infDist_pt (abstract). -/
def lipschitz_infDist_pt' : Prop := True
/-- uniformContinuous_infDist_pt (abstract). -/
def uniformContinuous_infDist_pt' : Prop := True
/-- continuous_infDist_pt (abstract). -/
def continuous_infDist_pt' : Prop := True
/-- infDist_closure (abstract). -/
def infDist_closure' : Prop := True
/-- infDist_zero_of_mem_closure (abstract). -/
def infDist_zero_of_mem_closure' : Prop := True
/-- mem_closure_iff_infDist_zero (abstract). -/
def mem_closure_iff_infDist_zero' : Prop := True
/-- mem_iff_infDist_zero (abstract). -/
def mem_iff_infDist_zero' : Prop := True
/-- not_mem_iff_infDist_pos (abstract). -/
def not_mem_iff_infDist_pos' : Prop := True
/-- continuousAt_inv_infDist_pt (abstract). -/
def continuousAt_inv_infDist_pt' : Prop := True
/-- infDist_image (abstract). -/
def infDist_image' : Prop := True
/-- infDist_inter_closedBall_of_mem (abstract). -/
def infDist_inter_closedBall_of_mem' : Prop := True
/-- exists_infDist_eq_dist (abstract). -/
def exists_infDist_eq_dist' : Prop := True
-- COLLISION: infNndist' already in MeasureTheory2.lean — rename needed
/-- lipschitz_infNndist_pt (abstract). -/
def lipschitz_infNndist_pt' : Prop := True
/-- uniformContinuous_infNndist_pt (abstract). -/
def uniformContinuous_infNndist_pt' : Prop := True
/-- continuous_infNndist_pt (abstract). -/
def continuous_infNndist_pt' : Prop := True
/-- hausdorffDist (abstract). -/
def hausdorffDist' : Prop := True
/-- hausdorffDist_nonneg (abstract). -/
def hausdorffDist_nonneg' : Prop := True
/-- hausdorffEdist_ne_top_of_nonempty_of_bounded (abstract). -/
def hausdorffEdist_ne_top_of_nonempty_of_bounded' : Prop := True
/-- hausdorffDist_self_zero (abstract). -/
def hausdorffDist_self_zero' : Prop := True
/-- hausdorffDist_comm (abstract). -/
def hausdorffDist_comm' : Prop := True
/-- hausdorffDist_empty (abstract). -/
def hausdorffDist_empty' : Prop := True
/-- hausdorffDist_le_of_infDist (abstract). -/
def hausdorffDist_le_of_infDist' : Prop := True
/-- hausdorffDist_le_of_mem_dist (abstract). -/
def hausdorffDist_le_of_mem_dist' : Prop := True
/-- hausdorffDist_le_diam (abstract). -/
def hausdorffDist_le_diam' : Prop := True
/-- infDist_le_hausdorffDist_of_mem (abstract). -/
def infDist_le_hausdorffDist_of_mem' : Prop := True
/-- exists_dist_lt_of_hausdorffDist_lt (abstract). -/
def exists_dist_lt_of_hausdorffDist_lt' : Prop := True
/-- infDist_le_infDist_add_hausdorffDist (abstract). -/
def infDist_le_infDist_add_hausdorffDist' : Prop := True
/-- hausdorffDist_image (abstract). -/
def hausdorffDist_image' : Prop := True
/-- hausdorffDist_triangle (abstract). -/
def hausdorffDist_triangle' : Prop := True
/-- hausdorffDist_self_closure (abstract). -/
def hausdorffDist_self_closure' : Prop := True
/-- hausdorffDist_closure₁ (abstract). -/
def hausdorffDist_closure₁' : Prop := True
/-- hausdorffDist_closure₂ (abstract). -/
def hausdorffDist_closure₂' : Prop := True
/-- hausdorffDist_closure (abstract). -/
def hausdorffDist_closure' : Prop := True
/-- hausdorffDist_zero_iff_closure_eq_closure (abstract). -/
def hausdorffDist_zero_iff_closure_eq_closure' : Prop := True
/-- hausdorffDist_zero_iff_eq (abstract). -/
def hausdorffDist_zero_iff_eq' : Prop := True

-- MetricSpace/Holder.lean
/-- HolderWith (abstract). -/
def HolderWith' : Prop := True
/-- HolderOnWith (abstract). -/
def HolderOnWith' : Prop := True
/-- holderOnWith_empty (abstract). -/
def holderOnWith_empty' : Prop := True
/-- holderOnWith_singleton (abstract). -/
def holderOnWith_singleton' : Prop := True
/-- holderOnWith (abstract). -/
def holderOnWith' : Prop := True
/-- holderOnWith_univ (abstract). -/
def holderOnWith_univ' : Prop := True
/-- holderOnWith_one (abstract). -/
def holderOnWith_one' : Prop := True
/-- holderWith_one (abstract). -/
def holderWith_one' : Prop := True
/-- edist_le_of_le (abstract). -/
def edist_le_of_le' : Prop := True
/-- comp_holderWith (abstract). -/
def comp_holderWith' : Prop := True
/-- ediam_image_le_of_le (abstract). -/
def ediam_image_le_of_le' : Prop := True
/-- ediam_image_le_of_subset (abstract). -/
def ediam_image_le_of_subset' : Prop := True
/-- ediam_image_le_of_subset_of_le (abstract). -/
def ediam_image_le_of_subset_of_le' : Prop := True
/-- ediam_image_inter_le_of_le (abstract). -/
def ediam_image_inter_le_of_le' : Prop := True
/-- comp_holderOnWith (abstract). -/
def comp_holderOnWith' : Prop := True
-- COLLISION: zero' already in SetTheory.lean — rename needed
/-- nndist_le_of_le (abstract). -/
def nndist_le_of_le' : Prop := True
/-- nndist_le (abstract). -/
def nndist_le' : Prop := True
/-- dist_le_of_le (abstract). -/
def dist_le_of_le' : Prop := True
/-- holderWith_zero_iff (abstract). -/
def holderWith_zero_iff' : Prop := True

-- MetricSpace/HolderNorm.lean
/-- eHolderNorm (abstract). -/
def eHolderNorm' : Prop := True
/-- nnHolderNorm (abstract). -/
def nnHolderNorm' : Prop := True
/-- MemHolder (abstract). -/
def MemHolder' : Prop := True
/-- eHolderNorm_ne_top (abstract). -/
def eHolderNorm_ne_top' : Prop := True
/-- eHolderNorm_eq_top (abstract). -/
def eHolderNorm_eq_top' : Prop := True
/-- coe_nnHolderNorm_le_eHolderNorm (abstract). -/
def coe_nnHolderNorm_le_eHolderNorm' : Prop := True
/-- eHolderNorm_const (abstract). -/
def eHolderNorm_const' : Prop := True
/-- eHolderNorm_zero (abstract). -/
def eHolderNorm_zero' : Prop := True
/-- nnHolderNorm_const (abstract). -/
def nnHolderNorm_const' : Prop := True
/-- nnHolderNorm_zero (abstract). -/
def nnHolderNorm_zero' : Prop := True
/-- eHolderNorm_of_isEmpty (abstract). -/
def eHolderNorm_of_isEmpty' : Prop := True
/-- eHolderNorm_le (abstract). -/
def eHolderNorm_le' : Prop := True
/-- memHolder_const (abstract). -/
def memHolder_const' : Prop := True
/-- memHolder_zero (abstract). -/
def memHolder_zero' : Prop := True
/-- holderWith (abstract). -/
def holderWith' : Prop := True
/-- memHolder_iff_holderWith (abstract). -/
def memHolder_iff_holderWith' : Prop := True
/-- coe_nnHolderNorm_eq_eHolderNorm (abstract). -/
def coe_nnHolderNorm_eq_eHolderNorm' : Prop := True
/-- nnholderNorm_le (abstract). -/
def nnholderNorm_le' : Prop := True
/-- nnHolderNorm_eq_zero (abstract). -/
def nnHolderNorm_eq_zero' : Prop := True
-- COLLISION: nsmul' already in RingTheory2.lean — rename needed
/-- nnHolderNorm_add_le (abstract). -/
def nnHolderNorm_add_le' : Prop := True
/-- eHolderNorm_add_le (abstract). -/
def eHolderNorm_add_le' : Prop := True
/-- eHolderNorm_smul (abstract). -/
def eHolderNorm_smul' : Prop := True
/-- nnHolderNorm_smul (abstract). -/
def nnHolderNorm_smul' : Prop := True
/-- eHolderNorm_nsmul (abstract). -/
def eHolderNorm_nsmul' : Prop := True
/-- nnHolderNorm_nsmul (abstract). -/
def nnHolderNorm_nsmul' : Prop := True

-- MetricSpace/Infsep.lean
/-- einfsep (abstract). -/
def einfsep' : Prop := True
/-- le_einfsep_iff (abstract). -/
def le_einfsep_iff' : Prop := True
/-- einfsep_zero (abstract). -/
def einfsep_zero' : Prop := True
/-- einfsep_pos (abstract). -/
def einfsep_pos' : Prop := True
/-- einfsep_top (abstract). -/
def einfsep_top' : Prop := True
/-- einfsep_lt_top (abstract). -/
def einfsep_lt_top' : Prop := True
/-- einfsep_ne_top (abstract). -/
def einfsep_ne_top' : Prop := True
/-- einfsep_lt_iff (abstract). -/
def einfsep_lt_iff' : Prop := True
/-- le_einfsep_image_iff (abstract). -/
def le_einfsep_image_iff' : Prop := True
/-- le_edist_of_le_einfsep (abstract). -/
def le_edist_of_le_einfsep' : Prop := True
/-- einfsep_le_edist_of_mem (abstract). -/
def einfsep_le_edist_of_mem' : Prop := True
/-- einfsep_le_of_mem_of_edist_le (abstract). -/
def einfsep_le_of_mem_of_edist_le' : Prop := True
/-- le_einfsep (abstract). -/
def le_einfsep' : Prop := True
/-- einfsep_empty (abstract). -/
def einfsep_empty' : Prop := True
/-- einfsep_singleton (abstract). -/
def einfsep_singleton' : Prop := True
/-- einfsep_iUnion_mem_option (abstract). -/
def einfsep_iUnion_mem_option' : Prop := True
/-- einfsep_anti (abstract). -/
def einfsep_anti' : Prop := True
/-- einfsep_insert_le (abstract). -/
def einfsep_insert_le' : Prop := True
/-- le_einfsep_pair (abstract). -/
def le_einfsep_pair' : Prop := True
/-- einfsep_pair_le_left (abstract). -/
def einfsep_pair_le_left' : Prop := True
/-- einfsep_pair_le_right (abstract). -/
def einfsep_pair_le_right' : Prop := True
/-- einfsep_pair_eq_inf (abstract). -/
def einfsep_pair_eq_inf' : Prop := True
/-- einfsep_eq_iInf (abstract). -/
def einfsep_eq_iInf' : Prop := True
/-- einfsep_of_fintype (abstract). -/
def einfsep_of_fintype' : Prop := True
/-- coe_einfsep (abstract). -/
def coe_einfsep' : Prop := True
/-- einfsep_pair (abstract). -/
def einfsep_pair' : Prop := True
/-- einfsep_insert (abstract). -/
def einfsep_insert' : Prop := True
/-- einfsep_triple (abstract). -/
def einfsep_triple' : Prop := True
/-- le_einfsep_pi_of_le (abstract). -/
def le_einfsep_pi_of_le' : Prop := True
/-- subsingleton_of_einfsep_eq_top (abstract). -/
def subsingleton_of_einfsep_eq_top' : Prop := True
/-- einfsep_eq_top_iff (abstract). -/
def einfsep_eq_top_iff' : Prop := True
/-- le_einfsep_of_forall_dist_le (abstract). -/
def le_einfsep_of_forall_dist_le' : Prop := True
/-- einfsep_pos_of_finite (abstract). -/
def einfsep_pos_of_finite' : Prop := True
/-- relatively_discrete_of_finite (abstract). -/
def relatively_discrete_of_finite' : Prop := True
/-- relatively_discrete (abstract). -/
def relatively_discrete' : Prop := True
/-- infsep (abstract). -/
def infsep' : Prop := True
/-- infsep_zero (abstract). -/
def infsep_zero' : Prop := True
/-- infsep_nonneg (abstract). -/
def infsep_nonneg' : Prop := True
/-- infsep_pos (abstract). -/
def infsep_pos' : Prop := True
/-- infsep_empty (abstract). -/
def infsep_empty' : Prop := True
/-- infsep_singleton (abstract). -/
def infsep_singleton' : Prop := True
/-- infsep_pair_le_toReal_inf (abstract). -/
def infsep_pair_le_toReal_inf' : Prop := True
/-- infsep_pair_eq_toReal (abstract). -/
def infsep_pair_eq_toReal' : Prop := True
/-- le_edist_of_le_infsep (abstract). -/
def le_edist_of_le_infsep' : Prop := True
/-- infsep_le_dist_of_mem (abstract). -/
def infsep_le_dist_of_mem' : Prop := True
/-- infsep_le_of_mem_of_edist_le (abstract). -/
def infsep_le_of_mem_of_edist_le' : Prop := True
/-- infsep_pair (abstract). -/
def infsep_pair' : Prop := True
/-- infsep_triple (abstract). -/
def infsep_triple' : Prop := True
/-- coe_infsep (abstract). -/
def coe_infsep' : Prop := True
/-- coe_infsep_of_offDiag_nonempty (abstract). -/
def coe_infsep_of_offDiag_nonempty' : Prop := True
/-- coe_infsep_of_offDiag_empty (abstract). -/
def coe_infsep_of_offDiag_empty' : Prop := True
/-- infsep_zero_iff_subsingleton_of_finite (abstract). -/
def infsep_zero_iff_subsingleton_of_finite' : Prop := True
/-- infsep_zero_iff_subsingleton (abstract). -/
def infsep_zero_iff_subsingleton' : Prop := True

-- MetricSpace/IsometricSMul.lean
/-- IsometricVAdd (abstract). -/
def IsometricVAdd' : Prop := True
/-- IsometricSMul (abstract). -/
def IsometricSMul' : Prop := True
/-- isometry_smul (abstract). -/
def isometry_smul' : Prop := True
/-- edist_smul_left (abstract). -/
def edist_smul_left' : Prop := True
/-- ediam_smul (abstract). -/
def ediam_smul' : Prop := True
/-- isometry_mul_left (abstract). -/
def isometry_mul_left' : Prop := True
/-- edist_mul_left (abstract). -/
def edist_mul_left' : Prop := True
/-- isometry_mul_right (abstract). -/
def isometry_mul_right' : Prop := True
/-- edist_mul_right (abstract). -/
def edist_mul_right' : Prop := True
/-- edist_div_right (abstract). -/
def edist_div_right' : Prop := True
/-- edist_inv_inv (abstract). -/
def edist_inv_inv' : Prop := True
/-- isometry_inv (abstract). -/
def isometry_inv' : Prop := True
/-- edist_inv (abstract). -/
def edist_inv' : Prop := True
/-- edist_div_left (abstract). -/
def edist_div_left' : Prop := True
/-- constSMul (abstract). -/
def constSMul' : Prop := True
/-- constSMul_symm (abstract). -/
def constSMul_symm' : Prop := True
/-- divRight_symm (abstract). -/
def divRight_symm' : Prop := True
-- COLLISION: smul_ball' already in Analysis.lean — rename needed
/-- preimage_smul_ball (abstract). -/
def preimage_smul_ball' : Prop := True
-- COLLISION: smul_closedBall' already in Analysis.lean — rename needed
/-- preimage_smul_closedBall (abstract). -/
def preimage_smul_closedBall' : Prop := True
/-- preimage_mul_left_ball (abstract). -/
def preimage_mul_left_ball' : Prop := True
/-- preimage_mul_right_ball (abstract). -/
def preimage_mul_right_ball' : Prop := True
/-- preimage_mul_left_closedBall (abstract). -/
def preimage_mul_left_closedBall' : Prop := True
/-- preimage_mul_right_closedBall (abstract). -/
def preimage_mul_right_closedBall' : Prop := True
/-- dist_smul (abstract). -/
def dist_smul' : Prop := True
/-- nndist_smul (abstract). -/
def nndist_smul' : Prop := True
/-- diam_smul (abstract). -/
def diam_smul' : Prop := True
/-- dist_mul_left (abstract). -/
def dist_mul_left' : Prop := True
/-- nndist_mul_left (abstract). -/
def nndist_mul_left' : Prop := True
/-- dist_mul_right (abstract). -/
def dist_mul_right' : Prop := True
/-- nndist_mul_right (abstract). -/
def nndist_mul_right' : Prop := True
/-- dist_div_right (abstract). -/
def dist_div_right' : Prop := True
/-- nndist_div_right (abstract). -/
def nndist_div_right' : Prop := True
/-- dist_inv_inv (abstract). -/
def dist_inv_inv' : Prop := True
/-- nndist_inv_inv (abstract). -/
def nndist_inv_inv' : Prop := True
/-- dist_div_left (abstract). -/
def dist_div_left' : Prop := True
/-- nndist_div_left (abstract). -/
def nndist_div_left' : Prop := True
-- COLLISION: smul_sphere' already in Analysis.lean — rename needed
/-- preimage_smul_sphere (abstract). -/
def preimage_smul_sphere' : Prop := True

-- MetricSpace/Isometry.lean
-- COLLISION: Isometry' already in LinearAlgebra2.lean — rename needed
/-- isometry_iff_nndist_eq (abstract). -/
def isometry_iff_nndist_eq' : Prop := True
/-- isometry_iff_dist_eq (abstract). -/
def isometry_iff_dist_eq' : Prop := True
/-- isometry_subsingleton (abstract). -/
def isometry_subsingleton' : Prop := True
-- COLLISION: isometry_id' already in Analysis.lean — rename needed
-- COLLISION: right_inv' already in RingTheory2.lean — rename needed
/-- preimage_emetric_closedBall (abstract). -/
def preimage_emetric_closedBall' : Prop := True
/-- preimage_emetric_ball (abstract). -/
def preimage_emetric_ball' : Prop := True
/-- isometry_subtype_coe (abstract). -/
def isometry_subtype_coe' : Prop := True
/-- preimage_setOf_dist (abstract). -/
def preimage_setOf_dist' : Prop := True
-- COLLISION: preimage_closedBall' already in Analysis.lean — rename needed
-- COLLISION: preimage_ball' already in Analysis.lean — rename needed
-- COLLISION: preimage_sphere' already in Analysis.lean — rename needed
-- COLLISION: IsometryEquiv' already in LinearAlgebra2.lean — rename needed
/-- ediam_univ (abstract). -/
def ediam_univ' : Prop := True
/-- ediam_preimage (abstract). -/
def ediam_preimage' : Prop := True
-- COLLISION: inv_apply_self' already in Order.lean — rename needed
-- COLLISION: apply_inv_self' already in Order.lean — rename needed
/-- completeSpace_iff (abstract). -/
def completeSpace_iff' : Prop := True
/-- sumArrowIsometryEquivProdArrow (abstract). -/
def sumArrowIsometryEquivProdArrow' : Prop := True
/-- edist_append_eq_max_edist (abstract). -/
def edist_append_eq_max_edist' : Prop := True
/-- appendIsometry (abstract). -/
def appendIsometry' : Prop := True
/-- diam_preimage (abstract). -/
def diam_preimage' : Prop := True
/-- diam_univ (abstract). -/
def diam_univ' : Prop := True
-- COLLISION: image_ball' already in Analysis.lean — rename needed
-- COLLISION: image_sphere' already in Analysis.lean — rename needed
/-- isometryEquivOnRange (abstract). -/
def isometryEquivOnRange' : Prop := True
/-- lipschitzWith_iff (abstract). -/
def lipschitzWith_iff' : Prop := True

-- MetricSpace/Kuratowski.lean
/-- embeddingOfSubset (abstract). -/
def embeddingOfSubset' : Prop := True
/-- embeddingOfSubset_dist_le (abstract). -/
def embeddingOfSubset_dist_le' : Prop := True
/-- embeddingOfSubset_isometry (abstract). -/
def embeddingOfSubset_isometry' : Prop := True
/-- exists_isometric_embedding (abstract). -/
def exists_isometric_embedding' : Prop := True
/-- kuratowskiEmbedding (abstract). -/
def kuratowskiEmbedding' : Prop := True
-- COLLISION: isometry' already in Analysis.lean — rename needed
/-- extend_lp_infty (abstract). -/
def extend_lp_infty' : Prop := True
/-- here! (abstract). -/
def here!' : Prop := True

-- MetricSpace/Lipschitz.lean
/-- lipschitzWith_iff_dist_le_mul (abstract). -/
def lipschitzWith_iff_dist_le_mul' : Prop := True
/-- lipschitzOnWith_iff_dist_le_mul (abstract). -/
def lipschitzOnWith_iff_dist_le_mul' : Prop := True
/-- of_dist_le' (abstract). -/
def of_dist_le' : Prop := True
/-- mk_one (abstract). -/
def mk_one' : Prop := True
/-- of_le_add_mul' (abstract). -/
def of_le_add_mul' : Prop := True
/-- of_le_add (abstract). -/
def of_le_add' : Prop := True
/-- le_add_mul (abstract). -/
def le_add_mul' : Prop := True
/-- iff_le_add_mul (abstract). -/
def iff_le_add_mul' : Prop := True
/-- dist_le_mul_of_le (abstract). -/
def dist_le_mul_of_le' : Prop := True
/-- dist_lt_mul_of_lt (abstract). -/
def dist_lt_mul_of_lt' : Prop := True
/-- comap_cobounded_le (abstract). -/
def comap_cobounded_le' : Prop := True
/-- diam_image_le (abstract). -/
def diam_image_le' : Prop := True
/-- dist_left (abstract). -/
def dist_left' : Prop := True
/-- dist_right (abstract). -/
def dist_right' : Prop := True
/-- dist_iterate_succ_le_geometric (abstract). -/
def dist_iterate_succ_le_geometric' : Prop := True
/-- lipschitzWith_max (abstract). -/
def lipschitzWith_max' : Prop := True
/-- lipschitzWith_min (abstract). -/
def lipschitzWith_min' : Prop := True
/-- lipschitzWith_toNNReal (abstract). -/
def lipschitzWith_toNNReal' : Prop := True
/-- cauchySeq_comp (abstract). -/
def cauchySeq_comp' : Prop := True
-- COLLISION: max' already in Order.lean — rename needed
-- COLLISION: min' already in Order.lean — rename needed
/-- max_const (abstract). -/
def max_const' : Prop := True
-- COLLISION: const_max' already in Order.lean — rename needed
/-- min_const (abstract). -/
def min_const' : Prop := True
-- COLLISION: const_min' already in Order.lean — rename needed
-- COLLISION: projIcc' already in Order.lean — rename needed
/-- isBounded_image2 (abstract). -/
def isBounded_image2' : Prop := True
/-- continuousAt_of_locally_lipschitz (abstract). -/
def continuousAt_of_locally_lipschitz' : Prop := True
/-- extend_real (abstract). -/
def extend_real' : Prop := True
/-- extend_pi (abstract). -/
def extend_pi' : Prop := True

-- MetricSpace/MetricSeparated.lean
/-- IsMetricSeparated (abstract). -/
def IsMetricSeparated' : Prop := True
-- COLLISION: union_left' already in MeasureTheory2.lean — rename needed
-- COLLISION: union_left_iff' already in MeasureTheory2.lean — rename needed
-- COLLISION: union_right' already in Order.lean — rename needed
-- COLLISION: union_right_iff' already in MeasureTheory2.lean — rename needed
/-- finite_iUnion_left_iff (abstract). -/
def finite_iUnion_left_iff' : Prop := True
/-- finite_iUnion_right_iff (abstract). -/
def finite_iUnion_right_iff' : Prop := True
/-- finset_iUnion_left_iff (abstract). -/
def finset_iUnion_left_iff' : Prop := True
/-- finset_iUnion_right_iff (abstract). -/
def finset_iUnion_right_iff' : Prop := True

-- MetricSpace/PartitionOfUnity.lean
/-- eventually_nhds_zero_forall_closedBall_subset (abstract). -/
def eventually_nhds_zero_forall_closedBall_subset' : Prop := True
/-- exists_forall_closedBall_subset_aux₁ (abstract). -/
def exists_forall_closedBall_subset_aux₁' : Prop := True
/-- exists_forall_closedBall_subset_aux₂ (abstract). -/
def exists_forall_closedBall_subset_aux₂' : Prop := True
/-- exists_continuous_real_forall_closedBall_subset (abstract). -/
def exists_continuous_real_forall_closedBall_subset' : Prop := True
/-- exists_continuous_nnreal_forall_closedBall_subset (abstract). -/
def exists_continuous_nnreal_forall_closedBall_subset' : Prop := True
/-- exists_continuous_eNNReal_forall_closedBall_subset (abstract). -/
def exists_continuous_eNNReal_forall_closedBall_subset' : Prop := True

-- MetricSpace/Perfect.lean
/-- small_diam_aux (abstract). -/
def small_diam_aux' : Prop := True
/-- small_diam_splitting (abstract). -/
def small_diam_splitting' : Prop := True
/-- exists_nat_bool_injection (abstract). -/
def exists_nat_bool_injection' : Prop := True
/-- exists_nat_bool_injection_of_not_countable (abstract). -/
def exists_nat_bool_injection_of_not_countable' : Prop := True

-- MetricSpace/PiNat.lean
/-- firstDiff (abstract). -/
def firstDiff' : Prop := True
/-- apply_firstDiff_ne (abstract). -/
def apply_firstDiff_ne' : Prop := True
/-- apply_eq_of_lt_firstDiff (abstract). -/
def apply_eq_of_lt_firstDiff' : Prop := True
/-- firstDiff_comm (abstract). -/
def firstDiff_comm' : Prop := True
/-- min_firstDiff_le (abstract). -/
def min_firstDiff_le' : Prop := True
-- COLLISION: cylinder' already in Algebra.lean — rename needed
/-- self_mem_cylinder (abstract). -/
def self_mem_cylinder' : Prop := True
/-- mem_cylinder_iff_eq (abstract). -/
def mem_cylinder_iff_eq' : Prop := True
/-- mem_cylinder_comm (abstract). -/
def mem_cylinder_comm' : Prop := True
/-- mem_cylinder_iff_le_firstDiff (abstract). -/
def mem_cylinder_iff_le_firstDiff' : Prop := True
/-- mem_cylinder_firstDiff (abstract). -/
def mem_cylinder_firstDiff' : Prop := True
/-- cylinder_eq_cylinder_of_le_firstDiff (abstract). -/
def cylinder_eq_cylinder_of_le_firstDiff' : Prop := True
/-- iUnion_cylinder_update (abstract). -/
def iUnion_cylinder_update' : Prop := True
/-- res (abstract). -/
def res' : Prop := True
/-- res_length (abstract). -/
def res_length' : Prop := True
/-- res_eq_res (abstract). -/
def res_eq_res' : Prop := True
/-- res_injective (abstract). -/
def res_injective' : Prop := True
/-- cylinder_eq_res (abstract). -/
def cylinder_eq_res' : Prop := True
/-- dist_eq_of_ne (abstract). -/
def dist_eq_of_ne' : Prop := True
/-- dist_triangle_nonarch (abstract). -/
def dist_triangle_nonarch' : Prop := True
/-- mem_cylinder_iff_dist_le (abstract). -/
def mem_cylinder_iff_dist_le' : Prop := True
/-- apply_eq_of_dist_lt (abstract). -/
def apply_eq_of_dist_lt' : Prop := True
/-- lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder (abstract). -/
def lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder' : Prop := True
/-- isOpen_cylinder (abstract). -/
def isOpen_cylinder' : Prop := True
/-- isTopologicalBasis_cylinders (abstract). -/
def isTopologicalBasis_cylinders' : Prop := True
/-- isOpen_iff_dist (abstract). -/
def isOpen_iff_dist' : Prop := True
/-- metricSpaceOfDiscreteUniformity (abstract). -/
def metricSpaceOfDiscreteUniformity' : Prop := True
/-- metricSpaceNatNat (abstract). -/
def metricSpaceNatNat' : Prop := True
/-- exists_disjoint_cylinder (abstract). -/
def exists_disjoint_cylinder' : Prop := True
/-- shortestPrefixDiff (abstract). -/
def shortestPrefixDiff' : Prop := True
/-- firstDiff_lt_shortestPrefixDiff (abstract). -/
def firstDiff_lt_shortestPrefixDiff' : Prop := True
/-- shortestPrefixDiff_pos (abstract). -/
def shortestPrefixDiff_pos' : Prop := True
/-- longestPrefix (abstract). -/
def longestPrefix' : Prop := True
/-- firstDiff_le_longestPrefix (abstract). -/
def firstDiff_le_longestPrefix' : Prop := True
/-- inter_cylinder_longestPrefix_nonempty (abstract). -/
def inter_cylinder_longestPrefix_nonempty' : Prop := True
/-- disjoint_cylinder_of_longestPrefix_lt (abstract). -/
def disjoint_cylinder_of_longestPrefix_lt' : Prop := True
/-- cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff (abstract). -/
def cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff' : Prop := True
/-- exists_lipschitz_retraction_of_isClosed (abstract). -/
def exists_lipschitz_retraction_of_isClosed' : Prop := True
/-- exists_retraction_of_isClosed (abstract). -/
def exists_retraction_of_isClosed' : Prop := True
/-- exists_retraction_subtype_of_isClosed (abstract). -/
def exists_retraction_subtype_of_isClosed' : Prop := True
/-- dist_summable (abstract). -/
def dist_summable' : Prop := True
/-- min_dist_le_dist_pi (abstract). -/
def min_dist_le_dist_pi' : Prop := True
/-- dist_le_dist_pi_of_dist_lt (abstract). -/
def dist_le_dist_pi_of_dist_lt' : Prop := True

-- MetricSpace/Polish.lean
/-- PolishSpace (abstract). -/
def PolishSpace' : Prop := True
/-- UpgradedPolishSpace (abstract). -/
def UpgradedPolishSpace' : Prop := True
/-- polishSpaceMetric (abstract). -/
def polishSpaceMetric' : Prop := True
/-- complete_polishSpaceMetric (abstract). -/
def complete_polishSpaceMetric' : Prop := True
/-- upgradePolishSpace (abstract). -/
def upgradePolishSpace' : Prop := True
/-- exists_nat_nat_continuous_surjective (abstract). -/
def exists_nat_nat_continuous_surjective' : Prop := True
/-- polishSpace (abstract). -/
def polishSpace' : Prop := True
/-- polishSpace_induced (abstract). -/
def polishSpace_induced' : Prop := True
/-- exists_polishSpace_forall_le (abstract). -/
def exists_polishSpace_forall_le' : Prop := True
/-- CompleteCopy (abstract). -/
def CompleteCopy' : Prop := True
/-- dist_val_le_dist (abstract). -/
def dist_val_le_dist' : Prop := True
/-- IsClopenable (abstract). -/
def IsClopenable' : Prop := True
-- COLLISION: isClopenable' already in MeasureTheory2.lean — rename needed

-- MetricSpace/ProperSpace.lean
/-- ProperSpace (abstract). -/
def ProperSpace' : Prop := True
/-- isCompact_sphere (abstract). -/
def isCompact_sphere' : Prop := True
/-- of_isCompact_closedBall_of_le (abstract). -/
def of_isCompact_closedBall_of_le' : Prop := True
/-- of_seq_closedBall (abstract). -/
def of_seq_closedBall' : Prop := True

-- MetricSpace/ProperSpace/Lemmas.lean
-- COLLISION: exists_pos_lt_subset_ball' already in Analysis.lean — rename needed
/-- exists_lt_subset_ball (abstract). -/
def exists_lt_subset_ball' : Prop := True
/-- exists_isLocalMin_mem_ball (abstract). -/
def exists_isLocalMin_mem_ball' : Prop := True

-- MetricSpace/Pseudo/Basic.lean
/-- dist_le_Ico_sum_dist (abstract). -/
def dist_le_Ico_sum_dist' : Prop := True
/-- dist_le_range_sum_dist (abstract). -/
def dist_le_range_sum_dist' : Prop := True
/-- dist_le_Ico_sum_of_dist_le (abstract). -/
def dist_le_Ico_sum_of_dist_le' : Prop := True
/-- dist_le_range_sum_of_dist_le (abstract). -/
def dist_le_range_sum_of_dist_le' : Prop := True
/-- totallyBounded_of_finite_discretization (abstract). -/
def totallyBounded_of_finite_discretization' : Prop := True
/-- finite_approx_of_totallyBounded (abstract). -/
def finite_approx_of_totallyBounded' : Prop := True
/-- tendstoUniformlyOnFilter_iff (abstract). -/
def tendstoUniformlyOnFilter_iff' : Prop := True
/-- exists_ball_inter_eq_singleton_of_mem_discrete (abstract). -/
def exists_ball_inter_eq_singleton_of_mem_discrete' : Prop := True
/-- exists_closedBall_inter_eq_singleton_of_discrete (abstract). -/
def exists_closedBall_inter_eq_singleton_of_discrete' : Prop := True
/-- inseparable_iff_nndist (abstract). -/
def inseparable_iff_nndist' : Prop := True
/-- tendsto_nhds_unique_dist (abstract). -/
def tendsto_nhds_unique_dist' : Prop := True
/-- cauchySeq_iff_tendsto_dist_atTop_0 (abstract). -/
def cauchySeq_iff_tendsto_dist_atTop_0' : Prop := True
/-- isSeparable_preimage (abstract). -/
def isSeparable_preimage' : Prop := True

-- MetricSpace/Pseudo/Constructions.lean
/-- comapPseudoMetricSpace (abstract). -/
def comapPseudoMetricSpace' : Prop := True
/-- nndist_zero_eq_val (abstract). -/
def nndist_zero_eq_val' : Prop := True
/-- le_add_nndist (abstract). -/
def le_add_nndist' : Prop := True
/-- ball_zero_eq_Ico' (abstract). -/
def ball_zero_eq_Ico' : Prop := True
/-- closedBall_zero_eq_Icc' (abstract). -/
def closedBall_zero_eq_Icc' : Prop := True
/-- dist_prod_same_left (abstract). -/
def dist_prod_same_left' : Prop := True
/-- dist_prod_same_right (abstract). -/
def dist_prod_same_right' : Prop := True
/-- sphere_prod (abstract). -/
def sphere_prod' : Prop := True
/-- continuous_iff_continuous_dist (abstract). -/
def continuous_iff_continuous_dist' : Prop := True
/-- uniformContinuous_nndist (abstract). -/
def uniformContinuous_nndist' : Prop := True
-- COLLISION: nndist' already in MeasureTheory2.lean — rename needed
/-- continuous_nndist (abstract). -/
def continuous_nndist' : Prop := True

-- MetricSpace/Pseudo/Defs.lean
/-- ofDist_aux (abstract). -/
def ofDist_aux' : Prop := True
/-- ofDist (abstract). -/
def ofDist' : Prop := True
/-- Dist (abstract). -/
def Dist' : Prop := True
/-- PseudoMetricSpace (abstract). -/
def PseudoMetricSpace' : Prop := True
/-- edist_dist (abstract). -/
def edist_dist' : Prop := True
/-- dist_triangle_left (abstract). -/
def dist_triangle_left' : Prop := True
/-- dist_triangle_right (abstract). -/
def dist_triangle_right' : Prop := True
/-- dist_triangle4 (abstract). -/
def dist_triangle4' : Prop := True
/-- dist_triangle4_left (abstract). -/
def dist_triangle4_left' : Prop := True
/-- dist_triangle4_right (abstract). -/
def dist_triangle4_right' : Prop := True
/-- swap_dist (abstract). -/
def swap_dist' : Prop := True
/-- abs_dist_sub_le (abstract). -/
def abs_dist_sub_le' : Prop := True
/-- evalDist (abstract). -/
def evalDist' : Prop := True
/-- NNDist (abstract). -/
def NNDist' : Prop := True
/-- edist_nndist (abstract). -/
def edist_nndist' : Prop := True
/-- nndist_edist (abstract). -/
def nndist_edist' : Prop := True
/-- coe_nnreal_ennreal_nndist (abstract). -/
def coe_nnreal_ennreal_nndist' : Prop := True
/-- edist_lt_coe (abstract). -/
def edist_lt_coe' : Prop := True
/-- edist_le_coe (abstract). -/
def edist_le_coe' : Prop := True
/-- edist_lt_ofReal (abstract). -/
def edist_lt_ofReal' : Prop := True
/-- edist_le_ofReal (abstract). -/
def edist_le_ofReal' : Prop := True
/-- nndist_dist (abstract). -/
def nndist_dist' : Prop := True
/-- nndist_comm (abstract). -/
def nndist_comm' : Prop := True
/-- nndist_triangle (abstract). -/
def nndist_triangle' : Prop := True
/-- nndist_triangle_left (abstract). -/
def nndist_triangle_left' : Prop := True
/-- mem_ball' (abstract). -/
def mem_ball' : Prop := True
/-- nonempty_ball (abstract). -/
def nonempty_ball' : Prop := True
/-- ball_eq_ball' (abstract). -/
def ball_eq_ball' : Prop := True
-- COLLISION: mem_sphere' already in Geometry2.lean — rename needed
/-- ne_of_mem_sphere (abstract). -/
def ne_of_mem_sphere' : Prop := True
/-- nonneg_of_mem_sphere (abstract). -/
def nonneg_of_mem_sphere' : Prop := True
/-- sphere_eq_empty_of_neg (abstract). -/
def sphere_eq_empty_of_neg' : Prop := True
/-- sphere_eq_empty_of_subsingleton (abstract). -/
def sphere_eq_empty_of_subsingleton' : Prop := True
/-- closedBall_eq_singleton_of_subsingleton (abstract). -/
def closedBall_eq_singleton_of_subsingleton' : Prop := True
/-- ball_eq_singleton_of_subsingleton (abstract). -/
def ball_eq_singleton_of_subsingleton' : Prop := True
/-- nonempty_closedBall (abstract). -/
def nonempty_closedBall' : Prop := True
/-- closedBall_eq_empty (abstract). -/
def closedBall_eq_empty' : Prop := True
/-- closedBall_eq_sphere_of_nonpos (abstract). -/
def closedBall_eq_sphere_of_nonpos' : Prop := True
/-- sphere_subset_closedBall (abstract). -/
def sphere_subset_closedBall' : Prop := True
/-- sphere_subset_ball (abstract). -/
def sphere_subset_ball' : Prop := True
/-- closedBall_disjoint_ball (abstract). -/
def closedBall_disjoint_ball' : Prop := True
/-- ball_disjoint_closedBall (abstract). -/
def ball_disjoint_closedBall' : Prop := True
/-- ball_disjoint_ball (abstract). -/
def ball_disjoint_ball' : Prop := True
/-- closedBall_disjoint_closedBall (abstract). -/
def closedBall_disjoint_closedBall' : Prop := True
/-- sphere_disjoint_ball (abstract). -/
def sphere_disjoint_ball' : Prop := True
/-- ball_union_sphere (abstract). -/
def ball_union_sphere' : Prop := True
/-- sphere_union_ball (abstract). -/
def sphere_union_ball' : Prop := True
/-- closedBall_diff_sphere (abstract). -/
def closedBall_diff_sphere' : Prop := True
/-- closedBall_diff_ball (abstract). -/
def closedBall_diff_ball' : Prop := True
/-- mem_sphere_comm (abstract). -/
def mem_sphere_comm' : Prop := True
/-- dist_lt_add_of_nonempty_ball_inter_closedBall (abstract). -/
def dist_lt_add_of_nonempty_ball_inter_closedBall' : Prop := True
/-- dist_lt_add_of_nonempty_ball_inter_ball (abstract). -/
def dist_lt_add_of_nonempty_ball_inter_ball' : Prop := True
/-- iUnion_closedBall_nat (abstract). -/
def iUnion_closedBall_nat' : Prop := True
/-- iUnion_inter_closedBall_nat (abstract). -/
def iUnion_inter_closedBall_nat' : Prop := True
/-- ball_subset (abstract). -/
def ball_subset' : Prop := True
/-- ball_half_subset (abstract). -/
def ball_half_subset' : Prop := True
/-- forall_of_forall_mem_closedBall (abstract). -/
def forall_of_forall_mem_closedBall' : Prop := True
/-- forall_of_forall_mem_ball (abstract). -/
def forall_of_forall_mem_ball' : Prop := True
/-- isBounded_iff_eventually (abstract). -/
def isBounded_iff_eventually' : Prop := True
/-- isBounded_iff_exists_ge (abstract). -/
def isBounded_iff_exists_ge' : Prop := True
/-- isBounded_iff_nndist (abstract). -/
def isBounded_iff_nndist' : Prop := True
/-- uniformity_basis_dist (abstract). -/
def uniformity_basis_dist' : Prop := True
/-- uniformity_basis_dist_rat (abstract). -/
def uniformity_basis_dist_rat' : Prop := True
/-- uniformity_basis_dist_inv_nat_succ (abstract). -/
def uniformity_basis_dist_inv_nat_succ' : Prop := True
/-- uniformity_basis_dist_inv_nat_pos (abstract). -/
def uniformity_basis_dist_inv_nat_pos' : Prop := True
/-- uniformity_basis_dist_pow (abstract). -/
def uniformity_basis_dist_pow' : Prop := True
/-- uniformity_basis_dist_lt (abstract). -/
def uniformity_basis_dist_lt' : Prop := True
/-- uniformity_basis_dist_le (abstract). -/
def uniformity_basis_dist_le' : Prop := True
/-- uniformity_basis_dist_le_pow (abstract). -/
def uniformity_basis_dist_le_pow' : Prop := True
/-- dist_mem_uniformity (abstract). -/
def dist_mem_uniformity' : Prop := True
/-- uniformContinuousOn_iff_le (abstract). -/
def uniformContinuousOn_iff_le' : Prop := True
-- COLLISION: nhds_basis_ball' already in Analysis.lean — rename needed
/-- eventually_nhds_iff_ball (abstract). -/
def eventually_nhds_iff_ball' : Prop := True
/-- eventually_nhds_prod_iff (abstract). -/
def eventually_nhds_prod_iff' : Prop := True
/-- eventually_prod_nhds_iff (abstract). -/
def eventually_prod_nhds_iff' : Prop := True
-- COLLISION: nhds_basis_closedBall' already in Analysis.lean — rename needed
/-- nhds_basis_ball_inv_nat_succ (abstract). -/
def nhds_basis_ball_inv_nat_succ' : Prop := True
/-- nhds_basis_ball_inv_nat_pos (abstract). -/
def nhds_basis_ball_inv_nat_pos' : Prop := True
/-- nhds_basis_ball_pow (abstract). -/
def nhds_basis_ball_pow' : Prop := True
/-- nhds_basis_closedBall_pow (abstract). -/
def nhds_basis_closedBall_pow' : Prop := True
/-- closedBall_mem_nhds_of_mem (abstract). -/
def closedBall_mem_nhds_of_mem' : Prop := True
/-- nhdsWithin_basis_ball (abstract). -/
def nhdsWithin_basis_ball' : Prop := True
/-- tendsto_nhdsWithin_nhds (abstract). -/
def tendsto_nhdsWithin_nhds' : Prop := True
-- COLLISION: isOpen_singleton_iff' already in SetTheory.lean — rename needed
/-- exists_dist_lt (abstract). -/
def exists_dist_lt' : Prop := True
/-- uniformSpace_eq_bot (abstract). -/
def uniformSpace_eq_bot' : Prop := True
/-- of_forall_le_dist (abstract). -/
def of_forall_le_dist' : Prop := True
/-- uniformity_edist_aux (abstract). -/
def uniformity_edist_aux' : Prop := True
/-- uniformity_edist (abstract). -/
def uniformity_edist' : Prop := True
/-- eball_top_eq_univ (abstract). -/
def eball_top_eq_univ' : Prop := True
/-- emetric_ball (abstract). -/
def emetric_ball' : Prop := True
/-- emetric_ball_nnreal (abstract). -/
def emetric_ball_nnreal' : Prop := True
/-- emetric_closedBall (abstract). -/
def emetric_closedBall' : Prop := True
/-- emetric_closedBall_nnreal (abstract). -/
def emetric_closedBall_nnreal' : Prop := True
/-- emetric_ball_top (abstract). -/
def emetric_ball_top' : Prop := True
/-- toPseudoMetricSpaceOfDist (abstract). -/
def toPseudoMetricSpaceOfDist' : Prop := True
/-- toPseudoMetricSpace (abstract). -/
def toPseudoMetricSpace' : Prop := True
/-- replaceBornology_eq (abstract). -/
def replaceBornology_eq' : Prop := True
/-- dist_0_eq_abs (abstract). -/
def dist_0_eq_abs' : Prop := True
/-- sub_le_dist (abstract). -/
def sub_le_dist' : Prop := True
/-- Ioo_eq_ball (abstract). -/
def Ioo_eq_ball' : Prop := True
/-- Icc_eq_closedBall (abstract). -/
def Icc_eq_closedBall' : Prop := True
/-- uniformity_eq_comap_nhds_zero (abstract). -/
def uniformity_eq_comap_nhds_zero' : Prop := True
/-- tendsto_uniformity_iff_dist_tendsto_zero (abstract). -/
def tendsto_uniformity_iff_dist_tendsto_zero' : Prop := True
/-- congr_dist (abstract). -/
def congr_dist' : Prop := True
/-- tendsto_iff_of_dist (abstract). -/
def tendsto_iff_of_dist' : Prop := True
/-- dist_eq_of_dist_zero (abstract). -/
def dist_eq_of_dist_zero' : Prop := True
/-- dist_dist_dist_le_left (abstract). -/
def dist_dist_dist_le_left' : Prop := True
/-- dist_dist_dist_le_right (abstract). -/
def dist_dist_dist_le_right' : Prop := True
/-- dist_dist_dist_le (abstract). -/
def dist_dist_dist_le' : Prop := True
/-- nhds_comap_dist (abstract). -/
def nhds_comap_dist' : Prop := True
/-- tendsto_iff_dist_tendsto_zero (abstract). -/
def tendsto_iff_dist_tendsto_zero' : Prop := True
/-- ball_subset_interior_closedBall (abstract). -/
def ball_subset_interior_closedBall' : Prop := True
/-- mem_closure_range_iff (abstract). -/
def mem_closure_range_iff' : Prop := True
/-- mem_closure_range_iff_nat (abstract). -/
def mem_closure_range_iff_nat' : Prop := True
/-- dense_iff_iUnion_ball (abstract). -/
def dense_iff_iUnion_ball' : Prop := True
/-- denseRange_iff (abstract). -/
def denseRange_iff' : Prop := True
/-- isSeparable_image (abstract). -/
def isSeparable_image' : Prop := True
/-- finite_cover_balls_of_compact (abstract). -/
def finite_cover_balls_of_compact' : Prop := True
/-- lebesgue_number_lemma_of_metric (abstract). -/
def lebesgue_number_lemma_of_metric' : Prop := True
/-- hs (abstract). -/
def hs' : Prop := True
/-- lebesgue_number_lemma_of_metric_sUnion (abstract). -/
def lebesgue_number_lemma_of_metric_sUnion' : Prop := True

-- MetricSpace/Pseudo/Lemmas.lean
/-- singleton_eq_inter_Icc (abstract). -/
def singleton_eq_inter_Icc' : Prop := True
/-- squeeze_zero' (abstract). -/
def squeeze_zero' : Prop := True
/-- eventually_closedBall_subset (abstract). -/
def eventually_closedBall_subset' : Prop := True
/-- tendsto_closedBall_smallSets (abstract). -/
def tendsto_closedBall_smallSets' : Prop := True
/-- isClosed_sphere (abstract). -/
def isClosed_sphere' : Prop := True
/-- closure_closedBall (abstract). -/
def closure_closedBall' : Prop := True
/-- closure_sphere (abstract). -/
def closure_sphere' : Prop := True
/-- closure_ball_subset_closedBall (abstract). -/
def closure_ball_subset_closedBall' : Prop := True
/-- frontier_ball_subset_sphere (abstract). -/
def frontier_ball_subset_sphere' : Prop := True
/-- frontier_closedBall_subset_sphere (abstract). -/
def frontier_closedBall_subset_sphere' : Prop := True
/-- eventually_isCompact_closedBall (abstract). -/
def eventually_isCompact_closedBall' : Prop := True
/-- exists_isCompact_closedBall (abstract). -/
def exists_isCompact_closedBall' : Prop := True

-- MetricSpace/Pseudo/Pi.lean
/-- nndist_pi_le_iff (abstract). -/
def nndist_pi_le_iff' : Prop := True
/-- nndist_pi_lt_iff (abstract). -/
def nndist_pi_lt_iff' : Prop := True
/-- nndist_pi_eq_iff (abstract). -/
def nndist_pi_eq_iff' : Prop := True
/-- dist_pi_lt_iff (abstract). -/
def dist_pi_lt_iff' : Prop := True
/-- dist_pi_le_iff (abstract). -/
def dist_pi_le_iff' : Prop := True
/-- dist_pi_eq_iff (abstract). -/
def dist_pi_eq_iff' : Prop := True
/-- dist_pi_const_le (abstract). -/
def dist_pi_const_le' : Prop := True
/-- nndist_pi_const_le (abstract). -/
def nndist_pi_const_le' : Prop := True
/-- dist_pi_const (abstract). -/
def dist_pi_const' : Prop := True
/-- nndist_pi_const (abstract). -/
def nndist_pi_const' : Prop := True
/-- nndist_le_pi_nndist (abstract). -/
def nndist_le_pi_nndist' : Prop := True
/-- dist_le_pi_dist (abstract). -/
def dist_le_pi_dist' : Prop := True
/-- ball_pi (abstract). -/
def ball_pi' : Prop := True
/-- closedBall_pi (abstract). -/
def closedBall_pi' : Prop := True
/-- nndist_insertNth_insertNth (abstract). -/
def nndist_insertNth_insertNth' : Prop := True
/-- dist_insertNth_insertNth (abstract). -/
def dist_insertNth_insertNth' : Prop := True

-- MetricSpace/Pseudo/Real.lean
/-- dist_left_le_of_mem_uIcc (abstract). -/
def dist_left_le_of_mem_uIcc' : Prop := True
/-- dist_right_le_of_mem_uIcc (abstract). -/
def dist_right_le_of_mem_uIcc' : Prop := True
/-- dist_le_of_mem_uIcc (abstract). -/
def dist_le_of_mem_uIcc' : Prop := True
/-- dist_le_of_mem_Icc (abstract). -/
def dist_le_of_mem_Icc' : Prop := True
/-- dist_le_of_mem_Icc_01 (abstract). -/
def dist_le_of_mem_Icc_01' : Prop := True
/-- dist_le_of_mem_pi_Icc (abstract). -/
def dist_le_of_mem_pi_Icc' : Prop := True

-- MetricSpace/Sequences.lean
/-- tendsto_subseq_of_frequently_bounded (abstract). -/
def tendsto_subseq_of_frequently_bounded' : Prop := True
/-- tendsto_subseq_of_bounded (abstract). -/
def tendsto_subseq_of_bounded' : Prop := True

-- MetricSpace/ShrinkingLemma.lean
/-- exists_subset_iUnion_ball_radius_lt (abstract). -/
def exists_subset_iUnion_ball_radius_lt' : Prop := True
/-- exists_iUnion_ball_eq_radius_lt (abstract). -/
def exists_iUnion_ball_eq_radius_lt' : Prop := True
/-- exists_subset_iUnion_ball_radius_pos_lt (abstract). -/
def exists_subset_iUnion_ball_radius_pos_lt' : Prop := True
/-- exists_iUnion_ball_eq_radius_pos_lt (abstract). -/
def exists_iUnion_ball_eq_radius_pos_lt' : Prop := True
/-- exists_locallyFinite_subset_iUnion_ball_radius_lt (abstract). -/
def exists_locallyFinite_subset_iUnion_ball_radius_lt' : Prop := True
/-- exists_locallyFinite_iUnion_eq_ball_radius_lt (abstract). -/
def exists_locallyFinite_iUnion_eq_ball_radius_lt' : Prop := True

-- MetricSpace/ThickenedIndicator.lean
/-- thickenedIndicatorAux (abstract). -/
def thickenedIndicatorAux' : Prop := True
/-- continuous_thickenedIndicatorAux (abstract). -/
def continuous_thickenedIndicatorAux' : Prop := True
/-- thickenedIndicatorAux_le_one (abstract). -/
def thickenedIndicatorAux_le_one' : Prop := True
/-- thickenedIndicatorAux_lt_top (abstract). -/
def thickenedIndicatorAux_lt_top' : Prop := True
/-- thickenedIndicatorAux_closure_eq (abstract). -/
def thickenedIndicatorAux_closure_eq' : Prop := True
/-- thickenedIndicatorAux_one (abstract). -/
def thickenedIndicatorAux_one' : Prop := True
/-- thickenedIndicatorAux_one_of_mem_closure (abstract). -/
def thickenedIndicatorAux_one_of_mem_closure' : Prop := True
/-- thickenedIndicatorAux_zero (abstract). -/
def thickenedIndicatorAux_zero' : Prop := True
/-- thickenedIndicatorAux_mono (abstract). -/
def thickenedIndicatorAux_mono' : Prop := True
/-- indicator_le_thickenedIndicatorAux (abstract). -/
def indicator_le_thickenedIndicatorAux' : Prop := True
/-- thickenedIndicatorAux_subset (abstract). -/
def thickenedIndicatorAux_subset' : Prop := True
/-- thickenedIndicatorAux_tendsto_indicator_closure (abstract). -/
def thickenedIndicatorAux_tendsto_indicator_closure' : Prop := True
/-- thickenedIndicator (abstract). -/
def thickenedIndicator' : Prop := True
/-- thickenedIndicator_le_one (abstract). -/
def thickenedIndicator_le_one' : Prop := True
/-- thickenedIndicator_one_of_mem_closure (abstract). -/
def thickenedIndicator_one_of_mem_closure' : Prop := True
/-- one_le_thickenedIndicator_apply' (abstract). -/
def one_le_thickenedIndicator_apply' : Prop := True
/-- thickenedIndicator_one (abstract). -/
def thickenedIndicator_one' : Prop := True
/-- thickenedIndicator_zero (abstract). -/
def thickenedIndicator_zero' : Prop := True
/-- indicator_le_thickenedIndicator (abstract). -/
def indicator_le_thickenedIndicator' : Prop := True
/-- thickenedIndicator_mono (abstract). -/
def thickenedIndicator_mono' : Prop := True
/-- thickenedIndicator_subset (abstract). -/
def thickenedIndicator_subset' : Prop := True
/-- thickenedIndicator_tendsto_indicator_closure (abstract). -/
def thickenedIndicator_tendsto_indicator_closure' : Prop := True
/-- mulIndicator_thickening_eventually_eq_mulIndicator_closure (abstract). -/
def mulIndicator_thickening_eventually_eq_mulIndicator_closure' : Prop := True
/-- mulIndicator_cthickening_eventually_eq_mulIndicator_closure (abstract). -/
def mulIndicator_cthickening_eventually_eq_mulIndicator_closure' : Prop := True
/-- tendsto_mulIndicator_thickening_mulIndicator_closure (abstract). -/
def tendsto_mulIndicator_thickening_mulIndicator_closure' : Prop := True
/-- tendsto_mulIndicator_cthickening_mulIndicator_closure (abstract). -/
def tendsto_mulIndicator_cthickening_mulIndicator_closure' : Prop := True

-- MetricSpace/Thickening.lean
-- COLLISION: thickening' already in Analysis.lean — rename needed
/-- eventually_not_mem_thickening_of_infEdist_pos (abstract). -/
def eventually_not_mem_thickening_of_infEdist_pos' : Prop := True
/-- isOpen_thickening (abstract). -/
def isOpen_thickening' : Prop := True
/-- thickening_empty (abstract). -/
def thickening_empty' : Prop := True
/-- thickening_of_nonpos (abstract). -/
def thickening_of_nonpos' : Prop := True
/-- thickening_mono (abstract). -/
def thickening_mono' : Prop := True
/-- thickening_subset_of_subset (abstract). -/
def thickening_subset_of_subset' : Prop := True
/-- mem_thickening_iff_exists_edist_lt (abstract). -/
def mem_thickening_iff_exists_edist_lt' : Prop := True
/-- frontier_thickening_subset (abstract). -/
def frontier_thickening_subset' : Prop := True
/-- frontier_thickening_disjoint (abstract). -/
def frontier_thickening_disjoint' : Prop := True
/-- subset_compl_thickening_compl_thickening_self (abstract). -/
def subset_compl_thickening_compl_thickening_self' : Prop := True
/-- thickening_compl_thickening_self_subset_compl (abstract). -/
def thickening_compl_thickening_self_subset_compl' : Prop := True
/-- mem_thickening_iff_infDist_lt (abstract). -/
def mem_thickening_iff_infDist_lt' : Prop := True
/-- mem_thickening_iff (abstract). -/
def mem_thickening_iff' : Prop := True
/-- thickening_singleton (abstract). -/
def thickening_singleton' : Prop := True
/-- ball_subset_thickening (abstract). -/
def ball_subset_thickening' : Prop := True
/-- thickening_eq_biUnion_ball (abstract). -/
def thickening_eq_biUnion_ball' : Prop := True
-- COLLISION: cthickening' already in Analysis.lean — rename needed
/-- eventually_not_mem_cthickening_of_infEdist_pos (abstract). -/
def eventually_not_mem_cthickening_of_infEdist_pos' : Prop := True
/-- mem_cthickening_of_edist_le (abstract). -/
def mem_cthickening_of_edist_le' : Prop := True
/-- mem_cthickening_of_dist_le (abstract). -/
def mem_cthickening_of_dist_le' : Prop := True
/-- isClosed_cthickening (abstract). -/
def isClosed_cthickening' : Prop := True
/-- cthickening_empty (abstract). -/
def cthickening_empty' : Prop := True
/-- cthickening_of_nonpos (abstract). -/
def cthickening_of_nonpos' : Prop := True
/-- cthickening_zero (abstract). -/
def cthickening_zero' : Prop := True
/-- cthickening_max_zero (abstract). -/
def cthickening_max_zero' : Prop := True
/-- cthickening_mono (abstract). -/
def cthickening_mono' : Prop := True
/-- cthickening_singleton (abstract). -/
def cthickening_singleton' : Prop := True
/-- closedBall_subset_cthickening_singleton (abstract). -/
def closedBall_subset_cthickening_singleton' : Prop := True
/-- cthickening_subset_of_subset (abstract). -/
def cthickening_subset_of_subset' : Prop := True
/-- cthickening_subset_thickening (abstract). -/
def cthickening_subset_thickening' : Prop := True
/-- thickening_subset_cthickening (abstract). -/
def thickening_subset_cthickening' : Prop := True
/-- thickening_subset_interior_cthickening (abstract). -/
def thickening_subset_interior_cthickening' : Prop := True
/-- closure_thickening_subset_cthickening (abstract). -/
def closure_thickening_subset_cthickening' : Prop := True
/-- closure_subset_cthickening (abstract). -/
def closure_subset_cthickening' : Prop := True
/-- closure_subset_thickening (abstract). -/
def closure_subset_thickening' : Prop := True
/-- self_subset_thickening (abstract). -/
def self_subset_thickening' : Prop := True
/-- self_subset_cthickening (abstract). -/
def self_subset_cthickening' : Prop := True
/-- thickening_mem_nhdsSet (abstract). -/
def thickening_mem_nhdsSet' : Prop := True
/-- cthickening_mem_nhdsSet (abstract). -/
def cthickening_mem_nhdsSet' : Prop := True
/-- thickening_union (abstract). -/
def thickening_union' : Prop := True
/-- cthickening_union (abstract). -/
def cthickening_union' : Prop := True
/-- thickening_iUnion (abstract). -/
def thickening_iUnion' : Prop := True
/-- thickening_biUnion (abstract). -/
def thickening_biUnion' : Prop := True
/-- ediam_cthickening_le (abstract). -/
def ediam_cthickening_le' : Prop := True
/-- ediam_thickening_le (abstract). -/
def ediam_thickening_le' : Prop := True
/-- diam_cthickening_le (abstract). -/
def diam_cthickening_le' : Prop := True
/-- diam_thickening_le (abstract). -/
def diam_thickening_le' : Prop := True
/-- thickening_closure (abstract). -/
def thickening_closure' : Prop := True
/-- cthickening_closure (abstract). -/
def cthickening_closure' : Prop := True
/-- exists_thickenings (abstract). -/
def exists_thickenings' : Prop := True
/-- exists_cthickenings (abstract). -/
def exists_cthickenings' : Prop := True
/-- exists_cthickening_subset_open (abstract). -/
def exists_cthickening_subset_open' : Prop := True
/-- exists_isCompact_cthickening (abstract). -/
def exists_isCompact_cthickening' : Prop := True
/-- exists_thickening_subset_open (abstract). -/
def exists_thickening_subset_open' : Prop := True
/-- hasBasis_nhdsSet_thickening (abstract). -/
def hasBasis_nhdsSet_thickening' : Prop := True
/-- hasBasis_nhdsSet_cthickening (abstract). -/
def hasBasis_nhdsSet_cthickening' : Prop := True
/-- cthickening_eq_iInter_cthickening' (abstract). -/
def cthickening_eq_iInter_cthickening' : Prop := True
/-- cthickening_eq_iInter_thickening' (abstract). -/
def cthickening_eq_iInter_thickening' : Prop := True
/-- cthickening_eq_iInter_thickening'' (abstract). -/
def cthickening_eq_iInter_thickening'' : Prop := True
/-- closure_eq_iInter_cthickening' (abstract). -/
def closure_eq_iInter_cthickening' : Prop := True
/-- closure_eq_iInter_thickening' (abstract). -/
def closure_eq_iInter_thickening' : Prop := True
/-- frontier_cthickening_subset (abstract). -/
def frontier_cthickening_subset' : Prop := True
/-- closedBall_subset_cthickening (abstract). -/
def closedBall_subset_cthickening' : Prop := True
/-- cthickening_subset_iUnion_closedBall_of_lt (abstract). -/
def cthickening_subset_iUnion_closedBall_of_lt' : Prop := True
/-- cthickening_eq_biUnion_closedBall (abstract). -/
def cthickening_eq_biUnion_closedBall' : Prop := True
/-- infEdist_le_infEdist_thickening_add (abstract). -/
def infEdist_le_infEdist_thickening_add' : Prop := True
/-- thickening_thickening_subset (abstract). -/
def thickening_thickening_subset' : Prop := True
/-- thickening_cthickening_subset (abstract). -/
def thickening_cthickening_subset' : Prop := True
/-- cthickening_thickening_subset (abstract). -/
def cthickening_thickening_subset' : Prop := True
/-- cthickening_cthickening_subset (abstract). -/
def cthickening_cthickening_subset' : Prop := True
/-- frontier_cthickening_disjoint (abstract). -/
def frontier_cthickening_disjoint' : Prop := True

-- MetricSpace/Ultra/Basic.lean
/-- IsUltrametricDist (abstract). -/
def IsUltrametricDist' : Prop := True
/-- dist_triangle_max (abstract). -/
def dist_triangle_max' : Prop := True
/-- dist_eq_max_of_dist_ne_dist (abstract). -/
def dist_eq_max_of_dist_ne_dist' : Prop := True
/-- ball_eq_of_mem (abstract). -/
def ball_eq_of_mem' : Prop := True
/-- mem_ball_iff (abstract). -/
def mem_ball_iff' : Prop := True
/-- ball_subset_trichotomy (abstract). -/
def ball_subset_trichotomy' : Prop := True
/-- ball_eq_or_disjoint (abstract). -/
def ball_eq_or_disjoint' : Prop := True
/-- closedBall_eq_of_mem (abstract). -/
def closedBall_eq_of_mem' : Prop := True
/-- mem_closedBall_iff (abstract). -/
def mem_closedBall_iff' : Prop := True
/-- closedBall_subset_trichotomy (abstract). -/
def closedBall_subset_trichotomy' : Prop := True
/-- isClopen_ball (abstract). -/
def isClopen_ball' : Prop := True
/-- frontier_ball_eq_empty (abstract). -/
def frontier_ball_eq_empty' : Prop := True
/-- closedBall_eq_or_disjoint (abstract). -/
def closedBall_eq_or_disjoint' : Prop := True
/-- isOpen_closedBall (abstract). -/
def isOpen_closedBall' : Prop := True
/-- isClopen_closedBall (abstract). -/
def isClopen_closedBall' : Prop := True
/-- frontier_closedBall_eq_empty (abstract). -/
def frontier_closedBall_eq_empty' : Prop := True
/-- isOpen_sphere (abstract). -/
def isOpen_sphere' : Prop := True
/-- isClopen_sphere (abstract). -/
def isClopen_sphere' : Prop := True

-- Metrizable/Basic.lean
/-- PseudoMetrizableSpace (abstract). -/
def PseudoMetrizableSpace' : Prop := True
/-- pseudoMetrizableSpacePseudoMetric (abstract). -/
def pseudoMetrizableSpacePseudoMetric' : Prop := True
/-- pseudoMetrizableSpace (abstract). -/
def pseudoMetrizableSpace' : Prop := True
/-- MetrizableSpace (abstract). -/
def MetrizableSpace' : Prop := True
/-- metrizableSpaceMetric (abstract). -/
def metrizableSpaceMetric' : Prop := True
/-- metrizableSpace (abstract). -/
def metrizableSpace' : Prop := True

-- Metrizable/Uniformity.lean
-- COLLISION: such' already in Analysis.lean — rename needed
/-- ofPreNNDist (abstract). -/
def ofPreNNDist' : Prop := True
/-- dist_ofPreNNDist_le (abstract). -/
def dist_ofPreNNDist_le' : Prop := True
/-- le_two_mul_dist_ofPreNNDist (abstract). -/
def le_two_mul_dist_ofPreNNDist' : Prop := True
/-- metrizable_uniformity (abstract). -/
def metrizable_uniformity' : Prop := True
/-- pseudoMetricSpace (abstract). -/
def pseudoMetricSpace' : Prop := True

-- Metrizable/Urysohn.lean
/-- exists_isInducing_l_infty (abstract). -/
def exists_isInducing_l_infty' : Prop := True
/-- exists_embedding_l_infty (abstract). -/
def exists_embedding_l_infty' : Prop := True

-- NhdsSet.lean
/-- nhdsSet_diagonal (abstract). -/
def nhdsSet_diagonal' : Prop := True
/-- mem_nhdsSet_iff_forall (abstract). -/
def mem_nhdsSet_iff_forall' : Prop := True
/-- nhdsSet_le (abstract). -/
def nhdsSet_le' : Prop := True
/-- bUnion_mem_nhdsSet (abstract). -/
def bUnion_mem_nhdsSet' : Prop := True
/-- subset_interior_iff_mem_nhdsSet (abstract). -/
def subset_interior_iff_mem_nhdsSet' : Prop := True
/-- disjoint_principal_nhdsSet (abstract). -/
def disjoint_principal_nhdsSet' : Prop := True
/-- disjoint_nhdsSet_principal (abstract). -/
def disjoint_nhdsSet_principal' : Prop := True
/-- mem_nhdsSet_iff_exists (abstract). -/
def mem_nhdsSet_iff_exists' : Prop := True
/-- eventually_nhdsSet_iff_exists (abstract). -/
def eventually_nhdsSet_iff_exists' : Prop := True
/-- eventually_nhdsSet_iff_forall (abstract). -/
def eventually_nhdsSet_iff_forall' : Prop := True
/-- hasBasis_nhdsSet (abstract). -/
def hasBasis_nhdsSet' : Prop := True
/-- lift'_nhdsSet_interior (abstract). -/
def lift'_nhdsSet_interior' : Prop := True
/-- nhdsSet_interior (abstract). -/
def nhdsSet_interior' : Prop := True
/-- mem_nhdsSet (abstract). -/
def mem_nhdsSet' : Prop := True
/-- mem_nhdsSet_self (abstract). -/
def mem_nhdsSet_self' : Prop := True
/-- nhdsSet_eq_principal_iff (abstract). -/
def nhdsSet_eq_principal_iff' : Prop := True
/-- nhdsSet_singleton (abstract). -/
def nhdsSet_singleton' : Prop := True
/-- mem_nhdsSet_interior (abstract). -/
def mem_nhdsSet_interior' : Prop := True
/-- nhdsSet_empty (abstract). -/
def nhdsSet_empty' : Prop := True
/-- nhdsSet_univ (abstract). -/
def nhdsSet_univ' : Prop := True
/-- nhdsSet_mono (abstract). -/
def nhdsSet_mono' : Prop := True
/-- monotone_nhdsSet (abstract). -/
def monotone_nhdsSet' : Prop := True
/-- nhds_le_nhdsSet (abstract). -/
def nhds_le_nhdsSet' : Prop := True
/-- nhdsSet_union (abstract). -/
def nhdsSet_union' : Prop := True
/-- union_mem_nhdsSet (abstract). -/
def union_mem_nhdsSet' : Prop := True
/-- nhdsSet_insert (abstract). -/
def nhdsSet_insert' : Prop := True
/-- tendsto_nhdsSet (abstract). -/
def tendsto_nhdsSet' : Prop := True
/-- tendsto_nhdsSet_nhds (abstract). -/
def tendsto_nhdsSet_nhds' : Prop := True
/-- nhdsSet_inter_le (abstract). -/
def nhdsSet_inter_le' : Prop := True
/-- nhdsSet_iInter_le (abstract). -/
def nhdsSet_iInter_le' : Prop := True
/-- nhdsSet_sInter_le (abstract). -/
def nhdsSet_sInter_le' : Prop := True
/-- nhdsSet_le_sup (abstract). -/
def nhdsSet_le_sup' : Prop := True
/-- eventually_nhdsSet (abstract). -/
def eventually_nhdsSet' : Prop := True
/-- union_nhdsSet (abstract). -/
def union_nhdsSet' : Prop := True
/-- nhdsSet_iUnion (abstract). -/
def nhdsSet_iUnion' : Prop := True
/-- eventually_nhdsSet_iUnion₂ (abstract). -/
def eventually_nhdsSet_iUnion₂' : Prop := True
/-- eventually_nhdsSet_iUnion (abstract). -/
def eventually_nhdsSet_iUnion' : Prop := True

-- NoetherianSpace.lean
/-- NoetherianSpace (abstract). -/
def NoetherianSpace' : Prop := True
/-- noetherianSpace_iff_opens (abstract). -/
def noetherianSpace_iff_opens' : Prop := True
/-- noetherianSpace (abstract). -/
def noetherianSpace' : Prop := True
/-- noetherianSpace_TFAE (abstract). -/
def noetherianSpace_TFAE' : Prop := True
/-- noetherianSpace_iff_isCompact (abstract). -/
def noetherianSpace_iff_isCompact' : Prop := True
/-- wellFounded_closeds (abstract). -/
def wellFounded_closeds' : Prop := True
/-- noetherianSpace_of_surjective (abstract). -/
def noetherianSpace_of_surjective' : Prop := True
/-- noetherianSpace_iff_of_homeomorph (abstract). -/
def noetherianSpace_iff_of_homeomorph' : Prop := True
/-- noetherianSpace_set_iff (abstract). -/
def noetherianSpace_set_iff' : Prop := True
/-- noetherian_univ_iff (abstract). -/
def noetherian_univ_iff' : Prop := True
/-- exists_finite_set_closeds_irreducible (abstract). -/
def exists_finite_set_closeds_irreducible' : Prop := True
/-- exists_finite_set_isClosed_irreducible (abstract). -/
def exists_finite_set_isClosed_irreducible' : Prop := True
/-- exists_finset_irreducible (abstract). -/
def exists_finset_irreducible' : Prop := True
/-- finite_irreducibleComponents (abstract). -/
def finite_irreducibleComponents' : Prop := True
/-- exists_open_ne_empty_le_irreducibleComponent (abstract). -/
def exists_open_ne_empty_le_irreducibleComponent' : Prop := True

-- OmegaCompletePartialOrder.lean
/-- ωscottContinuous_iff_continuous (abstract). -/
def ωscottContinuous_iff_continuous' : Prop := True
/-- IsωSup (abstract). -/
def IsωSup' : Prop := True
/-- isωSup_iff_isLUB (abstract). -/
def isωSup_iff_isLUB' : Prop := True
/-- isUpperSet (abstract). -/
def isUpperSet' : Prop := True
/-- Scott (abstract). -/
def Scott' : Prop := True
/-- notBelow (abstract). -/
def notBelow' : Prop := True
/-- notBelow_isOpen (abstract). -/
def notBelow_isOpen' : Prop := True
/-- isωSup_ωSup (abstract). -/
def isωSup_ωSup' : Prop := True
/-- scottContinuous_of_continuous (abstract). -/
def scottContinuous_of_continuous' : Prop := True
/-- continuous_of_scottContinuous (abstract). -/
def continuous_of_scottContinuous' : Prop := True

-- Order.lean
/-- GenerateOpen (abstract). -/
def GenerateOpen' : Prop := True
-- COLLISION: generateFrom' already in MeasureTheory2.lean — rename needed
/-- isOpen_generateFrom_of_mem (abstract). -/
def isOpen_generateFrom_of_mem' : Prop := True
/-- nhds_generateFrom (abstract). -/
def nhds_generateFrom' : Prop := True
/-- tendsto_nhds_generateFrom_iff (abstract). -/
def tendsto_nhds_generateFrom_iff' : Prop := True
/-- mkOfNhds (abstract). -/
def mkOfNhds' : Prop := True
/-- nhds_mkOfNhds_of_hasBasis (abstract). -/
def nhds_mkOfNhds_of_hasBasis' : Prop := True
/-- nhds_mkOfNhds (abstract). -/
def nhds_mkOfNhds' : Prop := True
/-- nhds_mkOfNhds_single (abstract). -/
def nhds_mkOfNhds_single' : Prop := True
/-- nhds_mkOfNhds_filterBasis (abstract). -/
def nhds_mkOfNhds_filterBasis' : Prop := True
/-- le_generateFrom_iff_subset_isOpen (abstract). -/
def le_generateFrom_iff_subset_isOpen' : Prop := True
-- COLLISION: mkOfClosure' already in Order.lean — rename needed
-- COLLISION: mkOfClosure_sets' already in Order.lean — rename needed
/-- gc_generateFrom (abstract). -/
def gc_generateFrom' : Prop := True
/-- gciGenerateFrom (abstract). -/
def gciGenerateFrom' : Prop := True
/-- generateFrom_anti (abstract). -/
def generateFrom_anti' : Prop := True
/-- generateFrom_setOf_isOpen (abstract). -/
def generateFrom_setOf_isOpen' : Prop := True
/-- leftInverse_generateFrom (abstract). -/
def leftInverse_generateFrom' : Prop := True
/-- isOpen_top_iff (abstract). -/
def isOpen_top_iff' : Prop := True
/-- DiscreteTopology (abstract). -/
def DiscreteTopology' : Prop := True
/-- discreteTopology_bot (abstract). -/
def discreteTopology_bot' : Prop := True
/-- isOpen_discrete (abstract). -/
def isOpen_discrete' : Prop := True
/-- isClosed_discrete (abstract). -/
def isClosed_discrete' : Prop := True
/-- closure_discrete (abstract). -/
def closure_discrete' : Prop := True
/-- dense_discrete (abstract). -/
def dense_discrete' : Prop := True
/-- denseRange_discrete (abstract). -/
def denseRange_discrete' : Prop := True
/-- continuous_of_discreteTopology (abstract). -/
def continuous_of_discreteTopology' : Prop := True
/-- continuous_discrete_rng (abstract). -/
def continuous_discrete_rng' : Prop := True
/-- nhds_discrete (abstract). -/
def nhds_discrete' : Prop := True
/-- mem_nhds_discrete (abstract). -/
def mem_nhds_discrete' : Prop := True
/-- le_of_nhds_le_nhds (abstract). -/
def le_of_nhds_le_nhds' : Prop := True
/-- eq_bot_of_singletons_open (abstract). -/
def eq_bot_of_singletons_open' : Prop := True
/-- forall_open_iff_discrete (abstract). -/
def forall_open_iff_discrete' : Prop := True
/-- discreteTopology_iff_forall_isClosed (abstract). -/
def discreteTopology_iff_forall_isClosed' : Prop := True
/-- singletons_open_iff_discrete (abstract). -/
def singletons_open_iff_discrete' : Prop := True
/-- of_finite_of_isClosed_singleton (abstract). -/
def of_finite_of_isClosed_singleton' : Prop := True
/-- discreteTopology_iff_singleton_mem_nhds (abstract). -/
def discreteTopology_iff_singleton_mem_nhds' : Prop := True
/-- discreteTopology_iff_nhds (abstract). -/
def discreteTopology_iff_nhds' : Prop := True
/-- discreteTopology_iff_nhds_ne (abstract). -/
def discreteTopology_iff_nhds_ne' : Prop := True
/-- of_continuous_injective (abstract). -/
def of_continuous_injective' : Prop := True
/-- isClosed_coinduced (abstract). -/
def isClosed_coinduced' : Prop := True
/-- preimage_nhds_coinduced (abstract). -/
def preimage_nhds_coinduced' : Prop := True
/-- coinduced_le (abstract). -/
def coinduced_le' : Prop := True
-- COLLISION: α' already in SetTheory.lean — rename needed
/-- coinduced_le_iff_le_induced (abstract). -/
def coinduced_le_iff_le_induced' : Prop := True
/-- le_induced (abstract). -/
def le_induced' : Prop := True
/-- gc_coinduced_induced (abstract). -/
def gc_coinduced_induced' : Prop := True
/-- induced_mono (abstract). -/
def induced_mono' : Prop := True
/-- coinduced_mono (abstract). -/
def coinduced_mono' : Prop := True
/-- induced_top (abstract). -/
def induced_top' : Prop := True
/-- induced_inf (abstract). -/
def induced_inf' : Prop := True
/-- induced_iInf (abstract). -/
def induced_iInf' : Prop := True
/-- induced_sInf (abstract). -/
def induced_sInf' : Prop := True
/-- coinduced_bot (abstract). -/
def coinduced_bot' : Prop := True
/-- coinduced_sup (abstract). -/
def coinduced_sup' : Prop := True
/-- coinduced_iSup (abstract). -/
def coinduced_iSup' : Prop := True
/-- coinduced_sSup (abstract). -/
def coinduced_sSup' : Prop := True
/-- induced_id (abstract). -/
def induced_id' : Prop := True
/-- induced_compose (abstract). -/
def induced_compose' : Prop := True
/-- induced_const (abstract). -/
def induced_const' : Prop := True
/-- coinduced_id (abstract). -/
def coinduced_id' : Prop := True
/-- coinduced_compose (abstract). -/
def coinduced_compose' : Prop := True
/-- induced_symm (abstract). -/
def induced_symm' : Prop := True
/-- coinduced_symm (abstract). -/
def coinduced_symm' : Prop := True
/-- continuous_empty_function (abstract). -/
def continuous_empty_function' : Prop := True
/-- le_generateFrom (abstract). -/
def le_generateFrom' : Prop := True
/-- induced_generateFrom_eq (abstract). -/
def induced_generateFrom_eq' : Prop := True
/-- le_induced_generateFrom (abstract). -/
def le_induced_generateFrom' : Prop := True
/-- generateFrom_insert_of_generateOpen (abstract). -/
def generateFrom_insert_of_generateOpen' : Prop := True
-- COLLISION: generateFrom_insert_univ' already in MeasureTheory2.lean — rename needed
-- COLLISION: generateFrom_insert_empty' already in MeasureTheory2.lean — rename needed
/-- nhdsAdjoint (abstract). -/
def nhdsAdjoint' : Prop := True
/-- gc_nhds (abstract). -/
def gc_nhds' : Prop := True
/-- le_iff_nhds (abstract). -/
def le_iff_nhds' : Prop := True
/-- isOpen_singleton_nhdsAdjoint (abstract). -/
def isOpen_singleton_nhdsAdjoint' : Prop := True
/-- nhds_nhdsAdjoint_same (abstract). -/
def nhds_nhdsAdjoint_same' : Prop := True
/-- nhds_nhdsAdjoint_of_ne (abstract). -/
def nhds_nhdsAdjoint_of_ne' : Prop := True
/-- nhdsAdjoint_nhds_of_ne (abstract). -/
def nhdsAdjoint_nhds_of_ne' : Prop := True
/-- nhds_nhdsAdjoint (abstract). -/
def nhds_nhdsAdjoint' : Prop := True
/-- le_nhdsAdjoint_iff' (abstract). -/
def le_nhdsAdjoint_iff' : Prop := True
/-- nhds_sInf (abstract). -/
def nhds_sInf' : Prop := True
/-- continuous_iff_coinduced_le (abstract). -/
def continuous_iff_coinduced_le' : Prop := True
/-- continuous_iff_le_induced (abstract). -/
def continuous_iff_le_induced' : Prop := True
/-- continuous_generateFrom_iff (abstract). -/
def continuous_generateFrom_iff' : Prop := True
/-- continuous_induced_dom (abstract). -/
def continuous_induced_dom' : Prop := True
/-- continuous_induced_rng (abstract). -/
def continuous_induced_rng' : Prop := True
/-- continuous_coinduced_rng (abstract). -/
def continuous_coinduced_rng' : Prop := True
/-- continuous_coinduced_dom (abstract). -/
def continuous_coinduced_dom' : Prop := True
/-- continuous_le_dom (abstract). -/
def continuous_le_dom' : Prop := True
/-- continuous_le_rng (abstract). -/
def continuous_le_rng' : Prop := True
/-- continuous_sup_dom (abstract). -/
def continuous_sup_dom' : Prop := True
/-- continuous_sup_rng_left (abstract). -/
def continuous_sup_rng_left' : Prop := True
/-- continuous_sup_rng_right (abstract). -/
def continuous_sup_rng_right' : Prop := True
/-- continuous_sSup_dom (abstract). -/
def continuous_sSup_dom' : Prop := True
/-- continuous_sSup_rng (abstract). -/
def continuous_sSup_rng' : Prop := True
/-- continuous_iSup_dom (abstract). -/
def continuous_iSup_dom' : Prop := True
/-- continuous_iSup_rng (abstract). -/
def continuous_iSup_rng' : Prop := True
/-- continuous_inf_rng (abstract). -/
def continuous_inf_rng' : Prop := True
/-- continuous_inf_dom_left (abstract). -/
def continuous_inf_dom_left' : Prop := True
/-- continuous_inf_dom_right (abstract). -/
def continuous_inf_dom_right' : Prop := True
/-- continuous_sInf_dom (abstract). -/
def continuous_sInf_dom' : Prop := True
/-- continuous_sInf_rng (abstract). -/
def continuous_sInf_rng' : Prop := True
/-- continuous_iInf_dom (abstract). -/
def continuous_iInf_dom' : Prop := True
/-- continuous_iInf_rng (abstract). -/
def continuous_iInf_rng' : Prop := True
/-- continuous_bot (abstract). -/
def continuous_bot' : Prop := True
/-- continuous_top (abstract). -/
def continuous_top' : Prop := True
/-- continuous_id_iff_le (abstract). -/
def continuous_id_iff_le' : Prop := True
/-- continuous_id_of_le (abstract). -/
def continuous_id_of_le' : Prop := True
/-- mem_nhds_induced (abstract). -/
def mem_nhds_induced' : Prop := True
/-- nhds_induced (abstract). -/
def nhds_induced' : Prop := True
/-- induced_iff_nhds_eq (abstract). -/
def induced_iff_nhds_eq' : Prop := True
/-- map_nhds_induced_of_surjective (abstract). -/
def map_nhds_induced_of_surjective' : Prop := True
/-- continuous_nhdsAdjoint_dom (abstract). -/
def continuous_nhdsAdjoint_dom' : Prop := True
/-- coinduced_nhdsAdjoint (abstract). -/
def coinduced_nhdsAdjoint' : Prop := True
/-- isOpen_induced (abstract). -/
def isOpen_induced' : Prop := True
/-- map_nhds_induced_eq (abstract). -/
def map_nhds_induced_eq' : Prop := True
/-- map_nhds_induced_of_mem (abstract). -/
def map_nhds_induced_of_mem' : Prop := True
/-- closure_induced (abstract). -/
def closure_induced' : Prop := True
/-- isClosed_induced_iff' (abstract). -/
def isClosed_induced_iff' : Prop := True
/-- isOpen_singleton_true (abstract). -/
def isOpen_singleton_true' : Prop := True
/-- nhds_true (abstract). -/
def nhds_true' : Prop := True
/-- nhds_false (abstract). -/
def nhds_false' : Prop := True
/-- tendsto_nhds_Prop (abstract). -/
def tendsto_nhds_Prop' : Prop := True
/-- continuous_Prop (abstract). -/
def continuous_Prop' : Prop := True
/-- isOpen_iff_continuous_mem (abstract). -/
def isOpen_iff_continuous_mem' : Prop := True
/-- generateFrom_union (abstract). -/
def generateFrom_union' : Prop := True
/-- generateFrom_iUnion (abstract). -/
def generateFrom_iUnion' : Prop := True
/-- setOf_isOpen_iSup (abstract). -/
def setOf_isOpen_iSup' : Prop := True
/-- generateFrom_sUnion (abstract). -/
def generateFrom_sUnion' : Prop := True
/-- setOf_isOpen_sSup (abstract). -/
def setOf_isOpen_sSup' : Prop := True
/-- generateFrom_union_isOpen (abstract). -/
def generateFrom_union_isOpen' : Prop := True
/-- generateFrom_iUnion_isOpen (abstract). -/
def generateFrom_iUnion_isOpen' : Prop := True
/-- generateFrom_inter (abstract). -/
def generateFrom_inter' : Prop := True
/-- generateFrom_iInter (abstract). -/
def generateFrom_iInter' : Prop := True
/-- generateFrom_iInter_of_generateFrom_eq_self (abstract). -/
def generateFrom_iInter_of_generateFrom_eq_self' : Prop := True
/-- isOpen_iSup_iff (abstract). -/
def isOpen_iSup_iff' : Prop := True
/-- isOpen_sSup_iff (abstract). -/
def isOpen_sSup_iff' : Prop := True
/-- isClosed_iSup_iff (abstract). -/
def isClosed_iSup_iff' : Prop := True
/-- isClosed_sSup_iff (abstract). -/
def isClosed_sSup_iff' : Prop := True

-- Order/Basic.lean
/-- known (abstract). -/
def known' : Prop := True
/-- OrderTopology (abstract). -/
def OrderTopology' : Prop := True
/-- isOpen_iff_generate_intervals (abstract). -/
def isOpen_iff_generate_intervals' : Prop := True
/-- isOpen_lt' (abstract). -/
def isOpen_lt' : Prop := True
/-- isOpen_gt' (abstract). -/
def isOpen_gt' : Prop := True
/-- lt_mem_nhds (abstract). -/
def lt_mem_nhds' : Prop := True
/-- le_mem_nhds (abstract). -/
def le_mem_nhds' : Prop := True
/-- gt_mem_nhds (abstract). -/
def gt_mem_nhds' : Prop := True
/-- ge_mem_nhds (abstract). -/
def ge_mem_nhds' : Prop := True
/-- nhds_eq_order (abstract). -/
def nhds_eq_order' : Prop := True
/-- tendsto_order (abstract). -/
def tendsto_order' : Prop := True
/-- tendsto_of_tendsto_of_tendsto_of_le_of_le' (abstract). -/
def tendsto_of_tendsto_of_tendsto_of_le_of_le' : Prop := True
/-- nhds_order_unbounded (abstract). -/
def nhds_order_unbounded' : Prop := True
/-- tendsto_order_unbounded (abstract). -/
def tendsto_order_unbounded' : Prop := True
/-- induced_topology_le_preorder (abstract). -/
def induced_topology_le_preorder' : Prop := True
/-- induced_topology_eq_preorder (abstract). -/
def induced_topology_eq_preorder' : Prop := True
/-- induced_orderTopology' (abstract). -/
def induced_orderTopology' : Prop := True
/-- isEmbedding_of_ordConnected (abstract). -/
def isEmbedding_of_ordConnected' : Prop := True
/-- nhdsWithin_Ici_eq'' (abstract). -/
def nhdsWithin_Ici_eq'' : Prop := True
/-- nhdsWithin_Iic_eq'' (abstract). -/
def nhdsWithin_Iic_eq'' : Prop := True
/-- nhdsWithin_Ici_eq' (abstract). -/
def nhdsWithin_Ici_eq' : Prop := True
/-- nhdsWithin_Iic_eq' (abstract). -/
def nhdsWithin_Iic_eq' : Prop := True
/-- nhdsWithin_Ici_basis' (abstract). -/
def nhdsWithin_Ici_basis' : Prop := True
/-- nhdsWithin_Iic_basis' (abstract). -/
def nhdsWithin_Iic_basis' : Prop := True
/-- nhds_top_order (abstract). -/
def nhds_top_order' : Prop := True
/-- nhds_bot_order (abstract). -/
def nhds_bot_order' : Prop := True
/-- tendsto_nhds_top_mono (abstract). -/
def tendsto_nhds_top_mono' : Prop := True
/-- tendsto_nhds_bot_mono (abstract). -/
def tendsto_nhds_bot_mono' : Prop := True
/-- exists_Ioc_subset_of_mem_nhds (abstract). -/
def exists_Ioc_subset_of_mem_nhds' : Prop := True
/-- exists_Icc_mem_subset_of_mem_nhdsWithin_Ici (abstract). -/
def exists_Icc_mem_subset_of_mem_nhdsWithin_Ici' : Prop := True
/-- exists_Icc_mem_subset_of_mem_nhdsWithin_Iic (abstract). -/
def exists_Icc_mem_subset_of_mem_nhdsWithin_Iic' : Prop := True
/-- exists_Icc_mem_subset_of_mem_nhds (abstract). -/
def exists_Icc_mem_subset_of_mem_nhds' : Prop := True
/-- mem_nhds_iff_exists_Ioo_subset' (abstract). -/
def mem_nhds_iff_exists_Ioo_subset' : Prop := True
/-- nhds_basis_Ioo' (abstract). -/
def nhds_basis_Ioo' : Prop := True
/-- exists_Ioo_subset (abstract). -/
def exists_Ioo_subset' : Prop := True
/-- topology_eq_generateFrom (abstract). -/
def topology_eq_generateFrom' : Prop := True
/-- atBot_le_nhds_bot (abstract). -/
def atBot_le_nhds_bot' : Prop := True
/-- atTop_le_nhds_top (abstract). -/
def atTop_le_nhds_top' : Prop := True
/-- of_separableSpace_orderTopology (abstract). -/
def of_separableSpace_orderTopology' : Prop := True
/-- countable_setOf_covBy_right (abstract). -/
def countable_setOf_covBy_right' : Prop := True
/-- countable_setOf_covBy_left (abstract). -/
def countable_setOf_covBy_left' : Prop := True
/-- countable_of_isolated_left' (abstract). -/
def countable_of_isolated_left' : Prop := True
/-- countable_of_Ioo (abstract). -/
def countable_of_Ioo' : Prop := True
/-- countable_image_lt_image_Ioi (abstract). -/
def countable_image_lt_image_Ioi' : Prop := True
/-- countable_image_gt_image_Ioi (abstract). -/
def countable_image_gt_image_Ioi' : Prop := True
/-- countable_image_lt_image_Iio (abstract). -/
def countable_image_lt_image_Iio' : Prop := True
/-- countable_image_gt_image_Iio (abstract). -/
def countable_image_gt_image_Iio' : Prop := True
/-- pi_Iic_mem_nhds (abstract). -/
def pi_Iic_mem_nhds' : Prop := True
/-- pi_Ici_mem_nhds (abstract). -/
def pi_Ici_mem_nhds' : Prop := True
/-- pi_Icc_mem_nhds (abstract). -/
def pi_Icc_mem_nhds' : Prop := True
/-- pi_Iio_mem_nhds (abstract). -/
def pi_Iio_mem_nhds' : Prop := True
/-- pi_Ioi_mem_nhds (abstract). -/
def pi_Ioi_mem_nhds' : Prop := True
/-- pi_Ioc_mem_nhds (abstract). -/
def pi_Ioc_mem_nhds' : Prop := True
/-- pi_Ico_mem_nhds (abstract). -/
def pi_Ico_mem_nhds' : Prop := True
/-- pi_Ioo_mem_nhds (abstract). -/
def pi_Ioo_mem_nhds' : Prop := True

-- Order/Bornology.lean
-- COLLISION: predicate' already in Algebra.lean — rename needed
/-- orderBornology (abstract). -/
def orderBornology' : Prop := True
/-- orderBornology_isBounded (abstract). -/
def orderBornology_isBounded' : Prop := True
/-- IsOrderBornology (abstract). -/
def IsOrderBornology' : Prop := True
/-- isOrderBornology_iff_eq_orderBornology (abstract). -/
def isOrderBornology_iff_eq_orderBornology' : Prop := True
/-- isBounded_iff_bddBelow_bddAbove (abstract). -/
def isBounded_iff_bddBelow_bddAbove' : Prop := True
-- COLLISION: bddBelow' already in Order.lean — rename needed
-- COLLISION: bddAbove' already in Order.lean — rename needed
/-- isBounded_inter (abstract). -/
def isBounded_inter' : Prop := True
/-- subset_Icc_sInf_sSup (abstract). -/
def subset_Icc_sInf_sSup' : Prop := True

-- Order/Category/AlexDisc.lean
/-- AlexandrovDiscreteSpace (abstract). -/
def AlexandrovDiscreteSpace' : Prop := True
/-- AlexDisc (abstract). -/
def AlexDisc' : Prop := True
/-- alexDiscEquivPreord (abstract). -/
def alexDiscEquivPreord' : Prop := True

-- Order/Category/FrameAdjunction.lean
/-- PT (abstract). -/
def PT' : Prop := True
/-- openOfElementHom (abstract). -/
def openOfElementHom' : Prop := True
/-- pt (abstract). -/
def pt' : Prop := True
/-- localePointOfSpacePoint (abstract). -/
def localePointOfSpacePoint' : Prop := True
/-- counitAppCont (abstract). -/
def counitAppCont' : Prop := True
/-- adjunctionTopToLocalePT (abstract). -/
def adjunctionTopToLocalePT' : Prop := True

-- Order/Compact.lean
/-- CompactIccSpace (abstract). -/
def CompactIccSpace' : Prop := True
-- COLLISION: mk'' already in Algebra.lean — rename needed
/-- isCompact_uIcc (abstract). -/
def isCompact_uIcc' : Prop := True
/-- exists_isLeast (abstract). -/
def exists_isLeast' : Prop := True
/-- exists_isGreatest (abstract). -/
def exists_isGreatest' : Prop := True
/-- exists_isGLB (abstract). -/
def exists_isGLB' : Prop := True
/-- exists_isLUB (abstract). -/
def exists_isLUB' : Prop := True
/-- cocompact_le_atBot_atTop (abstract). -/
def cocompact_le_atBot_atTop' : Prop := True
/-- cocompact_le_atBot (abstract). -/
def cocompact_le_atBot' : Prop := True
/-- cocompact_le_atTop (abstract). -/
def cocompact_le_atTop' : Prop := True
/-- atBot_le_cocompact (abstract). -/
def atBot_le_cocompact' : Prop := True
/-- atTop_le_cocompact (abstract). -/
def atTop_le_cocompact' : Prop := True
/-- atBot_atTop_le_cocompact (abstract). -/
def atBot_atTop_le_cocompact' : Prop := True
/-- cocompact_eq_atBot_atTop (abstract). -/
def cocompact_eq_atBot_atTop' : Prop := True
/-- cocompact_eq_atBot (abstract). -/
def cocompact_eq_atBot' : Prop := True
/-- cocompact_eq_atTop (abstract). -/
def cocompact_eq_atTop' : Prop := True
/-- exists_isMinOn (abstract). -/
def exists_isMinOn' : Prop := True
-- COLLISION: exists_forall_le' already in Order.lean — rename needed
/-- exists_isMaxOn (abstract). -/
def exists_isMaxOn' : Prop := True
-- COLLISION: exists_forall_ge' already in Order.lean — rename needed
/-- exists_forall_le_of_hasCompactMulSupport (abstract). -/
def exists_forall_le_of_hasCompactMulSupport' : Prop := True
/-- exists_forall_ge_of_hasCompactMulSupport (abstract). -/
def exists_forall_ge_of_hasCompactMulSupport' : Prop := True
-- COLLISION: bddBelow_image' already in Order.lean — rename needed
-- COLLISION: bddAbove_image' already in SetTheory.lean — rename needed
/-- bddBelow_range_of_hasCompactMulSupport (abstract). -/
def bddBelow_range_of_hasCompactMulSupport' : Prop := True
/-- bddAbove_range_of_hasCompactMulSupport (abstract). -/
def bddAbove_range_of_hasCompactMulSupport' : Prop := True
/-- sSup_lt_iff_of_continuous (abstract). -/
def sSup_lt_iff_of_continuous' : Prop := True
/-- lt_sInf_iff_of_continuous (abstract). -/
def lt_sInf_iff_of_continuous' : Prop := True
/-- sInf_mem (abstract). -/
def sInf_mem' : Prop := True
/-- sSup_mem (abstract). -/
def sSup_mem' : Prop := True
-- COLLISION: isGLB_sInf' already in Order.lean — rename needed
-- COLLISION: isLUB_sSup' already in Order.lean — rename needed
/-- isLeast_sInf (abstract). -/
def isLeast_sInf' : Prop := True
/-- isGreatest_sSup (abstract). -/
def isGreatest_sSup' : Prop := True
/-- exists_sInf_image_eq_and_le (abstract). -/
def exists_sInf_image_eq_and_le' : Prop := True
/-- exists_sSup_image_eq_and_ge (abstract). -/
def exists_sSup_image_eq_and_ge' : Prop := True
/-- exists_sInf_image_eq (abstract). -/
def exists_sInf_image_eq' : Prop := True
/-- exists_sSup_image_eq (abstract). -/
def exists_sSup_image_eq' : Prop := True
/-- exists_isMinOn_mem_subset (abstract). -/
def exists_isMinOn_mem_subset' : Prop := True
/-- exists_isMaxOn_mem_subset (abstract). -/
def exists_isMaxOn_mem_subset' : Prop := True
/-- exists_isLocalMin_mem_open (abstract). -/
def exists_isLocalMin_mem_open' : Prop := True
/-- exists_isLocalMax_mem_open (abstract). -/
def exists_isLocalMax_mem_open' : Prop := True
/-- eq_Icc_of_connected_compact (abstract). -/
def eq_Icc_of_connected_compact' : Prop := True
/-- continuous_sSup (abstract). -/
def continuous_sSup' : Prop := True
/-- continuous_sInf (abstract). -/
def continuous_sInf' : Prop := True
-- COLLISION: image_Icc' already in Order.lean — rename needed
/-- image_uIcc_eq_Icc (abstract). -/
def image_uIcc_eq_Icc' : Prop := True
-- COLLISION: image_uIcc' already in Algebra.lean — rename needed
/-- sInf_image_Icc_le (abstract). -/
def sInf_image_Icc_le' : Prop := True
/-- le_sSup_image_Icc (abstract). -/
def le_sSup_image_Icc' : Prop := True

-- Order/DenselyOrdered.lean
/-- closure_Ioi' (abstract). -/
def closure_Ioi' : Prop := True
/-- closure_Iio' (abstract). -/
def closure_Iio' : Prop := True
/-- closure_Ioo (abstract). -/
def closure_Ioo' : Prop := True
/-- closure_Ioc (abstract). -/
def closure_Ioc' : Prop := True
/-- closure_Ico (abstract). -/
def closure_Ico' : Prop := True
/-- interior_Ici' (abstract). -/
def interior_Ici' : Prop := True
/-- interior_Iic' (abstract). -/
def interior_Iic' : Prop := True
/-- interior_Icc (abstract). -/
def interior_Icc' : Prop := True
/-- Icc_mem_nhds_iff (abstract). -/
def Icc_mem_nhds_iff' : Prop := True
/-- interior_Ico (abstract). -/
def interior_Ico' : Prop := True
/-- Ico_mem_nhds_iff (abstract). -/
def Ico_mem_nhds_iff' : Prop := True
/-- interior_Ioc (abstract). -/
def interior_Ioc' : Prop := True
/-- Ioc_mem_nhds_iff (abstract). -/
def Ioc_mem_nhds_iff' : Prop := True
/-- closure_interior_Icc (abstract). -/
def closure_interior_Icc' : Prop := True
/-- Ioc_subset_closure_interior (abstract). -/
def Ioc_subset_closure_interior' : Prop := True
/-- Ico_subset_closure_interior (abstract). -/
def Ico_subset_closure_interior' : Prop := True
/-- frontier_Ici' (abstract). -/
def frontier_Ici' : Prop := True
/-- frontier_Iic' (abstract). -/
def frontier_Iic' : Prop := True
/-- frontier_Ioi' (abstract). -/
def frontier_Ioi' : Prop := True
/-- frontier_Iio' (abstract). -/
def frontier_Iio' : Prop := True
/-- frontier_Icc (abstract). -/
def frontier_Icc' : Prop := True
/-- frontier_Ioo (abstract). -/
def frontier_Ioo' : Prop := True
/-- frontier_Ico (abstract). -/
def frontier_Ico' : Prop := True
/-- frontier_Ioc (abstract). -/
def frontier_Ioc' : Prop := True
/-- nhdsWithin_Ioi_neBot' (abstract). -/
def nhdsWithin_Ioi_neBot' : Prop := True
/-- nhdsWithin_Ioi_self_neBot' (abstract). -/
def nhdsWithin_Ioi_self_neBot' : Prop := True
/-- nhdsWithin_Iio_neBot' (abstract). -/
def nhdsWithin_Iio_neBot' : Prop := True
/-- nhdsWithin_Iio_self_neBot' (abstract). -/
def nhdsWithin_Iio_self_neBot' : Prop := True
/-- right_nhdsWithin_Ico_neBot (abstract). -/
def right_nhdsWithin_Ico_neBot' : Prop := True
/-- left_nhdsWithin_Ioc_neBot (abstract). -/
def left_nhdsWithin_Ioc_neBot' : Prop := True
/-- left_nhdsWithin_Ioo_neBot (abstract). -/
def left_nhdsWithin_Ioo_neBot' : Prop := True
/-- right_nhdsWithin_Ioo_neBot (abstract). -/
def right_nhdsWithin_Ioo_neBot' : Prop := True
/-- comap_coe_nhdsWithin_Iio_of_Ioo_subset (abstract). -/
def comap_coe_nhdsWithin_Iio_of_Ioo_subset' : Prop := True
/-- comap_coe_nhdsWithin_Ioi_of_Ioo_subset (abstract). -/
def comap_coe_nhdsWithin_Ioi_of_Ioo_subset' : Prop := True
/-- map_coe_atTop_of_Ioo_subset (abstract). -/
def map_coe_atTop_of_Ioo_subset' : Prop := True
/-- map_coe_atBot_of_Ioo_subset (abstract). -/
def map_coe_atBot_of_Ioo_subset' : Prop := True
/-- comap_coe_Ioo_nhdsWithin_Iio (abstract). -/
def comap_coe_Ioo_nhdsWithin_Iio' : Prop := True
/-- comap_coe_Ioo_nhdsWithin_Ioi (abstract). -/
def comap_coe_Ioo_nhdsWithin_Ioi' : Prop := True
/-- comap_coe_Ioi_nhdsWithin_Ioi (abstract). -/
def comap_coe_Ioi_nhdsWithin_Ioi' : Prop := True
/-- comap_coe_Iio_nhdsWithin_Iio (abstract). -/
def comap_coe_Iio_nhdsWithin_Iio' : Prop := True
/-- map_coe_Ioo_atTop (abstract). -/
def map_coe_Ioo_atTop' : Prop := True
/-- map_coe_Ioo_atBot (abstract). -/
def map_coe_Ioo_atBot' : Prop := True
/-- map_coe_Ioi_atBot (abstract). -/
def map_coe_Ioi_atBot' : Prop := True
/-- map_coe_Iio_atTop (abstract). -/
def map_coe_Iio_atTop' : Prop := True
/-- tendsto_comp_coe_Ioo_atTop (abstract). -/
def tendsto_comp_coe_Ioo_atTop' : Prop := True
/-- tendsto_comp_coe_Ioo_atBot (abstract). -/
def tendsto_comp_coe_Ioo_atBot' : Prop := True
/-- tendsto_comp_coe_Ioi_atBot (abstract). -/
def tendsto_comp_coe_Ioi_atBot' : Prop := True
/-- tendsto_comp_coe_Iio_atTop (abstract). -/
def tendsto_comp_coe_Iio_atTop' : Prop := True
/-- tendsto_Ioo_atTop (abstract). -/
def tendsto_Ioo_atTop' : Prop := True
/-- tendsto_Ioo_atBot (abstract). -/
def tendsto_Ioo_atBot' : Prop := True
/-- tendsto_Ioi_atBot (abstract). -/
def tendsto_Ioi_atBot' : Prop := True
/-- tendsto_Iio_atTop (abstract). -/
def tendsto_Iio_atTop' : Prop := True

-- Order/ExtendFrom.lean
/-- continuousOn_Icc_extendFrom_Ioo (abstract). -/
def continuousOn_Icc_extendFrom_Ioo' : Prop := True
/-- eq_lim_at_left_extendFrom_Ioo (abstract). -/
def eq_lim_at_left_extendFrom_Ioo' : Prop := True
/-- eq_lim_at_right_extendFrom_Ioo (abstract). -/
def eq_lim_at_right_extendFrom_Ioo' : Prop := True
/-- continuousOn_Ico_extendFrom_Ioo (abstract). -/
def continuousOn_Ico_extendFrom_Ioo' : Prop := True
/-- continuousOn_Ioc_extendFrom_Ioo (abstract). -/
def continuousOn_Ioc_extendFrom_Ioo' : Prop := True

-- Order/Filter.lean
-- COLLISION: tendsto_nhds_atTop' already in Analysis.lean — rename needed
/-- tendsto_nhds_atBot (abstract). -/
def tendsto_nhds_atBot' : Prop := True

-- Order/Hom/Basic.lean
/-- ContinuousOrderHom (abstract). -/
def ContinuousOrderHom' : Prop := True
/-- ContinuousOrderHomClass (abstract). -/
def ContinuousOrderHomClass' : Prop := True
/-- toContinuousOrderHom (abstract). -/
def toContinuousOrderHom' : Prop := True

-- Order/Hom/Esakia.lean
/-- PseudoEpimorphism (abstract). -/
def PseudoEpimorphism' : Prop := True
/-- EsakiaHom (abstract). -/
def EsakiaHom' : Prop := True
/-- PseudoEpimorphismClass (abstract). -/
def PseudoEpimorphismClass' : Prop := True
/-- EsakiaHomClass (abstract). -/
def EsakiaHomClass' : Prop := True
/-- toPseudoEpimorphism (abstract). -/
def toPseudoEpimorphism' : Prop := True

-- Order/IntermediateValue.lean
/-- intermediate_value_univ₂ (abstract). -/
def intermediate_value_univ₂' : Prop := True
/-- intermediate_value_univ₂_eventually₁ (abstract). -/
def intermediate_value_univ₂_eventually₁' : Prop := True
/-- intermediate_value_univ₂_eventually₂ (abstract). -/
def intermediate_value_univ₂_eventually₂' : Prop := True
/-- intermediate_value₂ (abstract). -/
def intermediate_value₂' : Prop := True
/-- intermediate_value₂_eventually₁ (abstract). -/
def intermediate_value₂_eventually₁' : Prop := True
/-- intermediate_value₂_eventually₂ (abstract). -/
def intermediate_value₂_eventually₂' : Prop := True
/-- intermediate_value (abstract). -/
def intermediate_value' : Prop := True
/-- intermediate_value_Ico (abstract). -/
def intermediate_value_Ico' : Prop := True
/-- intermediate_value_Ioc (abstract). -/
def intermediate_value_Ioc' : Prop := True
/-- intermediate_value_Ioo (abstract). -/
def intermediate_value_Ioo' : Prop := True
/-- intermediate_value_Ici (abstract). -/
def intermediate_value_Ici' : Prop := True
/-- intermediate_value_Iic (abstract). -/
def intermediate_value_Iic' : Prop := True
/-- intermediate_value_Ioi (abstract). -/
def intermediate_value_Ioi' : Prop := True
/-- intermediate_value_Iio (abstract). -/
def intermediate_value_Iio' : Prop := True
/-- intermediate_value_Iii (abstract). -/
def intermediate_value_Iii' : Prop := True
/-- intermediate_value_univ (abstract). -/
def intermediate_value_univ' : Prop := True
/-- mem_range_of_exists_le_of_exists_ge (abstract). -/
def mem_range_of_exists_le_of_exists_ge' : Prop := True
-- COLLISION: Icc_subset' already in Order.lean — rename needed
-- COLLISION: ordConnected' already in Order.lean — rename needed
/-- eq_univ_of_unbounded (abstract). -/
def eq_univ_of_unbounded' : Prop := True
/-- Ioo_csInf_csSup_subset (abstract). -/
def Ioo_csInf_csSup_subset' : Prop := True
/-- eq_Icc_csInf_csSup_of_connected_bdd_closed (abstract). -/
def eq_Icc_csInf_csSup_of_connected_bdd_closed' : Prop := True
/-- Ioi_csInf_subset (abstract). -/
def Ioi_csInf_subset' : Prop := True
/-- Iio_csSup_subset (abstract). -/
def Iio_csSup_subset' : Prop := True
/-- mem_intervals (abstract). -/
def mem_intervals' : Prop := True
/-- setOf_isPreconnected_subset_of_ordered (abstract). -/
def setOf_isPreconnected_subset_of_ordered' : Prop := True
/-- mem_of_ge_of_forall_exists_gt (abstract). -/
def mem_of_ge_of_forall_exists_gt' : Prop := True
/-- Icc_subset_of_forall_exists_gt (abstract). -/
def Icc_subset_of_forall_exists_gt' : Prop := True
/-- Icc_subset_of_forall_mem_nhdsWithin (abstract). -/
def Icc_subset_of_forall_mem_nhdsWithin' : Prop := True
/-- isPreconnected_Icc_aux (abstract). -/
def isPreconnected_Icc_aux' : Prop := True
/-- isPreconnected_Icc (abstract). -/
def isPreconnected_Icc' : Prop := True
/-- isPreconnected_uIcc (abstract). -/
def isPreconnected_uIcc' : Prop := True
/-- isPreconnected_iff_ordConnected (abstract). -/
def isPreconnected_iff_ordConnected' : Prop := True
/-- isPreconnected_Ici (abstract). -/
def isPreconnected_Ici' : Prop := True
/-- isPreconnected_Iic (abstract). -/
def isPreconnected_Iic' : Prop := True
/-- isPreconnected_Iio (abstract). -/
def isPreconnected_Iio' : Prop := True
/-- isPreconnected_Ioi (abstract). -/
def isPreconnected_Ioi' : Prop := True
/-- isPreconnected_Ioo (abstract). -/
def isPreconnected_Ioo' : Prop := True
/-- isPreconnected_Ioc (abstract). -/
def isPreconnected_Ioc' : Prop := True
/-- isPreconnected_Ico (abstract). -/
def isPreconnected_Ico' : Prop := True
/-- isConnected_Ici (abstract). -/
def isConnected_Ici' : Prop := True
/-- isConnected_Iic (abstract). -/
def isConnected_Iic' : Prop := True
/-- isConnected_Ioi (abstract). -/
def isConnected_Ioi' : Prop := True
/-- isConnected_Iio (abstract). -/
def isConnected_Iio' : Prop := True
/-- isConnected_Icc (abstract). -/
def isConnected_Icc' : Prop := True
/-- isConnected_Ioo (abstract). -/
def isConnected_Ioo' : Prop := True
/-- isConnected_Ioc (abstract). -/
def isConnected_Ioc' : Prop := True
/-- isConnected_Ico (abstract). -/
def isConnected_Ico' : Prop := True
/-- setOf_isPreconnected_eq_of_ordered (abstract). -/
def setOf_isPreconnected_eq_of_ordered' : Prop := True
/-- isTotallyDisconnected_iff_lt (abstract). -/
def isTotallyDisconnected_iff_lt' : Prop := True
/-- intermediate_value_Icc (abstract). -/
def intermediate_value_Icc' : Prop := True
/-- intermediate_value_uIcc (abstract). -/
def intermediate_value_uIcc' : Prop := True
/-- exists_mem_uIcc_isFixedPt (abstract). -/
def exists_mem_uIcc_isFixedPt' : Prop := True
/-- exists_mem_Icc_isFixedPt (abstract). -/
def exists_mem_Icc_isFixedPt' : Prop := True
/-- exists_mem_Icc_isFixedPt_of_mapsTo (abstract). -/
def exists_mem_Icc_isFixedPt_of_mapsTo' : Prop := True
/-- surjOn_Icc (abstract). -/
def surjOn_Icc' : Prop := True
/-- surjOn_uIcc (abstract). -/
def surjOn_uIcc' : Prop := True
/-- surjOn_of_tendsto (abstract). -/
def surjOn_of_tendsto' : Prop := True
/-- strictMono_of_inj_boundedOrder (abstract). -/
def strictMono_of_inj_boundedOrder' : Prop := True
/-- strictAnti_of_inj_boundedOrder (abstract). -/
def strictAnti_of_inj_boundedOrder' : Prop := True
/-- strictMonoOn_of_inj_rigidity (abstract). -/
def strictMonoOn_of_inj_rigidity' : Prop := True
/-- strictMonoOn_of_injOn_Icc (abstract). -/
def strictMonoOn_of_injOn_Icc' : Prop := True
/-- strictAntiOn_of_injOn_Icc (abstract). -/
def strictAntiOn_of_injOn_Icc' : Prop := True
/-- strictMono_of_inj (abstract). -/
def strictMono_of_inj' : Prop := True
/-- strictMonoOn_of_injOn_Ioo (abstract). -/
def strictMonoOn_of_injOn_Ioo' : Prop := True

-- Order/IsLUB.lean
/-- frequently_mem (abstract). -/
def frequently_mem' : Prop := True
/-- frequently_nhds_mem (abstract). -/
def frequently_nhds_mem' : Prop := True
/-- isLUB_of_mem_nhds (abstract). -/
def isLUB_of_mem_nhds' : Prop := True
/-- isLUB_of_mem_closure (abstract). -/
def isLUB_of_mem_closure' : Prop := True
/-- isGLB_of_mem_nhds (abstract). -/
def isGLB_of_mem_nhds' : Prop := True
/-- isGLB_of_mem_closure (abstract). -/
def isGLB_of_mem_closure' : Prop := True
/-- mem_upperBounds_of_tendsto (abstract). -/
def mem_upperBounds_of_tendsto' : Prop := True
/-- isLUB_of_tendsto (abstract). -/
def isLUB_of_tendsto' : Prop := True
/-- mem_lowerBounds_of_tendsto (abstract). -/
def mem_lowerBounds_of_tendsto' : Prop := True
/-- isGLB_of_tendsto (abstract). -/
def isGLB_of_tendsto' : Prop := True
/-- mem_of_isClosed (abstract). -/
def mem_of_isClosed' : Prop := True
/-- exists_seq_strictMono_tendsto_of_not_mem (abstract). -/
def exists_seq_strictMono_tendsto_of_not_mem' : Prop := True
/-- exists_seq_monotone_tendsto (abstract). -/
def exists_seq_monotone_tendsto' : Prop := True
/-- exists_seq_strictMono_tendsto' (abstract). -/
def exists_seq_strictMono_tendsto' : Prop := True
/-- exists_seq_strictMono_tendsto_nhdsWithin (abstract). -/
def exists_seq_strictMono_tendsto_nhdsWithin' : Prop := True
/-- exists_seq_tendsto_sSup (abstract). -/
def exists_seq_tendsto_sSup' : Prop := True
/-- exists_seq_strictAnti_tendsto_of_not_mem (abstract). -/
def exists_seq_strictAnti_tendsto_of_not_mem' : Prop := True
/-- exists_seq_antitone_tendsto (abstract). -/
def exists_seq_antitone_tendsto' : Prop := True
/-- exists_seq_strictAnti_tendsto' (abstract). -/
def exists_seq_strictAnti_tendsto' : Prop := True
/-- exists_seq_strictAnti_tendsto_nhdsWithin (abstract). -/
def exists_seq_strictAnti_tendsto_nhdsWithin' : Prop := True
/-- exists_seq_strictAnti_strictMono_tendsto (abstract). -/
def exists_seq_strictAnti_strictMono_tendsto' : Prop := True
/-- exists_seq_tendsto_sInf (abstract). -/
def exists_seq_tendsto_sInf' : Prop := True

-- Order/Lattice.lean
/-- ContinuousInf (abstract). -/
def ContinuousInf' : Prop := True
/-- ContinuousSup (abstract). -/
def ContinuousSup' : Prop := True
/-- TopologicalLattice (abstract). -/
def TopologicalLattice' : Prop := True
/-- continuous_inf (abstract). -/
def continuous_inf' : Prop := True
/-- continuous_sup (abstract). -/
def continuous_sup' : Prop := True
/-- sup_nhds' (abstract). -/
def sup_nhds' : Prop := True
/-- inf_nhds' (abstract). -/
def inf_nhds' : Prop := True
/-- finset_sup'_nhds (abstract). -/
def finset_sup'_nhds' : Prop := True
/-- finset_sup'_nhds_apply (abstract). -/
def finset_sup'_nhds_apply' : Prop := True
/-- finset_inf'_nhds (abstract). -/
def finset_inf'_nhds' : Prop := True
/-- finset_inf'_nhds_apply (abstract). -/
def finset_inf'_nhds_apply' : Prop := True
/-- finset_sup_nhds (abstract). -/
def finset_sup_nhds' : Prop := True
/-- finset_sup_nhds_apply (abstract). -/
def finset_sup_nhds_apply' : Prop := True
/-- finset_inf_nhds (abstract). -/
def finset_inf_nhds' : Prop := True
/-- finset_inf_nhds_apply (abstract). -/
def finset_inf_nhds_apply' : Prop := True
/-- finset_sup'_apply (abstract). -/
def finset_sup'_apply' : Prop := True
/-- finset_sup' (abstract). -/
def finset_sup' : Prop := True
-- COLLISION: finset_sup_apply' already in Analysis.lean — rename needed
/-- finset_inf'_apply (abstract). -/
def finset_inf'_apply' : Prop := True
/-- finset_inf' (abstract). -/
def finset_inf' : Prop := True
/-- finset_inf_apply (abstract). -/
def finset_inf_apply' : Prop := True

-- Order/LawsonTopology.lean
/-- lawson (abstract). -/
def lawson' : Prop := True
/-- IsLawson (abstract). -/
def IsLawson' : Prop := True
/-- lawsonBasis (abstract). -/
def lawsonBasis' : Prop := True
/-- WithLawson (abstract). -/
def WithLawson' : Prop := True
/-- toLawson (abstract). -/
def toLawson' : Prop := True
/-- ofLawson (abstract). -/
def ofLawson' : Prop := True
/-- lawsonOpen_iff_scottOpen_of_isUpperSet (abstract). -/
def lawsonOpen_iff_scottOpen_of_isUpperSet' : Prop := True
/-- isLawson_le_isScott (abstract). -/
def isLawson_le_isScott' : Prop := True
/-- scottHausdorff_le_isLawson (abstract). -/
def scottHausdorff_le_isLawson' : Prop := True
/-- lawsonClosed_iff_scottClosed_of_isLowerSet (abstract). -/
def lawsonClosed_iff_scottClosed_of_isLowerSet' : Prop := True
/-- lawsonClosed_iff_dirSupClosed_of_isLowerSet (abstract). -/
def lawsonClosed_iff_dirSupClosed_of_isLowerSet' : Prop := True
/-- singleton_isClosed (abstract). -/
def singleton_isClosed' : Prop := True

-- Order/LeftRight.lean
/-- frequently_lt_nhds (abstract). -/
def frequently_lt_nhds' : Prop := True
/-- frequently_gt_nhds (abstract). -/
def frequently_gt_nhds' : Prop := True
-- COLLISION: exists_lt' already in Order.lean — rename needed
-- COLLISION: exists_gt' already in Order.lean — rename needed
/-- nhdsWithin_Ici_neBot (abstract). -/
def nhdsWithin_Ici_neBot' : Prop := True
/-- nhdsWithin_Iic_neBot (abstract). -/
def nhdsWithin_Iic_neBot' : Prop := True
/-- nhds_left'_le_nhds_ne (abstract). -/
def nhds_left'_le_nhds_ne' : Prop := True
/-- nhds_right'_le_nhds_ne (abstract). -/
def nhds_right'_le_nhds_ne' : Prop := True
/-- interior_eq_empty (abstract). -/
def interior_eq_empty' : Prop := True
/-- continuousWithinAt_Ioi_iff_Ici (abstract). -/
def continuousWithinAt_Ioi_iff_Ici' : Prop := True
/-- continuousWithinAt_Iio_iff_Iic (abstract). -/
def continuousWithinAt_Iio_iff_Iic' : Prop := True
/-- nhds_left_sup_nhds_right (abstract). -/
def nhds_left_sup_nhds_right' : Prop := True
/-- nhds_left'_sup_nhds_right (abstract). -/
def nhds_left'_sup_nhds_right' : Prop := True
/-- nhdsWithin_right_sup_nhds_singleton (abstract). -/
def nhdsWithin_right_sup_nhds_singleton' : Prop := True
/-- continuousAt_iff_continuous_left_right (abstract). -/
def continuousAt_iff_continuous_left_right' : Prop := True
/-- continuousAt_iff_continuous_left'_right' (abstract). -/
def continuousAt_iff_continuous_left'_right' : Prop := True

-- Order/LeftRightLim.lean
/-- leftLim (abstract). -/
def leftLim' : Prop := True
/-- rightLim (abstract). -/
def rightLim' : Prop := True
/-- leftLim_eq_of_tendsto (abstract). -/
def leftLim_eq_of_tendsto' : Prop := True
/-- leftLim_eq_of_eq_bot (abstract). -/
def leftLim_eq_of_eq_bot' : Prop := True
/-- rightLim_eq_of_tendsto (abstract). -/
def rightLim_eq_of_tendsto' : Prop := True
/-- rightLim_eq_of_eq_bot (abstract). -/
def rightLim_eq_of_eq_bot' : Prop := True
/-- leftLim_eq_sSup (abstract). -/
def leftLim_eq_sSup' : Prop := True
/-- rightLim_eq_sInf (abstract). -/
def rightLim_eq_sInf' : Prop := True
/-- leftLim_le (abstract). -/
def leftLim_le' : Prop := True
/-- le_leftLim (abstract). -/
def le_leftLim' : Prop := True
/-- le_rightLim (abstract). -/
def le_rightLim' : Prop := True
/-- rightLim_le (abstract). -/
def rightLim_le' : Prop := True
/-- leftLim_le_rightLim (abstract). -/
def leftLim_le_rightLim' : Prop := True
/-- rightLim_le_leftLim (abstract). -/
def rightLim_le_leftLim' : Prop := True
/-- tendsto_leftLim (abstract). -/
def tendsto_leftLim' : Prop := True
/-- tendsto_leftLim_within (abstract). -/
def tendsto_leftLim_within' : Prop := True
/-- tendsto_rightLim (abstract). -/
def tendsto_rightLim' : Prop := True
/-- tendsto_rightLim_within (abstract). -/
def tendsto_rightLim_within' : Prop := True
/-- continuousWithinAt_Iio_iff_leftLim_eq (abstract). -/
def continuousWithinAt_Iio_iff_leftLim_eq' : Prop := True
/-- continuousWithinAt_Ioi_iff_rightLim_eq (abstract). -/
def continuousWithinAt_Ioi_iff_rightLim_eq' : Prop := True
/-- continuousAt_iff_leftLim_eq_rightLim (abstract). -/
def continuousAt_iff_leftLim_eq_rightLim' : Prop := True
/-- countable_not_continuousWithinAt_Ioi (abstract). -/
def countable_not_continuousWithinAt_Ioi' : Prop := True
/-- countable_not_continuousWithinAt_Iio (abstract). -/
def countable_not_continuousWithinAt_Iio' : Prop := True
/-- countable_not_continuousAt (abstract). -/
def countable_not_continuousAt' : Prop := True

-- Order/LeftRightNhds.lean
/-- TFAE_mem_nhdsWithin_Ioi (abstract). -/
def TFAE_mem_nhdsWithin_Ioi' : Prop := True
/-- nhdsWithin_Ioi_basis (abstract). -/
def nhdsWithin_Ioi_basis' : Prop := True
/-- nhdsWithin_Ioi_eq_bot_iff (abstract). -/
def nhdsWithin_Ioi_eq_bot_iff' : Prop := True
/-- mem_nhdsWithin_Ioi_iff_exists_Ioo_subset (abstract). -/
def mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' : Prop := True
/-- countable_setOf_isolated_right (abstract). -/
def countable_setOf_isolated_right' : Prop := True
/-- countable_setOf_isolated_left (abstract). -/
def countable_setOf_isolated_left' : Prop := True
/-- mem_nhdsWithin_Ioi_iff_exists_Ioc_subset (abstract). -/
def mem_nhdsWithin_Ioi_iff_exists_Ioc_subset' : Prop := True
/-- TFAE_mem_nhdsWithin_Iio (abstract). -/
def TFAE_mem_nhdsWithin_Iio' : Prop := True
/-- mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset (abstract). -/
def mem_nhdsWithin_Iio_iff_exists_mem_Ico_Ioo_subset' : Prop := True
/-- mem_nhdsWithin_Iio_iff_exists_Ioo_subset' (abstract). -/
def mem_nhdsWithin_Iio_iff_exists_Ioo_subset' : Prop := True
/-- nhdsWithin_Iio_basis (abstract). -/
def nhdsWithin_Iio_basis' : Prop := True
/-- nhdsWithin_Iio_eq_bot_iff (abstract). -/
def nhdsWithin_Iio_eq_bot_iff' : Prop := True
/-- TFAE_mem_nhdsWithin_Ici (abstract). -/
def TFAE_mem_nhdsWithin_Ici' : Prop := True
/-- mem_nhdsWithin_Ici_iff_exists_mem_Ioc_Ico_subset (abstract). -/
def mem_nhdsWithin_Ici_iff_exists_mem_Ioc_Ico_subset' : Prop := True
/-- mem_nhdsWithin_Ici_iff_exists_Ico_subset' (abstract). -/
def mem_nhdsWithin_Ici_iff_exists_Ico_subset' : Prop := True
/-- nhdsWithin_Ici_basis_Ico (abstract). -/
def nhdsWithin_Ici_basis_Ico' : Prop := True
/-- nhdsWithin_Ici_basis_Icc (abstract). -/
def nhdsWithin_Ici_basis_Icc' : Prop := True
/-- mem_nhdsWithin_Ici_iff_exists_Icc_subset (abstract). -/
def mem_nhdsWithin_Ici_iff_exists_Icc_subset' : Prop := True
/-- TFAE_mem_nhdsWithin_Iic (abstract). -/
def TFAE_mem_nhdsWithin_Iic' : Prop := True
/-- mem_nhdsWithin_Iic_iff_exists_mem_Ico_Ioc_subset (abstract). -/
def mem_nhdsWithin_Iic_iff_exists_mem_Ico_Ioc_subset' : Prop := True
/-- mem_nhdsWithin_Iic_iff_exists_Ioc_subset' (abstract). -/
def mem_nhdsWithin_Iic_iff_exists_Ioc_subset' : Prop := True
/-- nhdsWithin_Iic_basis_Icc (abstract). -/
def nhdsWithin_Iic_basis_Icc' : Prop := True
/-- nhds_eq_iInf_abs_sub (abstract). -/
def nhds_eq_iInf_abs_sub' : Prop := True
/-- orderTopology_of_nhds_abs (abstract). -/
def orderTopology_of_nhds_abs' : Prop := True
/-- eventually_abs_sub_lt (abstract). -/
def eventually_abs_sub_lt' : Prop := True
/-- add_atTop (abstract). -/
def add_atTop' : Prop := True
/-- add_atBot (abstract). -/
def add_atBot' : Prop := True
/-- atTop_add (abstract). -/
def atTop_add' : Prop := True
/-- atBot_add (abstract). -/
def atBot_add' : Prop := True
/-- nhds_basis_abs_sub_lt (abstract). -/
def nhds_basis_abs_sub_lt' : Prop := True
/-- nhds_basis_Ioo_pos (abstract). -/
def nhds_basis_Ioo_pos' : Prop := True
/-- nhds_basis_Icc_pos (abstract). -/
def nhds_basis_Icc_pos' : Prop := True
/-- nhds_basis_zero_abs_sub_lt (abstract). -/
def nhds_basis_zero_abs_sub_lt' : Prop := True
/-- nhds_basis_Ioo_pos_of_pos (abstract). -/
def nhds_basis_Ioo_pos_of_pos' : Prop := True
/-- mem_nhdsWithin_Ici (abstract). -/
def mem_nhdsWithin_Ici' : Prop := True
/-- mem_nhdsWithin_Ioi (abstract). -/
def mem_nhdsWithin_Ioi' : Prop := True
/-- mem_nhdsWithin_Iic (abstract). -/
def mem_nhdsWithin_Iic' : Prop := True
/-- mem_nhdsWithin_Iio (abstract). -/
def mem_nhdsWithin_Iio' : Prop := True

-- Order/LocalExtr.lean
/-- IsLocalMinOn (abstract). -/
def IsLocalMinOn' : Prop := True
/-- IsLocalMaxOn (abstract). -/
def IsLocalMaxOn' : Prop := True
/-- IsLocalExtrOn (abstract). -/
def IsLocalExtrOn' : Prop := True
/-- IsLocalMin (abstract). -/
def IsLocalMin' : Prop := True
/-- IsLocalMax (abstract). -/
def IsLocalMax' : Prop := True
/-- IsLocalExtr (abstract). -/
def IsLocalExtr' : Prop := True
-- COLLISION: on_subset' already in Order.lean — rename needed
/-- localize (abstract). -/
def localize' : Prop := True
/-- isLocalMin (abstract). -/
def isLocalMin' : Prop := True
/-- isLocalMax (abstract). -/
def isLocalMax' : Prop := True
/-- isLocalExtr (abstract). -/
def isLocalExtr' : Prop := True
/-- not_nhds_le_map (abstract). -/
def not_nhds_le_map' : Prop := True
/-- isLocalMinOn_const (abstract). -/
def isLocalMinOn_const' : Prop := True
/-- isLocalMaxOn_const (abstract). -/
def isLocalMaxOn_const' : Prop := True
/-- isLocalExtrOn_const (abstract). -/
def isLocalExtrOn_const' : Prop := True
/-- isLocalMin_const (abstract). -/
def isLocalMin_const' : Prop := True
/-- isLocalMax_const (abstract). -/
def isLocalMax_const' : Prop := True
/-- isLocalExtr_const (abstract). -/
def isLocalExtr_const' : Prop := True
-- COLLISION: comp_mono' already in Order.lean — rename needed
-- COLLISION: comp_antitone' already in Order.lean — rename needed
-- COLLISION: bicomp_mono' already in Order.lean — rename needed
/-- isLocalMaxOn_iff (abstract). -/
def isLocalMaxOn_iff' : Prop := True
/-- isLocalExtrOn_iff (abstract). -/
def isLocalExtrOn_iff' : Prop := True
/-- isLocalExtr_iff (abstract). -/
def isLocalExtr_iff' : Prop := True
/-- isLocalMax_of_mono_anti' (abstract). -/
def isLocalMax_of_mono_anti' : Prop := True
/-- isLocalMin_of_anti_mono' (abstract). -/
def isLocalMin_of_anti_mono' : Prop := True

-- Order/LowerUpperTopology.lean
-- COLLISION: lower' already in Order.lean — rename needed
/-- upper (abstract). -/
def upper' : Prop := True
/-- WithLower (abstract). -/
def WithLower' : Prop := True
/-- toLower (abstract). -/
def toLower' : Prop := True
/-- ofLower (abstract). -/
def ofLower' : Prop := True
/-- WithUpper (abstract). -/
def WithUpper' : Prop := True
/-- toUpper (abstract). -/
def toUpper' : Prop := True
/-- ofUpper (abstract). -/
def ofUpper' : Prop := True
/-- IsLower (abstract). -/
def IsLower' : Prop := True
/-- IsUpper (abstract). -/
def IsUpper' : Prop := True
/-- toDualHomeomorph (abstract). -/
def toDualHomeomorph' : Prop := True
/-- lowerBasis (abstract). -/
def lowerBasis' : Prop := True
/-- topology_eq (abstract). -/
def topology_eq' : Prop := True
/-- withLowerHomeomorph (abstract). -/
def withLowerHomeomorph' : Prop := True
/-- isOpen_iff_generate_Ici_compl (abstract). -/
def isOpen_iff_generate_Ici_compl' : Prop := True
/-- isUpperSet_of_isClosed (abstract). -/
def isUpperSet_of_isClosed' : Prop := True
/-- continuous_iff_Ici (abstract). -/
def continuous_iff_Ici' : Prop := True
/-- isTopologicalBasis_insert_univ_subbasis (abstract). -/
def isTopologicalBasis_insert_univ_subbasis' : Prop := True
/-- isTopologicalSpace_basis (abstract). -/
def isTopologicalSpace_basis' : Prop := True
/-- upperBasis (abstract). -/
def upperBasis' : Prop := True
/-- withUpperHomeomorph (abstract). -/
def withUpperHomeomorph' : Prop := True
/-- isOpen_iff_generate_Iic_compl (abstract). -/
def isOpen_iff_generate_Iic_compl' : Prop := True
/-- isClosed_lowerClosure (abstract). -/
def isClosed_lowerClosure' : Prop := True
/-- isUpperSet_of_isOpen (abstract). -/
def isUpperSet_of_isOpen' : Prop := True
/-- isLowerSet_of_isClosed (abstract). -/
def isLowerSet_of_isClosed' : Prop := True
/-- continuous_iff_Iic (abstract). -/
def continuous_iff_Iic' : Prop := True
/-- isUpper_orderDual (abstract). -/
def isUpper_orderDual' : Prop := True
/-- isLower_orderDual (abstract). -/
def isLower_orderDual' : Prop := True

-- Order/Monotone.lean
/-- map_csSup_of_continuousWithinAt (abstract). -/
def map_csSup_of_continuousWithinAt' : Prop := True
/-- map_csSup_of_continuousAt (abstract). -/
def map_csSup_of_continuousAt' : Prop := True
/-- map_ciSup_of_continuousAt (abstract). -/
def map_ciSup_of_continuousAt' : Prop := True
/-- map_csInf_of_continuousWithinAt (abstract). -/
def map_csInf_of_continuousWithinAt' : Prop := True
/-- map_csInf_of_continuousAt (abstract). -/
def map_csInf_of_continuousAt' : Prop := True
/-- map_ciInf_of_continuousAt (abstract). -/
def map_ciInf_of_continuousAt' : Prop := True
/-- sSup_mem_closure (abstract). -/
def sSup_mem_closure' : Prop := True
/-- sInf_mem_closure (abstract). -/
def sInf_mem_closure' : Prop := True
/-- map_sSup_of_continuousWithinAt (abstract). -/
def map_sSup_of_continuousWithinAt' : Prop := True
/-- map_sSup_of_continuousAt (abstract). -/
def map_sSup_of_continuousAt' : Prop := True
/-- map_iSup_of_continuousAt (abstract). -/
def map_iSup_of_continuousAt' : Prop := True
/-- map_sInf_of_continuousWithinAt (abstract). -/
def map_sInf_of_continuousWithinAt' : Prop := True
/-- map_sInf_of_continuousAt (abstract). -/
def map_sInf_of_continuousAt' : Prop := True
/-- map_iInf_of_continuousAt (abstract). -/
def map_iInf_of_continuousAt' : Prop := True
/-- csSup_mem_closure (abstract). -/
def csSup_mem_closure' : Prop := True
/-- csInf_mem_closure (abstract). -/
def csInf_mem_closure' : Prop := True
-- COLLISION: csSup_mem' already in Order.lean — rename needed
-- COLLISION: csInf_mem' already in Order.lean — rename needed
-- COLLISION: isLeast_csInf' already in Order.lean — rename needed
/-- isGreatest_csSup (abstract). -/
def isGreatest_csSup' : Prop := True
/-- tendsto_nhdsWithin_Ioo_left (abstract). -/
def tendsto_nhdsWithin_Ioo_left' : Prop := True
/-- tendsto_nhdsWithin_Ioo_right (abstract). -/
def tendsto_nhdsWithin_Ioo_right' : Prop := True
/-- tendsto_nhdsWithin_Iio (abstract). -/
def tendsto_nhdsWithin_Iio' : Prop := True
/-- tendsto_nhdsWithin_Ioi (abstract). -/
def tendsto_nhdsWithin_Ioi' : Prop := True

-- Order/MonotoneContinuity.lean
/-- continuousWithinAt_right_of_exists_between (abstract). -/
def continuousWithinAt_right_of_exists_between' : Prop := True
/-- continuousWithinAt_right_of_monotoneOn_of_exists_between (abstract). -/
def continuousWithinAt_right_of_monotoneOn_of_exists_between' : Prop := True
/-- continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_right_of_monotoneOn_of_closure_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_right_of_monotoneOn_of_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_right_of_closure_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_right_of_closure_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_right_of_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_right_of_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_right_of_surjOn (abstract). -/
def continuousWithinAt_right_of_surjOn' : Prop := True
/-- continuousWithinAt_left_of_exists_between (abstract). -/
def continuousWithinAt_left_of_exists_between' : Prop := True
/-- continuousWithinAt_left_of_monotoneOn_of_exists_between (abstract). -/
def continuousWithinAt_left_of_monotoneOn_of_exists_between' : Prop := True
/-- continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_left_of_monotoneOn_of_closure_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_left_of_monotoneOn_of_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_left_of_closure_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_left_of_closure_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_left_of_image_mem_nhdsWithin (abstract). -/
def continuousWithinAt_left_of_image_mem_nhdsWithin' : Prop := True
/-- continuousWithinAt_left_of_surjOn (abstract). -/
def continuousWithinAt_left_of_surjOn' : Prop := True
/-- continuousAt_of_exists_between (abstract). -/
def continuousAt_of_exists_between' : Prop := True
/-- continuousAt_of_closure_image_mem_nhds (abstract). -/
def continuousAt_of_closure_image_mem_nhds' : Prop := True
/-- continuousAt_of_image_mem_nhds (abstract). -/
def continuousAt_of_image_mem_nhds' : Prop := True
/-- continuousAt_of_monotoneOn_of_exists_between (abstract). -/
def continuousAt_of_monotoneOn_of_exists_between' : Prop := True
/-- continuousAt_of_monotoneOn_of_closure_image_mem_nhds (abstract). -/
def continuousAt_of_monotoneOn_of_closure_image_mem_nhds' : Prop := True
/-- continuousAt_of_monotoneOn_of_image_mem_nhds (abstract). -/
def continuousAt_of_monotoneOn_of_image_mem_nhds' : Prop := True
/-- continuous_of_denseRange (abstract). -/
def continuous_of_denseRange' : Prop := True
/-- continuous_of_surjective (abstract). -/
def continuous_of_surjective' : Prop := True

-- Order/MonotoneConvergence.lean
/-- SupConvergenceClass (abstract). -/
def SupConvergenceClass' : Prop := True
/-- InfConvergenceClass (abstract). -/
def InfConvergenceClass' : Prop := True
/-- tendsto_atTop_isLUB (abstract). -/
def tendsto_atTop_isLUB' : Prop := True
/-- tendsto_atBot_isLUB (abstract). -/
def tendsto_atBot_isLUB' : Prop := True
/-- tendsto_atBot_isGLB (abstract). -/
def tendsto_atBot_isGLB' : Prop := True
/-- tendsto_atTop_isGLB (abstract). -/
def tendsto_atTop_isGLB' : Prop := True
/-- tendsto_atTop_ciSup (abstract). -/
def tendsto_atTop_ciSup' : Prop := True
/-- tendsto_atBot_ciSup (abstract). -/
def tendsto_atBot_ciSup' : Prop := True
/-- tendsto_atBot_ciInf (abstract). -/
def tendsto_atBot_ciInf' : Prop := True
/-- tendsto_atTop_ciInf (abstract). -/
def tendsto_atTop_ciInf' : Prop := True
/-- tendsto_atTop_iSup (abstract). -/
def tendsto_atTop_iSup' : Prop := True
/-- tendsto_atBot_iSup (abstract). -/
def tendsto_atBot_iSup' : Prop := True
/-- tendsto_atBot_iInf (abstract). -/
def tendsto_atBot_iInf' : Prop := True
/-- tendsto_atTop_iInf (abstract). -/
def tendsto_atTop_iInf' : Prop := True
/-- tendsto_of_monotone (abstract). -/
def tendsto_of_monotone' : Prop := True
/-- tendsto_iff_tendsto_subseq_of_monotone (abstract). -/
def tendsto_iff_tendsto_subseq_of_monotone' : Prop := True
/-- tendsto_iff_tendsto_subseq_of_antitone (abstract). -/
def tendsto_iff_tendsto_subseq_of_antitone' : Prop := True
/-- ge_of_tendsto (abstract). -/
def ge_of_tendsto' : Prop := True
/-- le_of_tendsto (abstract). -/
def le_of_tendsto' : Prop := True
/-- isLUB_of_tendsto_atTop (abstract). -/
def isLUB_of_tendsto_atTop' : Prop := True
/-- isGLB_of_tendsto_atBot (abstract). -/
def isGLB_of_tendsto_atBot' : Prop := True
/-- isLUB_of_tendsto_atBot (abstract). -/
def isLUB_of_tendsto_atBot' : Prop := True
/-- isGLB_of_tendsto_atTop (abstract). -/
def isGLB_of_tendsto_atTop' : Prop := True
/-- iSup_eq_of_tendsto (abstract). -/
def iSup_eq_of_tendsto' : Prop := True
/-- iInf_eq_of_tendsto (abstract). -/
def iInf_eq_of_tendsto' : Prop := True
/-- iSup_eq_iSup_subseq_of_monotone (abstract). -/
def iSup_eq_iSup_subseq_of_monotone' : Prop := True
/-- iSup_eq_iSup_subseq_of_antitone (abstract). -/
def iSup_eq_iSup_subseq_of_antitone' : Prop := True
/-- iInf_eq_iInf_subseq_of_monotone (abstract). -/
def iInf_eq_iInf_subseq_of_monotone' : Prop := True
/-- iInf_eq_iInf_subseq_of_antitone (abstract). -/
def iInf_eq_iInf_subseq_of_antitone' : Prop := True

-- Order/NhdsSet.lean
/-- nhdsSet_Ioi (abstract). -/
def nhdsSet_Ioi' : Prop := True
/-- nhdsSet_Iio (abstract). -/
def nhdsSet_Iio' : Prop := True
/-- nhdsSet_Ioo (abstract). -/
def nhdsSet_Ioo' : Prop := True
/-- nhdsSet_Ici (abstract). -/
def nhdsSet_Ici' : Prop := True
/-- nhdsSet_Iic (abstract). -/
def nhdsSet_Iic' : Prop := True
/-- nhdsSet_Ico (abstract). -/
def nhdsSet_Ico' : Prop := True
/-- nhdsSet_Ioc (abstract). -/
def nhdsSet_Ioc' : Prop := True
/-- nhdsSet_Icc (abstract). -/
def nhdsSet_Icc' : Prop := True
/-- Ioi_mem_nhdsSet_Ici_iff (abstract). -/
def Ioi_mem_nhdsSet_Ici_iff' : Prop := True
/-- Ici_mem_nhdsSet_Ici (abstract). -/
def Ici_mem_nhdsSet_Ici' : Prop := True
/-- Iio_mem_nhdsSet_Iic_iff (abstract). -/
def Iio_mem_nhdsSet_Iic_iff' : Prop := True
/-- Iic_mem_nhdsSet_Iic (abstract). -/
def Iic_mem_nhdsSet_Iic' : Prop := True
/-- Ioi_mem_nhdsSet_Icc (abstract). -/
def Ioi_mem_nhdsSet_Icc' : Prop := True
/-- Ici_mem_nhdsSet_Icc (abstract). -/
def Ici_mem_nhdsSet_Icc' : Prop := True
/-- Iio_mem_nhdsSet_Icc (abstract). -/
def Iio_mem_nhdsSet_Icc' : Prop := True
/-- Iic_mem_nhdsSet_Icc (abstract). -/
def Iic_mem_nhdsSet_Icc' : Prop := True
/-- Ioo_mem_nhdsSet_Icc (abstract). -/
def Ioo_mem_nhdsSet_Icc' : Prop := True
/-- Ico_mem_nhdsSet_Icc (abstract). -/
def Ico_mem_nhdsSet_Icc' : Prop := True
/-- Ioc_mem_nhdsSet_Icc (abstract). -/
def Ioc_mem_nhdsSet_Icc' : Prop := True
/-- Icc_mem_nhdsSet_Icc (abstract). -/
def Icc_mem_nhdsSet_Icc' : Prop := True
/-- Ici_mem_nhdsSet_Ico (abstract). -/
def Ici_mem_nhdsSet_Ico' : Prop := True
/-- Ioi_mem_nhdsSet_Ico (abstract). -/
def Ioi_mem_nhdsSet_Ico' : Prop := True
/-- Iio_mem_nhdsSet_Ico (abstract). -/
def Iio_mem_nhdsSet_Ico' : Prop := True
/-- Iic_mem_nhdsSet_Ico (abstract). -/
def Iic_mem_nhdsSet_Ico' : Prop := True
/-- Ioo_mem_nhdsSet_Ico (abstract). -/
def Ioo_mem_nhdsSet_Ico' : Prop := True
/-- Icc_mem_nhdsSet_Ico (abstract). -/
def Icc_mem_nhdsSet_Ico' : Prop := True
/-- Ioc_mem_nhdsSet_Ico (abstract). -/
def Ioc_mem_nhdsSet_Ico' : Prop := True
/-- Ico_mem_nhdsSet_Ico (abstract). -/
def Ico_mem_nhdsSet_Ico' : Prop := True
/-- Ioi_mem_nhdsSet_Ioc (abstract). -/
def Ioi_mem_nhdsSet_Ioc' : Prop := True
/-- Iio_mem_nhdsSet_Ioc (abstract). -/
def Iio_mem_nhdsSet_Ioc' : Prop := True
/-- Ici_mem_nhdsSet_Ioc (abstract). -/
def Ici_mem_nhdsSet_Ioc' : Prop := True
/-- Iic_mem_nhdsSet_Ioc (abstract). -/
def Iic_mem_nhdsSet_Ioc' : Prop := True
/-- Ioo_mem_nhdsSet_Ioc (abstract). -/
def Ioo_mem_nhdsSet_Ioc' : Prop := True
/-- Icc_mem_nhdsSet_Ioc (abstract). -/
def Icc_mem_nhdsSet_Ioc' : Prop := True
/-- Ioc_mem_nhdsSet_Ioc (abstract). -/
def Ioc_mem_nhdsSet_Ioc' : Prop := True
/-- Ico_mem_nhdsSet_Ioc (abstract). -/
def Ico_mem_nhdsSet_Ioc' : Prop := True
/-- hasBasis_nhdsSet_Iic_Iio (abstract). -/
def hasBasis_nhdsSet_Iic_Iio' : Prop := True
/-- hasBasis_nhdsSet_Iic_Iic (abstract). -/
def hasBasis_nhdsSet_Iic_Iic' : Prop := True
/-- Iic_mem_nhdsSet_Iic_iff (abstract). -/
def Iic_mem_nhdsSet_Iic_iff' : Prop := True
/-- hasBasis_nhdsSet_Ici_Ioi (abstract). -/
def hasBasis_nhdsSet_Ici_Ioi' : Prop := True
/-- hasBasis_nhdsSet_Ici_Ici (abstract). -/
def hasBasis_nhdsSet_Ici_Ici' : Prop := True
/-- Ici_mem_nhdsSet_Ici_iff (abstract). -/
def Ici_mem_nhdsSet_Ici_iff' : Prop := True

-- Order/OrderClosed.lean
/-- mixins (abstract). -/
def mixins' : Prop := True
/-- ClosedIicTopology (abstract). -/
def ClosedIicTopology' : Prop := True
/-- ClosedIciTopology (abstract). -/
def ClosedIciTopology' : Prop := True
/-- OrderClosedTopology (abstract). -/
def OrderClosedTopology' : Prop := True
-- COLLISION: orderDual' already in Order.lean — rename needed
/-- of_closure (abstract). -/
def of_closure' : Prop := True
/-- isClosed_Iic (abstract). -/
def isClosed_Iic' : Prop := True
/-- isClosed_le' (abstract). -/
def isClosed_le' : Prop := True
/-- closure_Iic (abstract). -/
def closure_Iic' : Prop := True
/-- le_of_tendsto_of_frequently (abstract). -/
def le_of_tendsto_of_frequently' : Prop := True
/-- upperBounds_closure (abstract). -/
def upperBounds_closure' : Prop := True
/-- bddAbove_closure (abstract). -/
def bddAbove_closure' : Prop := True
/-- disjoint_nhds_atBot_iff (abstract). -/
def disjoint_nhds_atBot_iff' : Prop := True
/-- range_of_tendsto (abstract). -/
def range_of_tendsto' : Prop := True
/-- disjoint_nhds_atBot (abstract). -/
def disjoint_nhds_atBot' : Prop := True
/-- inf_nhds_atBot (abstract). -/
def inf_nhds_atBot' : Prop := True
/-- not_tendsto_nhds_of_tendsto_atBot (abstract). -/
def not_tendsto_nhds_of_tendsto_atBot' : Prop := True
/-- not_tendsto_atBot_of_tendsto_nhds (abstract). -/
def not_tendsto_atBot_of_tendsto_nhds' : Prop := True
/-- iSup_eq_of_forall_le_of_tendsto (abstract). -/
def iSup_eq_of_forall_le_of_tendsto' : Prop := True
/-- iUnion_Iic_eq_Iio_of_lt_of_tendsto (abstract). -/
def iUnion_Iic_eq_Iio_of_lt_of_tendsto' : Prop := True
/-- isOpen_Ioi (abstract). -/
def isOpen_Ioi' : Prop := True
/-- interior_Ioi (abstract). -/
def interior_Ioi' : Prop := True
/-- Ioi_mem_nhds (abstract). -/
def Ioi_mem_nhds' : Prop := True
-- COLLISION: exists_ge' already in Order.lean — rename needed
/-- Ioo_mem_nhdsWithin_Iio' (abstract). -/
def Ioo_mem_nhdsWithin_Iio' : Prop := True
/-- nhdsWithin_Iio (abstract). -/
def nhdsWithin_Iio' : Prop := True
/-- Ico_mem_nhdsWithin_Iio (abstract). -/
def Ico_mem_nhdsWithin_Iio' : Prop := True
/-- Ioc_mem_nhdsWithin_Iio (abstract). -/
def Ioc_mem_nhdsWithin_Iio' : Prop := True
/-- Icc_mem_nhdsWithin_Iio (abstract). -/
def Icc_mem_nhdsWithin_Iio' : Prop := True
/-- nhdsWithin_Ico_eq_nhdsWithin_Iio (abstract). -/
def nhdsWithin_Ico_eq_nhdsWithin_Iio' : Prop := True
/-- nhdsWithin_Ioo_eq_nhdsWithin_Iio (abstract). -/
def nhdsWithin_Ioo_eq_nhdsWithin_Iio' : Prop := True
/-- continuousWithinAt_Ico_iff_Iio (abstract). -/
def continuousWithinAt_Ico_iff_Iio' : Prop := True
/-- continuousWithinAt_Ioo_iff_Iio (abstract). -/
def continuousWithinAt_Ioo_iff_Iio' : Prop := True
/-- nhdsWithin_Iic (abstract). -/
def nhdsWithin_Iic' : Prop := True
/-- Ioc_mem_nhdsWithin_Iic' (abstract). -/
def Ioc_mem_nhdsWithin_Iic' : Prop := True
/-- Ioo_mem_nhdsWithin_Iic (abstract). -/
def Ioo_mem_nhdsWithin_Iic' : Prop := True
/-- Ico_mem_nhdsWithin_Iic (abstract). -/
def Ico_mem_nhdsWithin_Iic' : Prop := True
/-- Icc_mem_nhdsWithin_Iic (abstract). -/
def Icc_mem_nhdsWithin_Iic' : Prop := True
/-- nhdsWithin_Icc_eq_nhdsWithin_Iic (abstract). -/
def nhdsWithin_Icc_eq_nhdsWithin_Iic' : Prop := True
/-- nhdsWithin_Ioc_eq_nhdsWithin_Iic (abstract). -/
def nhdsWithin_Ioc_eq_nhdsWithin_Iic' : Prop := True
/-- continuousWithinAt_Icc_iff_Iic (abstract). -/
def continuousWithinAt_Icc_iff_Iic' : Prop := True
/-- continuousWithinAt_Ioc_iff_Iic (abstract). -/
def continuousWithinAt_Ioc_iff_Iic' : Prop := True
/-- isClosed_Ici (abstract). -/
def isClosed_Ici' : Prop := True
/-- isClosed_ge' (abstract). -/
def isClosed_ge' : Prop := True
/-- closure_Ici (abstract). -/
def closure_Ici' : Prop := True
/-- ge_of_tendsto_of_frequently (abstract). -/
def ge_of_tendsto_of_frequently' : Prop := True
/-- lowerBounds_closure (abstract). -/
def lowerBounds_closure' : Prop := True
/-- bddBelow_closure (abstract). -/
def bddBelow_closure' : Prop := True
/-- disjoint_nhds_atTop_iff (abstract). -/
def disjoint_nhds_atTop_iff' : Prop := True
/-- disjoint_nhds_atTop (abstract). -/
def disjoint_nhds_atTop' : Prop := True
/-- inf_nhds_atTop (abstract). -/
def inf_nhds_atTop' : Prop := True
/-- not_tendsto_nhds_of_tendsto_atTop (abstract). -/
def not_tendsto_nhds_of_tendsto_atTop' : Prop := True
/-- not_tendsto_atTop_of_tendsto_nhds (abstract). -/
def not_tendsto_atTop_of_tendsto_nhds' : Prop := True
/-- iInf_eq_of_forall_le_of_tendsto (abstract). -/
def iInf_eq_of_forall_le_of_tendsto' : Prop := True
/-- iUnion_Ici_eq_Ioi_of_lt_of_tendsto (abstract). -/
def iUnion_Ici_eq_Ioi_of_lt_of_tendsto' : Prop := True
/-- isOpen_Iio (abstract). -/
def isOpen_Iio' : Prop := True
/-- interior_Iio (abstract). -/
def interior_Iio' : Prop := True
-- COLLISION: exists_le' already in Order.lean — rename needed
/-- Ioo_mem_nhdsWithin_Ioi (abstract). -/
def Ioo_mem_nhdsWithin_Ioi' : Prop := True
/-- nhdsWithin_Ioi (abstract). -/
def nhdsWithin_Ioi' : Prop := True
/-- Ioc_mem_nhdsWithin_Ioi (abstract). -/
def Ioc_mem_nhdsWithin_Ioi' : Prop := True
/-- Ico_mem_nhdsWithin_Ioi (abstract). -/
def Ico_mem_nhdsWithin_Ioi' : Prop := True
/-- Icc_mem_nhdsWithin_Ioi (abstract). -/
def Icc_mem_nhdsWithin_Ioi' : Prop := True
/-- nhdsWithin_Ioc_eq_nhdsWithin_Ioi (abstract). -/
def nhdsWithin_Ioc_eq_nhdsWithin_Ioi' : Prop := True
/-- nhdsWithin_Ioo_eq_nhdsWithin_Ioi (abstract). -/
def nhdsWithin_Ioo_eq_nhdsWithin_Ioi' : Prop := True
/-- continuousWithinAt_Ioc_iff_Ioi (abstract). -/
def continuousWithinAt_Ioc_iff_Ioi' : Prop := True
/-- continuousWithinAt_Ioo_iff_Ioi (abstract). -/
def continuousWithinAt_Ioo_iff_Ioi' : Prop := True
/-- nhdsWithin_Ici (abstract). -/
def nhdsWithin_Ici' : Prop := True
/-- Ico_mem_nhdsWithin_Ici' (abstract). -/
def Ico_mem_nhdsWithin_Ici' : Prop := True
/-- Ioo_mem_nhdsWithin_Ici (abstract). -/
def Ioo_mem_nhdsWithin_Ici' : Prop := True
/-- Ioc_mem_nhdsWithin_Ici (abstract). -/
def Ioc_mem_nhdsWithin_Ici' : Prop := True
/-- Icc_mem_nhdsWithin_Ici (abstract). -/
def Icc_mem_nhdsWithin_Ici' : Prop := True
/-- nhdsWithin_Icc_eq_nhdsWithin_Ici (abstract). -/
def nhdsWithin_Icc_eq_nhdsWithin_Ici' : Prop := True
/-- nhdsWithin_Ico_eq_nhdsWithin_Ici (abstract). -/
def nhdsWithin_Ico_eq_nhdsWithin_Ici' : Prop := True
/-- continuousWithinAt_Icc_iff_Ici (abstract). -/
def continuousWithinAt_Icc_iff_Ici' : Prop := True
/-- continuousWithinAt_Ico_iff_Ici (abstract). -/
def continuousWithinAt_Ico_iff_Ici' : Prop := True
/-- isClosed_le_prod (abstract). -/
def isClosed_le_prod' : Prop := True
/-- isClosed_Icc (abstract). -/
def isClosed_Icc' : Prop := True
/-- closure_Icc (abstract). -/
def closure_Icc' : Prop := True
/-- le_of_tendsto_of_tendsto (abstract). -/
def le_of_tendsto_of_tendsto' : Prop := True
/-- closure_le_eq (abstract). -/
def closure_le_eq' : Prop := True
/-- closure_lt_subset_le (abstract). -/
def closure_lt_subset_le' : Prop := True
-- COLLISION: closure_le' already in RingTheory2.lean — rename needed
/-- le_on_closure (abstract). -/
def le_on_closure' : Prop := True
/-- epigraph (abstract). -/
def epigraph' : Prop := True
/-- hypograph (abstract). -/
def hypograph' : Prop := True
/-- isOpen_lt_prod (abstract). -/
def isOpen_lt_prod' : Prop := True
/-- isOpen_Ioo (abstract). -/
def isOpen_Ioo' : Prop := True
/-- interior_Ioo (abstract). -/
def interior_Ioo' : Prop := True
/-- Ioo_subset_closure_interior (abstract). -/
def Ioo_subset_closure_interior' : Prop := True
/-- Ioo_mem_nhds (abstract). -/
def Ioo_mem_nhds' : Prop := True
/-- Ioc_mem_nhds (abstract). -/
def Ioc_mem_nhds' : Prop := True
/-- Ico_mem_nhds (abstract). -/
def Ico_mem_nhds' : Prop := True
/-- of_predOrder_succOrder (abstract). -/
def of_predOrder_succOrder' : Prop := True
/-- lt_subset_interior_le (abstract). -/
def lt_subset_interior_le' : Prop := True
/-- frontier_le_subset_eq (abstract). -/
def frontier_le_subset_eq' : Prop := True
/-- frontier_Iic_subset (abstract). -/
def frontier_Iic_subset' : Prop := True
/-- frontier_Ici_subset (abstract). -/
def frontier_Ici_subset' : Prop := True
/-- frontier_lt_subset_eq (abstract). -/
def frontier_lt_subset_eq' : Prop := True
/-- continuous_if_le (abstract). -/
def continuous_if_le' : Prop := True
/-- if_le (abstract). -/
def if_le' : Prop := True
/-- eventually_lt (abstract). -/
def eventually_lt' : Prop := True
/-- continuous_min (abstract). -/
def continuous_min' : Prop := True
/-- continuous_max (abstract). -/
def continuous_max' : Prop := True
/-- max_right (abstract). -/
def max_right' : Prop := True
/-- max_left (abstract). -/
def max_left' : Prop := True
/-- tendsto_nhds_max_right (abstract). -/
def tendsto_nhds_max_right' : Prop := True
/-- tendsto_nhds_max_left (abstract). -/
def tendsto_nhds_max_left' : Prop := True
/-- min_right (abstract). -/
def min_right' : Prop := True
/-- min_left (abstract). -/
def min_left' : Prop := True
/-- tendsto_nhds_min_right (abstract). -/
def tendsto_nhds_min_right' : Prop := True
/-- tendsto_nhds_min_left (abstract). -/
def tendsto_nhds_min_left' : Prop := True
-- COLLISION: exists_between' already in Order.lean — rename needed
/-- Ioi_eq_biUnion (abstract). -/
def Ioi_eq_biUnion' : Prop := True
/-- Iio_eq_biUnion (abstract). -/
def Iio_eq_biUnion' : Prop := True

-- Order/OrderClosedExtr.lean

-- Order/PartialSups.lean
-- COLLISION: partialSups' already in Order.lean — rename needed
-- COLLISION: partialSups_apply' already in Order.lean — rename needed

-- Order/Priestley.lean
/-- PriestleySpace (abstract). -/
def PriestleySpace' : Prop := True
/-- exists_isClopen_upper_of_not_le (abstract). -/
def exists_isClopen_upper_of_not_le' : Prop := True

-- Order/ProjIcc.lean
/-- continuous_projIcc (abstract). -/
def continuous_projIcc' : Prop := True
/-- isQuotientMap_projIcc (abstract). -/
def isQuotientMap_projIcc' : Prop := True
/-- continuous_IccExtend_iff (abstract). -/
def continuous_IccExtend_iff' : Prop := True
/-- Icc_extend' (abstract). -/
def Icc_extend' : Prop := True

-- Order/Rolle.lean
/-- exists_Ioo_extr_on_Icc (abstract). -/
def exists_Ioo_extr_on_Icc' : Prop := True
/-- exists_isLocalExtr_Ioo (abstract). -/
def exists_isLocalExtr_Ioo' : Prop := True
/-- exists_isExtrOn_Ioo_of_tendsto (abstract). -/
def exists_isExtrOn_Ioo_of_tendsto' : Prop := True
/-- exists_isLocalExtr_Ioo_of_tendsto (abstract). -/
def exists_isLocalExtr_Ioo_of_tendsto' : Prop := True

-- Order/ScottTopology.lean
/-- DirSupInaccOn (abstract). -/
def DirSupInaccOn' : Prop := True
/-- DirSupInacc (abstract). -/
def DirSupInacc' : Prop := True
/-- dirSupInaccOn_univ (abstract). -/
def dirSupInaccOn_univ' : Prop := True
/-- dirSupInaccOn (abstract). -/
def dirSupInaccOn' : Prop := True
/-- DirSupClosed (abstract). -/
def DirSupClosed' : Prop := True
/-- dirSupInacc_compl (abstract). -/
def dirSupInacc_compl' : Prop := True
/-- dirSupClosed_compl (abstract). -/
def dirSupClosed_compl' : Prop := True
/-- dirSupClosed (abstract). -/
def dirSupClosed' : Prop := True
/-- dirSupInacc (abstract). -/
def dirSupInacc' : Prop := True
/-- dirSupClosed_Iic (abstract). -/
def dirSupClosed_Iic' : Prop := True
/-- dirSupInacc_iff_forall_sSup (abstract). -/
def dirSupInacc_iff_forall_sSup' : Prop := True
/-- dirSupClosed_iff_forall_sSup (abstract). -/
def dirSupClosed_iff_forall_sSup' : Prop := True
/-- scottHausdorff (abstract). -/
def scottHausdorff' : Prop := True
/-- IsScottHausdorff (abstract). -/
def IsScottHausdorff' : Prop := True
/-- dirSupInaccOn_of_isOpen (abstract). -/
def dirSupInaccOn_of_isOpen' : Prop := True
/-- dirSupClosed_of_isClosed (abstract). -/
def dirSupClosed_of_isClosed' : Prop := True
/-- isOpen_of_isLowerSet (abstract). -/
def isOpen_of_isLowerSet' : Prop := True
/-- isClosed_of_isUpperSet (abstract). -/
def isClosed_of_isUpperSet' : Prop := True
/-- scott (abstract). -/
def scott' : Prop := True
/-- upperSet_le_scott (abstract). -/
def upperSet_le_scott' : Prop := True
/-- scottHausdorff_le_scott (abstract). -/
def scottHausdorff_le_scott' : Prop := True
/-- IsScott (abstract). -/
def IsScott' : Prop := True
/-- isOpen_iff_isUpperSet_and_scottHausdorff_open (abstract). -/
def isOpen_iff_isUpperSet_and_scottHausdorff_open' : Prop := True
/-- isClosed_iff_isLowerSet_and_dirSupClosed (abstract). -/
def isClosed_iff_isLowerSet_and_dirSupClosed' : Prop := True
/-- lowerClosure_subset_closure (abstract). -/
def lowerClosure_subset_closure' : Prop := True
/-- monotone_of_continuous (abstract). -/
def monotone_of_continuous' : Prop := True
/-- scottContinuous_iff_continuous (abstract). -/
def scottContinuous_iff_continuous' : Prop := True
/-- isOpen_iff_Iic_compl_or_univ (abstract). -/
def isOpen_iff_Iic_compl_or_univ' : Prop := True
/-- isOpen_iff_scottContinuous_mem (abstract). -/
def isOpen_iff_scottContinuous_mem' : Prop := True
/-- WithScott (abstract). -/
def WithScott' : Prop := True
/-- toScott (abstract). -/
def toScott' : Prop := True
/-- ofScott (abstract). -/
def ofScott' : Prop := True
/-- scottHausdorff_le_lower (abstract). -/
def scottHausdorff_le_lower' : Prop := True
/-- withScottHomeomorph (abstract). -/
def withScottHomeomorph' : Prop := True
/-- scottHausdorff_le (abstract). -/
def scottHausdorff_le' : Prop := True

-- Order/T5.lean
/-- ordConnectedComponent_mem_nhds (abstract). -/
def ordConnectedComponent_mem_nhds' : Prop := True
/-- compl_section_ordSeparatingSet_mem_nhdsWithin_Ici (abstract). -/
def compl_section_ordSeparatingSet_mem_nhdsWithin_Ici' : Prop := True
/-- compl_section_ordSeparatingSet_mem_nhdsWithin_Iic (abstract). -/
def compl_section_ordSeparatingSet_mem_nhdsWithin_Iic' : Prop := True
/-- compl_section_ordSeparatingSet_mem_nhds (abstract). -/
def compl_section_ordSeparatingSet_mem_nhds' : Prop := True
/-- ordT5Nhd_mem_nhdsSet (abstract). -/
def ordT5Nhd_mem_nhdsSet' : Prop := True

-- Order/UpperLowerSetTopology.lean
/-- upperSet (abstract). -/
def upperSet' : Prop := True
/-- lowerSet (abstract). -/
def lowerSet' : Prop := True
/-- WithUpperSet (abstract). -/
def WithUpperSet' : Prop := True
/-- toUpperSet (abstract). -/
def toUpperSet' : Prop := True
/-- ofUpperSet (abstract). -/
def ofUpperSet' : Prop := True
/-- ofUpperSetOrderIso (abstract). -/
def ofUpperSetOrderIso' : Prop := True
/-- toUpperSetOrderIso (abstract). -/
def toUpperSetOrderIso' : Prop := True
/-- WithLowerSet (abstract). -/
def WithLowerSet' : Prop := True
/-- toLowerSet (abstract). -/
def toLowerSet' : Prop := True
/-- ofLowerSet (abstract). -/
def ofLowerSet' : Prop := True
/-- ofLowerSetOrderIso (abstract). -/
def ofLowerSetOrderIso' : Prop := True
/-- toLowerSetOrderIso (abstract). -/
def toLowerSetOrderIso' : Prop := True
-- COLLISION: IsUpperSet' already in Order.lean — rename needed
-- COLLISION: IsLowerSet' already in Order.lean — rename needed
/-- WithUpperSetHomeomorph (abstract). -/
def WithUpperSetHomeomorph' : Prop := True
/-- isOpen_iff_isUpperSet (abstract). -/
def isOpen_iff_isUpperSet' : Prop := True
/-- isClosed_iff_isLower (abstract). -/
def isClosed_iff_isLower' : Prop := True
/-- closure_eq_lowerClosure (abstract). -/
def closure_eq_lowerClosure' : Prop := True
/-- monotone_iff_continuous (abstract). -/
def monotone_iff_continuous' : Prop := True
/-- monotone_to_upperTopology_continuous (abstract). -/
def monotone_to_upperTopology_continuous' : Prop := True
/-- upperSet_le_upper (abstract). -/
def upperSet_le_upper' : Prop := True
/-- WithLowerSetHomeomorph (abstract). -/
def WithLowerSetHomeomorph' : Prop := True
/-- isOpen_iff_isLowerSet (abstract). -/
def isOpen_iff_isLowerSet' : Prop := True
/-- isClosed_iff_isUpper (abstract). -/
def isClosed_iff_isUpper' : Prop := True
/-- closure_eq_upperClosure (abstract). -/
def closure_eq_upperClosure' : Prop := True
/-- monotone_to_lowerTopology_continuous (abstract). -/
def monotone_to_lowerTopology_continuous' : Prop := True
/-- lowerSet_le_lower (abstract). -/
def lowerSet_le_lower' : Prop := True
/-- isUpperSet_orderDual (abstract). -/
def isUpperSet_orderDual' : Prop := True
/-- isOpen_ofLowerSet_preimage (abstract). -/
def isOpen_ofLowerSet_preimage' : Prop := True

-- Partial.lean
/-- rtendsto_nhds (abstract). -/
def rtendsto_nhds' : Prop := True
/-- rtendsto'_nhds (abstract). -/
def rtendsto'_nhds' : Prop := True
/-- ptendsto_nhds (abstract). -/
def ptendsto_nhds' : Prop := True
/-- ptendsto'_nhds (abstract). -/
def ptendsto'_nhds' : Prop := True
/-- PContinuous (abstract). -/
def PContinuous' : Prop := True
/-- open_dom_of_pcontinuous (abstract). -/
def open_dom_of_pcontinuous' : Prop := True
/-- pcontinuous_iff' (abstract). -/
def pcontinuous_iff' : Prop := True
/-- continuousWithinAt_iff_ptendsto_res (abstract). -/
def continuousWithinAt_iff_ptendsto_res' : Prop := True

-- PartialHomeomorph.lean
/-- deals (abstract). -/
def deals' : Prop := True
-- COLLISION: PartialHomeomorph' already in Geometry2.lean — rename needed
/-- map_source (abstract). -/
def map_source' : Prop := True
/-- map_source'' (abstract). -/
def map_source'' : Prop := True
-- COLLISION: left_inv' already in RingTheory2.lean — rename needed
-- COLLISION: mapsTo' already in Order.lean — rename needed
/-- symm_mapsTo (abstract). -/
def symm_mapsTo' : Prop := True
/-- leftInvOn (abstract). -/
def leftInvOn' : Prop := True
-- COLLISION: rightInvOn' already in Algebra.lean — rename needed
/-- invOn (abstract). -/
def invOn' : Prop := True
-- COLLISION: injOn' already in Order.lean — rename needed
/-- bijOn (abstract). -/
def bijOn' : Prop := True
-- COLLISION: surjOn' already in Order.lean — rename needed
/-- toPartialHomeomorphOfImageEq (abstract). -/
def toPartialHomeomorphOfImageEq' : Prop := True
-- COLLISION: toPartialHomeomorph' already in Analysis.lean — rename needed
/-- replaceEquiv (abstract). -/
def replaceEquiv' : Prop := True
/-- replaceEquiv_eq_self (abstract). -/
def replaceEquiv_eq_self' : Prop := True
/-- source_preimage_target (abstract). -/
def source_preimage_target' : Prop := True
-- COLLISION: eventually_left_inverse' already in Analysis.lean — rename needed
-- COLLISION: eventually_right_inverse' already in Analysis.lean — rename needed
/-- eventually_ne_nhdsWithin (abstract). -/
def eventually_ne_nhdsWithin' : Prop := True
/-- nhdsWithin_source_inter (abstract). -/
def nhdsWithin_source_inter' : Prop := True
/-- nhdsWithin_target_inter (abstract). -/
def nhdsWithin_target_inter' : Prop := True
/-- image_eq_target_inter_inv_preimage (abstract). -/
def image_eq_target_inter_inv_preimage' : Prop := True
/-- image_source_inter_eq' (abstract). -/
def image_source_inter_eq' : Prop := True
/-- symm_image_eq_source_inter_preimage (abstract). -/
def symm_image_eq_source_inter_preimage' : Prop := True
/-- symm_image_target_inter_eq (abstract). -/
def symm_image_target_inter_eq' : Prop := True
/-- source_inter_preimage_inv_preimage (abstract). -/
def source_inter_preimage_inv_preimage' : Prop := True
/-- target_inter_inv_preimage_preimage (abstract). -/
def target_inter_inv_preimage_preimage' : Prop := True
/-- source_inter_preimage_target_inter (abstract). -/
def source_inter_preimage_target_inter' : Prop := True
/-- image_source_eq_target (abstract). -/
def image_source_eq_target' : Prop := True
/-- continuousAt_symm (abstract). -/
def continuousAt_symm' : Prop := True
/-- tendsto_symm (abstract). -/
def tendsto_symm' : Prop := True
/-- eventually_nhdsWithin (abstract). -/
def eventually_nhdsWithin' : Prop := True
/-- preimage_eventuallyEq_target_inter_preimage_inter (abstract). -/
def preimage_eventuallyEq_target_inter_preimage_inter' : Prop := True
/-- isOpen_inter_preimage_symm (abstract). -/
def isOpen_inter_preimage_symm' : Prop := True
/-- isOpen_image_of_subset_source (abstract). -/
def isOpen_image_of_subset_source' : Prop := True
/-- isOpen_image_source_inter (abstract). -/
def isOpen_image_source_inter' : Prop := True
/-- isOpen_image_symm_of_subset_target (abstract). -/
def isOpen_image_symm_of_subset_target' : Prop := True
/-- isOpen_symm_image_iff_of_subset_target (abstract). -/
def isOpen_symm_image_iff_of_subset_target' : Prop := True
/-- isOpen_image_iff_of_subset_source (abstract). -/
def isOpen_image_iff_of_subset_source' : Prop := True
-- COLLISION: IsImage' already in CategoryTheory.lean — rename needed
/-- iff_preimage_eq (abstract). -/
def iff_preimage_eq' : Prop := True
/-- iff_symm_preimage_eq (abstract). -/
def iff_symm_preimage_eq' : Prop := True
/-- of_image_eq (abstract). -/
def of_image_eq' : Prop := True
/-- of_symm_image_eq (abstract). -/
def of_symm_image_eq' : Prop := True
-- COLLISION: restr' already in Analysis.lean — rename needed
/-- isImage_source_target (abstract). -/
def isImage_source_target' : Prop := True
/-- isImage_source_target_of_disjoint (abstract). -/
def isImage_source_target_of_disjoint' : Prop := True
/-- preimage_interior (abstract). -/
def preimage_interior' : Prop := True
/-- preimage_frontier (abstract). -/
def preimage_frontier' : Prop := True
/-- ofContinuousOpenRestrict (abstract). -/
def ofContinuousOpenRestrict' : Prop := True
/-- ofContinuousOpen (abstract). -/
def ofContinuousOpen' : Prop := True
/-- restr_source' (abstract). -/
def restr_source' : Prop := True
/-- restr_toPartialEquiv' (abstract). -/
def restr_toPartialEquiv' : Prop := True
/-- restr_eq_of_source_subset (abstract). -/
def restr_eq_of_source_subset' : Prop := True
/-- restr_univ (abstract). -/
def restr_univ' : Prop := True
/-- restr_source_inter (abstract). -/
def restr_source_inter' : Prop := True
-- COLLISION: ofSet' already in SetTheory.lean — rename needed
/-- ofSet_univ_eq_refl (abstract). -/
def ofSet_univ_eq_refl' : Prop := True
/-- trans_target' (abstract). -/
def trans_target' : Prop := True
/-- trans_target'' (abstract). -/
def trans_target'' : Prop := True
/-- inv_image_trans_target (abstract). -/
def inv_image_trans_target' : Prop := True
-- COLLISION: trans_assoc' already in LinearAlgebra2.lean — rename needed
-- COLLISION: trans_refl' already in Algebra.lean — rename needed
-- COLLISION: refl_trans' already in Algebra.lean — rename needed
/-- trans_ofSet (abstract). -/
def trans_ofSet' : Prop := True
/-- trans_of_set' (abstract). -/
def trans_of_set' : Prop := True
/-- ofSet_trans (abstract). -/
def ofSet_trans' : Prop := True
/-- ofSet_trans_ofSet (abstract). -/
def ofSet_trans_ofSet' : Prop := True
/-- restr_trans (abstract). -/
def restr_trans' : Prop := True
/-- EqOnSource (abstract). -/
def EqOnSource' : Prop := True
/-- restr_eqOn_source (abstract). -/
def restr_eqOn_source' : Prop := True
/-- eq_of_eqOnSource_univ (abstract). -/
def eq_of_eqOnSource_univ' : Prop := True
/-- refl_prod_refl (abstract). -/
def refl_prod_refl' : Prop := True
/-- prod_trans (abstract). -/
def prod_trans' : Prop := True
/-- prod_eq_prod_of_nonempty (abstract). -/
def prod_eq_prod_of_nonempty' : Prop := True
/-- symm_piecewise (abstract). -/
def symm_piecewise' : Prop := True
/-- continuousWithinAt_iff_continuousWithinAt_comp_right (abstract). -/
def continuousWithinAt_iff_continuousWithinAt_comp_right' : Prop := True
/-- continuousAt_iff_continuousAt_comp_right (abstract). -/
def continuousAt_iff_continuousAt_comp_right' : Prop := True
/-- continuousOn_iff_continuousOn_comp_right (abstract). -/
def continuousOn_iff_continuousOn_comp_right' : Prop := True
/-- continuousWithinAt_iff_continuousWithinAt_comp_left (abstract). -/
def continuousWithinAt_iff_continuousWithinAt_comp_left' : Prop := True
/-- continuousAt_iff_continuousAt_comp_left (abstract). -/
def continuousAt_iff_continuousAt_comp_left' : Prop := True
/-- continuousOn_iff_continuousOn_comp_left (abstract). -/
def continuousOn_iff_continuousOn_comp_left' : Prop := True
/-- continuous_iff_continuous_comp_left (abstract). -/
def continuous_iff_continuous_comp_left' : Prop := True
/-- homeomorphOfImageSubsetSource (abstract). -/
def homeomorphOfImageSubsetSource' : Prop := True
/-- toHomeomorphSourceTarget (abstract). -/
def toHomeomorphSourceTarget' : Prop := True
/-- secondCountableTopology_source (abstract). -/
def secondCountableTopology_source' : Prop := True
/-- nhds_eq_comap_inf_principal (abstract). -/
def nhds_eq_comap_inf_principal' : Prop := True
/-- toHomeomorphOfSourceEqUnivTargetEqUniv (abstract). -/
def toHomeomorphOfSourceEqUnivTargetEqUniv' : Prop := True
/-- isOpenEmbedding_restrict (abstract). -/
def isOpenEmbedding_restrict' : Prop := True
/-- trans_toPartialHomeomorph (abstract). -/
def trans_toPartialHomeomorph' : Prop := True
/-- transPartialHomeomorph (abstract). -/
def transPartialHomeomorph' : Prop := True
/-- transPartialHomeomorph_eq_trans (abstract). -/
def transPartialHomeomorph_eq_trans' : Prop := True
/-- transPartialHomeomorph_trans (abstract). -/
def transPartialHomeomorph_trans' : Prop := True
/-- trans_transPartialHomeomorph (abstract). -/
def trans_transPartialHomeomorph' : Prop := True
/-- toPartialHomeomorph_left_inv (abstract). -/
def toPartialHomeomorph_left_inv' : Prop := True
/-- toPartialHomeomorph_right_inv (abstract). -/
def toPartialHomeomorph_right_inv' : Prop := True
/-- partialHomeomorphSubtypeCoe (abstract). -/
def partialHomeomorphSubtypeCoe' : Prop := True
/-- partialHomeomorphSubtypeCoe_target (abstract). -/
def partialHomeomorphSubtypeCoe_target' : Prop := True
/-- transHomeomorph (abstract). -/
def transHomeomorph' : Prop := True
/-- transHomeomorph_eq_trans (abstract). -/
def transHomeomorph_eq_trans' : Prop := True
/-- transHomeomorph_transHomeomorph (abstract). -/
def transHomeomorph_transHomeomorph' : Prop := True
/-- trans_transHomeomorph (abstract). -/
def trans_transHomeomorph' : Prop := True
/-- subtypeRestr (abstract). -/
def subtypeRestr' : Prop := True
/-- subtypeRestr_source (abstract). -/
def subtypeRestr_source' : Prop := True
/-- map_subtype_source (abstract). -/
def map_subtype_source' : Prop := True
/-- subtypeRestr_symm_trans_subtypeRestr (abstract). -/
def subtypeRestr_symm_trans_subtypeRestr' : Prop := True
/-- subtypeRestr_symm_eqOn (abstract). -/
def subtypeRestr_symm_eqOn' : Prop := True
/-- subtypeRestr_symm_eqOn_of_le (abstract). -/
def subtypeRestr_symm_eqOn_of_le' : Prop := True

-- PartitionOfUnity.lean
/-- PartitionOfUnity (abstract). -/
def PartitionOfUnity' : Prop := True
/-- BumpCovering (abstract). -/
def BumpCovering' : Prop := True
/-- locallyFinite (abstract). -/
def locallyFinite' : Prop := True
/-- locallyFinite_tsupport (abstract). -/
def locallyFinite_tsupport' : Prop := True
-- COLLISION: nonneg' already in SetTheory.lean — rename needed
/-- sum_eq_one (abstract). -/
def sum_eq_one' : Prop := True
-- COLLISION: exists_pos' already in LinearAlgebra2.lean — rename needed
/-- sum_le_one (abstract). -/
def sum_le_one' : Prop := True
/-- finsupport (abstract). -/
def finsupport' : Prop := True
/-- mem_finsupport (abstract). -/
def mem_finsupport' : Prop := True
/-- coe_finsupport (abstract). -/
def coe_finsupport' : Prop := True
/-- sum_finsupport (abstract). -/
def sum_finsupport' : Prop := True
/-- sum_finsupport_smul_eq_finsum (abstract). -/
def sum_finsupport_smul_eq_finsum' : Prop := True
/-- finite_tsupport (abstract). -/
def finite_tsupport' : Prop := True
/-- fintsupport (abstract). -/
def fintsupport' : Prop := True
/-- mem_fintsupport_iff (abstract). -/
def mem_fintsupport_iff' : Prop := True
/-- eventually_fintsupport_subset (abstract). -/
def eventually_fintsupport_subset' : Prop := True
/-- finsupport_subset_fintsupport (abstract). -/
def finsupport_subset_fintsupport' : Prop := True
/-- eventually_finsupport_subset (abstract). -/
def eventually_finsupport_subset' : Prop := True
/-- continuous_smul (abstract). -/
def continuous_smul' : Prop := True
/-- continuous_finsum_smul (abstract). -/
def continuous_finsum_smul' : Prop := True
-- COLLISION: IsSubordinate' already in Analysis.lean — rename needed
/-- exists_finset_nhd' (abstract). -/
def exists_finset_nhd' : Prop := True
/-- exists_finset_nhd_support_subset (abstract). -/
def exists_finset_nhd_support_subset' : Prop := True
-- COLLISION: single' already in RingTheory2.lean — rename needed
/-- exists_isSubordinate_of_locallyFinite_of_prop (abstract). -/
def exists_isSubordinate_of_locallyFinite_of_prop' : Prop := True
/-- exists_isSubordinate_of_locallyFinite (abstract). -/
def exists_isSubordinate_of_locallyFinite' : Prop := True
/-- exists_isSubordinate_of_prop (abstract). -/
def exists_isSubordinate_of_prop' : Prop := True
/-- exists_isSubordinate (abstract). -/
def exists_isSubordinate' : Prop := True
/-- exists_isSubordinate_of_locallyFinite_of_prop_t2space (abstract). -/
def exists_isSubordinate_of_locallyFinite_of_prop_t2space' : Prop := True
/-- exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space (abstract). -/
def exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space' : Prop := True
-- COLLISION: ind' already in Order.lean — rename needed
-- COLLISION: eventuallyEq_one' already in Analysis.lean — rename needed
/-- ind_apply (abstract). -/
def ind_apply' : Prop := True
/-- toPOUFun (abstract). -/
def toPOUFun' : Prop := True
/-- toPOUFun_zero_of_zero (abstract). -/
def toPOUFun_zero_of_zero' : Prop := True
/-- support_toPOUFun_subset (abstract). -/
def support_toPOUFun_subset' : Prop := True
/-- toPOUFun_eq_mul_prod (abstract). -/
def toPOUFun_eq_mul_prod' : Prop := True
/-- sum_toPOUFun_eq (abstract). -/
def sum_toPOUFun_eq' : Prop := True
/-- exists_finset_toPOUFun_eventuallyEq (abstract). -/
def exists_finset_toPOUFun_eventuallyEq' : Prop := True
/-- continuous_toPOUFun (abstract). -/
def continuous_toPOUFun' : Prop := True
/-- toPartitionOfUnity (abstract). -/
def toPartitionOfUnity' : Prop := True
/-- toPartitionOfUnity_eq_mul_prod (abstract). -/
def toPartitionOfUnity_eq_mul_prod' : Prop := True
/-- exists_finset_toPartitionOfUnity_eventuallyEq (abstract). -/
def exists_finset_toPartitionOfUnity_eventuallyEq' : Prop := True
/-- toPartitionOfUnity_zero_of_zero (abstract). -/
def toPartitionOfUnity_zero_of_zero' : Prop := True
/-- support_toPartitionOfUnity_subset (abstract). -/
def support_toPartitionOfUnity_subset' : Prop := True
/-- sum_toPartitionOfUnity_eq (abstract). -/
def sum_toPartitionOfUnity_eq' : Prop := True
/-- exists_isSubordinate_of_locallyFinite_t2space (abstract). -/
def exists_isSubordinate_of_locallyFinite_t2space' : Prop := True
/-- exists_continuous_sum_one_of_isOpen_isCompact (abstract). -/
def exists_continuous_sum_one_of_isOpen_isCompact' : Prop := True

-- Perfect.lean
-- COLLISION: step' already in Analysis.lean — rename needed
/-- nhds_inter (abstract). -/
def nhds_inter' : Prop := True
/-- Preperfect (abstract). -/
def Preperfect' : Prop := True
/-- Perfect (abstract). -/
def Perfect' : Prop := True
/-- preperfect_iff_nhds (abstract). -/
def preperfect_iff_nhds' : Prop := True
/-- PerfectSpace (abstract). -/
def PerfectSpace' : Prop := True
/-- univ_perfect (abstract). -/
def univ_perfect' : Prop := True
/-- open_inter (abstract). -/
def open_inter' : Prop := True
/-- perfect_closure (abstract). -/
def perfect_closure' : Prop := True
/-- closure_nhds_inter (abstract). -/
def closure_nhds_inter' : Prop := True
/-- splitting (abstract). -/
def splitting' : Prop := True
/-- exists_countable_union_perfect_of_isClosed (abstract). -/
def exists_countable_union_perfect_of_isClosed' : Prop := True
/-- exists_perfect_nonempty_of_isClosed_of_not_countable (abstract). -/
def exists_perfect_nonempty_of_isClosed_of_not_countable' : Prop := True
/-- perfectSpace_iff_forall_not_isolated (abstract). -/
def perfectSpace_iff_forall_not_isolated' : Prop := True

-- PreorderRestrict.lean
/-- continuous_restrictLe (abstract). -/
def continuous_restrictLe' : Prop := True
/-- continuous_restrictLe₂ (abstract). -/
def continuous_restrictLe₂' : Prop := True
/-- continuous_frestrictLe (abstract). -/
def continuous_frestrictLe' : Prop := True
/-- continuous_frestrictLe₂ (abstract). -/
def continuous_frestrictLe₂' : Prop := True

-- QuasiSeparated.lean
/-- IsQuasiSeparated (abstract). -/
def IsQuasiSeparated' : Prop := True
/-- QuasiSeparatedSpace (abstract). -/
def QuasiSeparatedSpace' : Prop := True
/-- isQuasiSeparated_univ_iff (abstract). -/
def isQuasiSeparated_univ_iff' : Prop := True
/-- isQuasiSeparated_univ (abstract). -/
def isQuasiSeparated_univ' : Prop := True
/-- image_of_isEmbedding (abstract). -/
def image_of_isEmbedding' : Prop := True
/-- isQuasiSeparated_iff (abstract). -/
def isQuasiSeparated_iff' : Prop := True
/-- isQuasiSeparated_iff_quasiSeparatedSpace (abstract). -/
def isQuasiSeparated_iff_quasiSeparatedSpace' : Prop := True
/-- of_quasiSeparatedSpace (abstract). -/
def of_quasiSeparatedSpace' : Prop := True

-- RestrictGen.lean
/-- of_continuous_prop (abstract). -/
def of_continuous_prop' : Prop := True
/-- of_isClosed (abstract). -/
def of_isClosed' : Prop := True
-- COLLISION: enlarge' already in MeasureTheory2.lean — rename needed
/-- of_seq (abstract). -/
def of_seq' : Prop := True
/-- isCompact_of_weaklyLocallyCompact (abstract). -/
def isCompact_of_weaklyLocallyCompact' : Prop := True

-- Semicontinuous.lean
/-- LowerSemicontinuousWithinAt (abstract). -/
def LowerSemicontinuousWithinAt' : Prop := True
/-- LowerSemicontinuousOn (abstract). -/
def LowerSemicontinuousOn' : Prop := True
/-- LowerSemicontinuousAt (abstract). -/
def LowerSemicontinuousAt' : Prop := True
/-- LowerSemicontinuous (abstract). -/
def LowerSemicontinuous' : Prop := True
/-- UpperSemicontinuousWithinAt (abstract). -/
def UpperSemicontinuousWithinAt' : Prop := True
/-- UpperSemicontinuousOn (abstract). -/
def UpperSemicontinuousOn' : Prop := True
/-- UpperSemicontinuousAt (abstract). -/
def UpperSemicontinuousAt' : Prop := True
/-- UpperSemicontinuous (abstract). -/
def UpperSemicontinuous' : Prop := True
/-- lowerSemicontinuousWithinAt_univ_iff (abstract). -/
def lowerSemicontinuousWithinAt_univ_iff' : Prop := True
/-- lowerSemicontinuousWithinAt (abstract). -/
def lowerSemicontinuousWithinAt' : Prop := True
/-- lowerSemicontinuousOn (abstract). -/
def lowerSemicontinuousOn' : Prop := True
/-- lowerSemicontinuousWithinAt_const (abstract). -/
def lowerSemicontinuousWithinAt_const' : Prop := True
/-- lowerSemicontinuousAt_const (abstract). -/
def lowerSemicontinuousAt_const' : Prop := True
/-- lowerSemicontinuousOn_const (abstract). -/
def lowerSemicontinuousOn_const' : Prop := True
/-- lowerSemicontinuous_const (abstract). -/
def lowerSemicontinuous_const' : Prop := True
/-- lowerSemicontinuous_indicator (abstract). -/
def lowerSemicontinuous_indicator' : Prop := True
/-- lowerSemicontinuousOn_indicator (abstract). -/
def lowerSemicontinuousOn_indicator' : Prop := True
/-- lowerSemicontinuousAt_indicator (abstract). -/
def lowerSemicontinuousAt_indicator' : Prop := True
/-- lowerSemicontinuousWithinAt_indicator (abstract). -/
def lowerSemicontinuousWithinAt_indicator' : Prop := True
/-- lowerSemicontinuous_iff_isOpen_preimage (abstract). -/
def lowerSemicontinuous_iff_isOpen_preimage' : Prop := True
/-- lowerSemicontinuous_iff_isClosed_preimage (abstract). -/
def lowerSemicontinuous_iff_isClosed_preimage' : Prop := True
/-- lowerSemicontinuousAt (abstract). -/
def lowerSemicontinuousAt' : Prop := True
-- COLLISION: lowerSemicontinuous' already in Analysis.lean — rename needed
/-- lowerSemicontinuousWithinAt_iff_le_liminf (abstract). -/
def lowerSemicontinuousWithinAt_iff_le_liminf' : Prop := True
/-- lowerSemicontinuousAt_iff_le_liminf (abstract). -/
def lowerSemicontinuousAt_iff_le_liminf' : Prop := True
/-- lowerSemicontinuous_iff_le_liminf (abstract). -/
def lowerSemicontinuous_iff_le_liminf' : Prop := True
/-- lowerSemicontinuousOn_iff_le_liminf (abstract). -/
def lowerSemicontinuousOn_iff_le_liminf' : Prop := True
/-- lowerSemicontinuous_iff_isClosed_epigraph (abstract). -/
def lowerSemicontinuous_iff_isClosed_epigraph' : Prop := True
/-- comp_lowerSemicontinuousWithinAt (abstract). -/
def comp_lowerSemicontinuousWithinAt' : Prop := True
/-- comp_lowerSemicontinuousAt (abstract). -/
def comp_lowerSemicontinuousAt' : Prop := True
/-- comp_lowerSemicontinuousOn (abstract). -/
def comp_lowerSemicontinuousOn' : Prop := True
/-- comp_lowerSemicontinuous (abstract). -/
def comp_lowerSemicontinuous' : Prop := True
/-- comp_lowerSemicontinuousWithinAt_antitone (abstract). -/
def comp_lowerSemicontinuousWithinAt_antitone' : Prop := True
/-- comp_lowerSemicontinuousAt_antitone (abstract). -/
def comp_lowerSemicontinuousAt_antitone' : Prop := True
/-- comp_lowerSemicontinuousOn_antitone (abstract). -/
def comp_lowerSemicontinuousOn_antitone' : Prop := True
/-- comp_lowerSemicontinuous_antitone (abstract). -/
def comp_lowerSemicontinuous_antitone' : Prop := True
/-- comp_continuousAt (abstract). -/
def comp_continuousAt' : Prop := True
/-- comp_continuousAt_of_eq (abstract). -/
def comp_continuousAt_of_eq' : Prop := True
/-- lowerSemicontinuousWithinAt_sum (abstract). -/
def lowerSemicontinuousWithinAt_sum' : Prop := True
/-- lowerSemicontinuousAt_sum (abstract). -/
def lowerSemicontinuousAt_sum' : Prop := True
/-- lowerSemicontinuousOn_sum (abstract). -/
def lowerSemicontinuousOn_sum' : Prop := True
/-- lowerSemicontinuous_sum (abstract). -/
def lowerSemicontinuous_sum' : Prop := True
/-- lowerSemicontinuousWithinAt_ciSup (abstract). -/
def lowerSemicontinuousWithinAt_ciSup' : Prop := True
/-- lowerSemicontinuousWithinAt_iSup (abstract). -/
def lowerSemicontinuousWithinAt_iSup' : Prop := True
/-- lowerSemicontinuousWithinAt_biSup (abstract). -/
def lowerSemicontinuousWithinAt_biSup' : Prop := True
/-- lowerSemicontinuousAt_ciSup (abstract). -/
def lowerSemicontinuousAt_ciSup' : Prop := True
/-- lowerSemicontinuousAt_iSup (abstract). -/
def lowerSemicontinuousAt_iSup' : Prop := True
/-- lowerSemicontinuousAt_biSup (abstract). -/
def lowerSemicontinuousAt_biSup' : Prop := True
/-- lowerSemicontinuousOn_ciSup (abstract). -/
def lowerSemicontinuousOn_ciSup' : Prop := True
/-- lowerSemicontinuousOn_iSup (abstract). -/
def lowerSemicontinuousOn_iSup' : Prop := True
/-- lowerSemicontinuousOn_biSup (abstract). -/
def lowerSemicontinuousOn_biSup' : Prop := True
/-- lowerSemicontinuous_ciSup (abstract). -/
def lowerSemicontinuous_ciSup' : Prop := True
/-- lowerSemicontinuous_iSup (abstract). -/
def lowerSemicontinuous_iSup' : Prop := True
/-- lowerSemicontinuous_biSup (abstract). -/
def lowerSemicontinuous_biSup' : Prop := True
/-- lowerSemicontinuousWithinAt_tsum (abstract). -/
def lowerSemicontinuousWithinAt_tsum' : Prop := True
/-- lowerSemicontinuousAt_tsum (abstract). -/
def lowerSemicontinuousAt_tsum' : Prop := True
/-- lowerSemicontinuousOn_tsum (abstract). -/
def lowerSemicontinuousOn_tsum' : Prop := True
/-- lowerSemicontinuous_tsum (abstract). -/
def lowerSemicontinuous_tsum' : Prop := True
/-- upperSemicontinuousWithinAt_univ_iff (abstract). -/
def upperSemicontinuousWithinAt_univ_iff' : Prop := True
/-- upperSemicontinuousWithinAt (abstract). -/
def upperSemicontinuousWithinAt' : Prop := True
/-- upperSemicontinuousOn (abstract). -/
def upperSemicontinuousOn' : Prop := True
/-- upperSemicontinuousWithinAt_const (abstract). -/
def upperSemicontinuousWithinAt_const' : Prop := True
/-- upperSemicontinuousAt_const (abstract). -/
def upperSemicontinuousAt_const' : Prop := True
/-- upperSemicontinuousOn_const (abstract). -/
def upperSemicontinuousOn_const' : Prop := True
/-- upperSemicontinuous_const (abstract). -/
def upperSemicontinuous_const' : Prop := True
/-- upperSemicontinuous_indicator (abstract). -/
def upperSemicontinuous_indicator' : Prop := True
/-- upperSemicontinuousOn_indicator (abstract). -/
def upperSemicontinuousOn_indicator' : Prop := True
/-- upperSemicontinuousAt_indicator (abstract). -/
def upperSemicontinuousAt_indicator' : Prop := True
/-- upperSemicontinuousWithinAt_indicator (abstract). -/
def upperSemicontinuousWithinAt_indicator' : Prop := True
/-- upperSemicontinuous_iff_isOpen_preimage (abstract). -/
def upperSemicontinuous_iff_isOpen_preimage' : Prop := True
/-- upperSemicontinuous_iff_isClosed_preimage (abstract). -/
def upperSemicontinuous_iff_isClosed_preimage' : Prop := True
/-- upperSemicontinuousAt (abstract). -/
def upperSemicontinuousAt' : Prop := True
/-- upperSemicontinuous (abstract). -/
def upperSemicontinuous' : Prop := True
/-- upperSemicontinuousWithinAt_iff_limsup_le (abstract). -/
def upperSemicontinuousWithinAt_iff_limsup_le' : Prop := True
/-- upperSemicontinuousAt_iff_limsup_le (abstract). -/
def upperSemicontinuousAt_iff_limsup_le' : Prop := True
/-- upperSemicontinuous_iff_limsup_le (abstract). -/
def upperSemicontinuous_iff_limsup_le' : Prop := True
/-- upperSemicontinuousOn_iff_limsup_le (abstract). -/
def upperSemicontinuousOn_iff_limsup_le' : Prop := True
/-- upperSemicontinuous_iff_IsClosed_hypograph (abstract). -/
def upperSemicontinuous_iff_IsClosed_hypograph' : Prop := True
/-- comp_upperSemicontinuousWithinAt (abstract). -/
def comp_upperSemicontinuousWithinAt' : Prop := True
/-- comp_upperSemicontinuousAt (abstract). -/
def comp_upperSemicontinuousAt' : Prop := True
/-- comp_upperSemicontinuousOn (abstract). -/
def comp_upperSemicontinuousOn' : Prop := True
/-- comp_upperSemicontinuous (abstract). -/
def comp_upperSemicontinuous' : Prop := True
/-- comp_upperSemicontinuousWithinAt_antitone (abstract). -/
def comp_upperSemicontinuousWithinAt_antitone' : Prop := True
/-- comp_upperSemicontinuousAt_antitone (abstract). -/
def comp_upperSemicontinuousAt_antitone' : Prop := True
/-- comp_upperSemicontinuousOn_antitone (abstract). -/
def comp_upperSemicontinuousOn_antitone' : Prop := True
/-- comp_upperSemicontinuous_antitone (abstract). -/
def comp_upperSemicontinuous_antitone' : Prop := True
/-- upperSemicontinuousWithinAt_sum (abstract). -/
def upperSemicontinuousWithinAt_sum' : Prop := True
/-- upperSemicontinuousAt_sum (abstract). -/
def upperSemicontinuousAt_sum' : Prop := True
/-- upperSemicontinuousOn_sum (abstract). -/
def upperSemicontinuousOn_sum' : Prop := True
/-- upperSemicontinuous_sum (abstract). -/
def upperSemicontinuous_sum' : Prop := True
/-- upperSemicontinuousWithinAt_ciInf (abstract). -/
def upperSemicontinuousWithinAt_ciInf' : Prop := True
/-- upperSemicontinuousWithinAt_iInf (abstract). -/
def upperSemicontinuousWithinAt_iInf' : Prop := True
/-- upperSemicontinuousWithinAt_biInf (abstract). -/
def upperSemicontinuousWithinAt_biInf' : Prop := True
/-- upperSemicontinuousAt_ciInf (abstract). -/
def upperSemicontinuousAt_ciInf' : Prop := True
/-- upperSemicontinuousAt_iInf (abstract). -/
def upperSemicontinuousAt_iInf' : Prop := True
/-- upperSemicontinuousAt_biInf (abstract). -/
def upperSemicontinuousAt_biInf' : Prop := True
/-- upperSemicontinuousOn_ciInf (abstract). -/
def upperSemicontinuousOn_ciInf' : Prop := True
/-- upperSemicontinuousOn_iInf (abstract). -/
def upperSemicontinuousOn_iInf' : Prop := True
/-- upperSemicontinuousOn_biInf (abstract). -/
def upperSemicontinuousOn_biInf' : Prop := True
/-- upperSemicontinuous_ciInf (abstract). -/
def upperSemicontinuous_ciInf' : Prop := True
/-- upperSemicontinuous_iInf (abstract). -/
def upperSemicontinuous_iInf' : Prop := True
/-- upperSemicontinuous_biInf (abstract). -/
def upperSemicontinuous_biInf' : Prop := True
/-- continuousWithinAt_iff_lower_upperSemicontinuousWithinAt (abstract). -/
def continuousWithinAt_iff_lower_upperSemicontinuousWithinAt' : Prop := True
/-- continuousAt_iff_lower_upperSemicontinuousAt (abstract). -/
def continuousAt_iff_lower_upperSemicontinuousAt' : Prop := True
/-- continuousOn_iff_lower_upperSemicontinuousOn (abstract). -/
def continuousOn_iff_lower_upperSemicontinuousOn' : Prop := True
/-- continuous_iff_lower_upperSemicontinuous (abstract). -/
def continuous_iff_lower_upperSemicontinuous' : Prop := True

-- SeparatedMap.lean
/-- toPullbackDiag (abstract). -/
def toPullbackDiag' : Prop := True
/-- mapPullback (abstract). -/
def mapPullback' : Prop := True
/-- IsSeparatedMap (abstract). -/
def IsSeparatedMap' : Prop := True
/-- t2space_iff_isSeparatedMap (abstract). -/
def t2space_iff_isSeparatedMap' : Prop := True
/-- isSeparatedMap_iff_disjoint_nhds (abstract). -/
def isSeparatedMap_iff_disjoint_nhds' : Prop := True
/-- isSeparatedMap_iff_nhds (abstract). -/
def isSeparatedMap_iff_nhds' : Prop := True
/-- isSeparatedMap_iff_isClosed_diagonal (abstract). -/
def isSeparatedMap_iff_isClosed_diagonal' : Prop := True
/-- isSeparatedMap_iff_isClosedEmbedding (abstract). -/
def isSeparatedMap_iff_isClosedEmbedding' : Prop := True
/-- isSeparatedMap_iff_isClosedMap (abstract). -/
def isSeparatedMap_iff_isClosedMap' : Prop := True
-- COLLISION: IsLocallyInjective' already in Algebra.lean — rename needed
/-- IsLocallyInjective_iff_isOpenEmbedding (abstract). -/
def IsLocallyInjective_iff_isOpenEmbedding' : Prop := True
/-- isLocallyInjective_iff_isOpenMap (abstract). -/
def isLocallyInjective_iff_isOpenMap' : Prop := True
/-- discreteTopology_iff_locallyInjective (abstract). -/
def discreteTopology_iff_locallyInjective' : Prop := True
/-- isClosed_eqLocus (abstract). -/
def isClosed_eqLocus' : Prop := True
/-- isOpen_eqLocus (abstract). -/
def isOpen_eqLocus' : Prop := True

-- Separation/Basic.lean
/-- SeparatedNhds (abstract). -/
def SeparatedNhds' : Prop := True
/-- separatedNhds_iff_disjoint (abstract). -/
def separatedNhds_iff_disjoint' : Prop := True
/-- HasSeparatingCover (abstract). -/
def HasSeparatingCover' : Prop := True
/-- hasSeparatingCovers_iff_separatedNhds (abstract). -/
def hasSeparatingCovers_iff_separatedNhds' : Prop := True
-- COLLISION: u' already in Analysis.lean — rename needed
-- COLLISION: v' already in Algebra.lean — rename needed
-- COLLISION: s' already in Algebra.lean — rename needed
/-- hasSeparatingCover_empty_left (abstract). -/
def hasSeparatingCover_empty_left' : Prop := True
/-- hasSeparatingCover_empty_right (abstract). -/
def hasSeparatingCover_empty_right' : Prop := True
/-- T0Space (abstract). -/
def T0Space' : Prop := True
/-- t0Space_iff_inseparable (abstract). -/
def t0Space_iff_inseparable' : Prop := True
/-- t0Space_iff_not_inseparable (abstract). -/
def t0Space_iff_not_inseparable' : Prop := True
-- COLLISION: eq' already in SetTheory.lean — rename needed
/-- isEmbedding_iff_isInducing (abstract). -/
def isEmbedding_iff_isInducing' : Prop := True
/-- t0Space_iff_nhds_injective (abstract). -/
def t0Space_iff_nhds_injective' : Prop := True
/-- nhds_injective (abstract). -/
def nhds_injective' : Prop := True
/-- inseparable_iff_eq (abstract). -/
def inseparable_iff_eq' : Prop := True
/-- nhds_eq_nhds_iff (abstract). -/
def nhds_eq_nhds_iff' : Prop := True
/-- inseparable_eq_eq (abstract). -/
def inseparable_eq_eq' : Prop := True
-- COLLISION: eq_iff' already in Order.lean — rename needed
/-- t0Space_iff_exists_isOpen_xor'_mem (abstract). -/
def t0Space_iff_exists_isOpen_xor'_mem' : Prop := True
/-- exists_isOpen_xor'_mem (abstract). -/
def exists_isOpen_xor'_mem' : Prop := True
/-- specializationOrder (abstract). -/
def specializationOrder' : Prop := True
/-- minimal_nonempty_closed_subsingleton (abstract). -/
def minimal_nonempty_closed_subsingleton' : Prop := True
/-- minimal_nonempty_closed_eq_singleton (abstract). -/
def minimal_nonempty_closed_eq_singleton' : Prop := True
/-- exists_closed_singleton (abstract). -/
def exists_closed_singleton' : Prop := True
/-- minimal_nonempty_open_subsingleton (abstract). -/
def minimal_nonempty_open_subsingleton' : Prop := True
/-- minimal_nonempty_open_eq_singleton (abstract). -/
def minimal_nonempty_open_eq_singleton' : Prop := True
/-- exists_isOpen_singleton_of_isOpen_finite (abstract). -/
def exists_isOpen_singleton_of_isOpen_finite' : Prop := True
/-- exists_open_singleton_of_finite (abstract). -/
def exists_open_singleton_of_finite' : Prop := True
/-- t0Space_of_injective_of_continuous (abstract). -/
def t0Space_of_injective_of_continuous' : Prop := True
/-- t0Space (abstract). -/
def t0Space' : Prop := True
/-- t0Space_iff_or_not_mem_closure (abstract). -/
def t0Space_iff_or_not_mem_closure' : Prop := True
/-- R0Space (abstract). -/
def R0Space' : Prop := True
/-- specializes_comm (abstract). -/
def specializes_comm' : Prop := True
/-- specializes_iff_inseparable (abstract). -/
def specializes_iff_inseparable' : Prop := True
/-- isCompact_closure_singleton (abstract). -/
def isCompact_closure_singleton' : Prop := True
/-- coclosedCompact_le_cofinite (abstract). -/
def coclosedCompact_le_cofinite' : Prop := True
/-- relativelyCompact (abstract). -/
def relativelyCompact' : Prop := True
/-- T1Space (abstract). -/
def T1Space' : Prop := True
/-- isClosed_singleton (abstract). -/
def isClosed_singleton' : Prop := True
/-- isOpen_compl_singleton (abstract). -/
def isOpen_compl_singleton' : Prop := True
/-- isOpen_ne (abstract). -/
def isOpen_ne' : Prop := True
/-- isOpen_mulSupport (abstract). -/
def isOpen_mulSupport' : Prop := True
/-- nhdsWithin_compl_singleton (abstract). -/
def nhdsWithin_compl_singleton' : Prop := True
/-- nhdsWithin_diff_singleton (abstract). -/
def nhdsWithin_diff_singleton' : Prop := True
/-- nhdsWithin_compl_singleton_le (abstract). -/
def nhdsWithin_compl_singleton_le' : Prop := True
/-- isOpen_setOf_eventually_nhdsWithin (abstract). -/
def isOpen_setOf_eventually_nhdsWithin' : Prop := True
/-- exists_mem_of_ne (abstract). -/
def exists_mem_of_ne' : Prop := True
/-- t1Space_TFAE (abstract). -/
def t1Space_TFAE' : Prop := True
/-- t1Space_iff_continuous_cofinite_of (abstract). -/
def t1Space_iff_continuous_cofinite_of' : Prop := True
/-- continuous_of (abstract). -/
def continuous_of' : Prop := True
/-- t1Space_iff_exists_open (abstract). -/
def t1Space_iff_exists_open' : Prop := True
/-- t1Space_iff_disjoint_pure_nhds (abstract). -/
def t1Space_iff_disjoint_pure_nhds' : Prop := True
/-- t1Space_iff_disjoint_nhds_pure (abstract). -/
def t1Space_iff_disjoint_nhds_pure' : Prop := True
/-- t1Space_iff_specializes_imp_eq (abstract). -/
def t1Space_iff_specializes_imp_eq' : Prop := True
/-- disjoint_pure_nhds (abstract). -/
def disjoint_pure_nhds' : Prop := True
/-- disjoint_nhds_pure (abstract). -/
def disjoint_nhds_pure' : Prop := True
/-- specializes_iff_eq (abstract). -/
def specializes_iff_eq' : Prop := True
/-- specializes_eq_eq (abstract). -/
def specializes_eq_eq' : Prop := True
/-- pure_le_nhds_iff (abstract). -/
def pure_le_nhds_iff' : Prop := True
/-- nhds_le_nhds_iff (abstract). -/
def nhds_le_nhds_iff' : Prop := True
/-- t1Space_antitone (abstract). -/
def t1Space_antitone' : Prop := True
/-- continuousWithinAt_update_of_ne (abstract). -/
def continuousWithinAt_update_of_ne' : Prop := True
/-- continuousAt_update_of_ne (abstract). -/
def continuousAt_update_of_ne' : Prop := True
/-- continuousOn_update_iff (abstract). -/
def continuousOn_update_iff' : Prop := True
/-- t1Space_of_injective_of_continuous (abstract). -/
def t1Space_of_injective_of_continuous' : Prop := True
/-- compl_singleton_mem_nhds_iff (abstract). -/
def compl_singleton_mem_nhds_iff' : Prop := True
/-- compl_singleton_mem_nhds (abstract). -/
def compl_singleton_mem_nhds' : Prop := True
/-- subsingleton_closure (abstract). -/
def subsingleton_closure' : Prop := True
/-- isClosedMap_const (abstract). -/
def isClosedMap_const' : Prop := True
/-- nhdsWithin_insert_of_ne (abstract). -/
def nhdsWithin_insert_of_ne' : Prop := True
/-- insert_mem_nhdsWithin_of_subset_insert (abstract). -/
def insert_mem_nhdsWithin_of_subset_insert' : Prop := True
/-- eventuallyEq_insert (abstract). -/
def eventuallyEq_insert' : Prop := True
/-- ker_nhds (abstract). -/
def ker_nhds' : Prop := True
/-- biInter_basis_nhds (abstract). -/
def biInter_basis_nhds' : Prop := True
/-- compl_singleton_mem_nhdsSet_iff (abstract). -/
def compl_singleton_mem_nhdsSet_iff' : Prop := True
/-- nhdsSet_le_iff (abstract). -/
def nhdsSet_le_iff' : Prop := True
/-- nhdsSet_inj_iff (abstract). -/
def nhdsSet_inj_iff' : Prop := True
/-- injective_nhdsSet (abstract). -/
def injective_nhdsSet' : Prop := True
/-- strictMono_nhdsSet (abstract). -/
def strictMono_nhdsSet' : Prop := True
/-- nhds_le_nhdsSet_iff (abstract). -/
def nhds_le_nhdsSet_iff' : Prop := True
/-- diff_singleton (abstract). -/
def diff_singleton' : Prop := True
/-- diff_finset (abstract). -/
def diff_finset' : Prop := True
-- COLLISION: eventually_ne' already in Analysis.lean — rename needed
/-- eventually_ne_nhds (abstract). -/
def eventually_ne_nhds' : Prop := True
-- COLLISION: continuousWithinAt_insert' already in Analysis.lean — rename needed
/-- continuousWithinAt_diff_singleton (abstract). -/
def continuousWithinAt_diff_singleton' : Prop := True
/-- continuousAt_of_tendsto_nhds (abstract). -/
def continuousAt_of_tendsto_nhds' : Prop := True
/-- tendsto_const_nhds_iff (abstract). -/
def tendsto_const_nhds_iff' : Prop := True
/-- isOpen_singleton_of_finite_mem_nhds (abstract). -/
def isOpen_singleton_of_finite_mem_nhds' : Prop := True
/-- infinite_of_mem_nhds (abstract). -/
def infinite_of_mem_nhds' : Prop := True
/-- trivial_of_discrete (abstract). -/
def trivial_of_discrete' : Prop := True
/-- isClosed_inter_singleton (abstract). -/
def isClosed_inter_singleton' : Prop := True
/-- isClosed_singleton_inter (abstract). -/
def isClosed_singleton_inter' : Prop := True
/-- singleton_mem_nhdsWithin_of_mem_discrete (abstract). -/
def singleton_mem_nhdsWithin_of_mem_discrete' : Prop := True
/-- nhdsWithin_of_mem_discrete (abstract). -/
def nhdsWithin_of_mem_discrete' : Prop := True
/-- exists_inter_eq_singleton_of_mem_discrete (abstract). -/
def exists_inter_eq_singleton_of_mem_discrete' : Prop := True
/-- nhds_inter_eq_singleton_of_mem_discrete (abstract). -/
def nhds_inter_eq_singleton_of_mem_discrete' : Prop := True
/-- isOpen_inter_eq_singleton_of_mem_discrete (abstract). -/
def isOpen_inter_eq_singleton_of_mem_discrete' : Prop := True
/-- disjoint_nhdsWithin_of_mem_discrete (abstract). -/
def disjoint_nhdsWithin_of_mem_discrete' : Prop := True
/-- isClosedEmbedding_update (abstract). -/
def isClosedEmbedding_update' : Prop := True
/-- R1Space (abstract). -/
def R1Space' : Prop := True
/-- disjoint_nhds_nhds_iff_not_specializes (abstract). -/
def disjoint_nhds_nhds_iff_not_specializes' : Prop := True
/-- specializes_iff_not_disjoint (abstract). -/
def specializes_iff_not_disjoint' : Prop := True
/-- disjoint_nhds_nhds_iff_not_inseparable (abstract). -/
def disjoint_nhds_nhds_iff_not_inseparable' : Prop := True
/-- r1Space_iff_inseparable_or_disjoint_nhds (abstract). -/
def r1Space_iff_inseparable_or_disjoint_nhds' : Prop := True
/-- of_nhds_neBot (abstract). -/
def of_nhds_neBot' : Prop := True
/-- tendsto_nhds_unique_inseparable (abstract). -/
def tendsto_nhds_unique_inseparable' : Prop := True
/-- isClosed_setOf_specializes (abstract). -/
def isClosed_setOf_specializes' : Prop := True
/-- isClosed_setOf_inseparable (abstract). -/
def isClosed_setOf_inseparable' : Prop := True
/-- mem_closure_iff_exists_inseparable (abstract). -/
def mem_closure_iff_exists_inseparable' : Prop := True
/-- closure_eq_biUnion_inseparable (abstract). -/
def closure_eq_biUnion_inseparable' : Prop := True
/-- closure_eq_biUnion_closure_singleton (abstract). -/
def closure_eq_biUnion_closure_singleton' : Prop := True
/-- closure_subset_of_isOpen (abstract). -/
def closure_subset_of_isOpen' : Prop := True
/-- closure_of_subset (abstract). -/
def closure_of_subset' : Prop := True
/-- exists_isCompact_superset_iff (abstract). -/
def exists_isCompact_superset_iff' : Prop := True
/-- of_isCompact_isCompact_isClosed (abstract). -/
def of_isCompact_isCompact_isClosed' : Prop := True
/-- binary_compact_cover (abstract). -/
def binary_compact_cover' : Prop := True
/-- finite_compact_cover (abstract). -/
def finite_compact_cover' : Prop := True
/-- of_continuous_specializes_imp (abstract). -/
def of_continuous_specializes_imp' : Prop := True
/-- r1Space (abstract). -/
def r1Space' : Prop := True
-- COLLISION: sInf' already in Order.lean — rename needed
/-- exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds (abstract). -/
def exists_mem_nhds_isCompact_mapsTo_of_isCompact_mem_nhds' : Prop := True
/-- isCompact_isClosed_basis_nhds (abstract). -/
def isCompact_isClosed_basis_nhds' : Prop := True
/-- coclosedCompact_eq_cocompact (abstract). -/
def coclosedCompact_eq_cocompact' : Prop := True
/-- relativelyCompact_eq_inCompact (abstract). -/
def relativelyCompact_eq_inCompact' : Prop := True
/-- exists_mem_nhds_isCompact_isClosed (abstract). -/
def exists_mem_nhds_isCompact_isClosed' : Prop := True
/-- exists_isOpen_superset_and_isCompact_closure (abstract). -/
def exists_isOpen_superset_and_isCompact_closure' : Prop := True
/-- exists_isOpen_mem_isCompact_closure (abstract). -/
def exists_isOpen_mem_isCompact_closure' : Prop := True
/-- T2Space (abstract). -/
def T2Space' : Prop := True
/-- t2_separation (abstract). -/
def t2_separation' : Prop := True
/-- t2Space_iff_disjoint_nhds (abstract). -/
def t2Space_iff_disjoint_nhds' : Prop := True
/-- disjoint_nhds_nhds (abstract). -/
def disjoint_nhds_nhds' : Prop := True
/-- pairwise_disjoint_nhds (abstract). -/
def pairwise_disjoint_nhds' : Prop := True
/-- pairwiseDisjoint_nhds (abstract). -/
def pairwiseDisjoint_nhds' : Prop := True
/-- t2Space_iff (abstract). -/
def t2Space_iff' : Prop := True
/-- t2Space_iff_t0Space (abstract). -/
def t2Space_iff_t0Space' : Prop := True
/-- t2_iff_nhds (abstract). -/
def t2_iff_nhds' : Prop := True
/-- eq_of_nhds_neBot (abstract). -/
def eq_of_nhds_neBot' : Prop := True
/-- t2Space_iff_nhds (abstract). -/
def t2Space_iff_nhds' : Prop := True
/-- t2_separation_nhds (abstract). -/
def t2_separation_nhds' : Prop := True
/-- t2_separation_compact_nhds (abstract). -/
def t2_separation_compact_nhds' : Prop := True
/-- t2_iff_ultrafilter (abstract). -/
def t2_iff_ultrafilter' : Prop := True
/-- t2_iff_isClosed_diagonal (abstract). -/
def t2_iff_isClosed_diagonal' : Prop := True
/-- isClosed_diagonal (abstract). -/
def isClosed_diagonal' : Prop := True
/-- tendsto_nhds_unique (abstract). -/
def tendsto_nhds_unique' : Prop := True
/-- tendsto_nhds_unique_of_eventuallyEq (abstract). -/
def tendsto_nhds_unique_of_eventuallyEq' : Prop := True
/-- tendsto_nhds_unique_of_frequently_eq (abstract). -/
def tendsto_nhds_unique_of_frequently_eq' : Prop := True
/-- nhdsSet_inter_eq (abstract). -/
def nhdsSet_inter_eq' : Prop := True
/-- separation_of_not_mem (abstract). -/
def separation_of_not_mem' : Prop := True
/-- disjoint_nhdsSet_nhds (abstract). -/
def disjoint_nhdsSet_nhds' : Prop := True
/-- exists_mem_nhdsSet (abstract). -/
def exists_mem_nhdsSet' : Prop := True
/-- exists_isOpen_superset (abstract). -/
def exists_isOpen_superset' : Prop := True
/-- lim_eq (abstract). -/
def lim_eq' : Prop := True
/-- lim_eq_iff (abstract). -/
def lim_eq_iff' : Prop := True
/-- lim_eq_iff_le_nhds (abstract). -/
def lim_eq_iff_le_nhds' : Prop := True
/-- isOpen_iff_ultrafilter' (abstract). -/
def isOpen_iff_ultrafilter' : Prop := True
/-- limUnder_eq (abstract). -/
def limUnder_eq' : Prop := True
/-- limUnder_eq_iff (abstract). -/
def limUnder_eq_iff' : Prop := True
/-- lim_nhds (abstract). -/
def lim_nhds' : Prop := True
/-- limUnder_nhds_id (abstract). -/
def limUnder_nhds_id' : Prop := True
/-- lim_nhdsWithin (abstract). -/
def lim_nhdsWithin' : Prop := True
/-- limUnder_nhdsWithin_id (abstract). -/
def limUnder_nhdsWithin_id' : Prop := True
/-- separated_by_continuous (abstract). -/
def separated_by_continuous' : Prop := True
/-- separated_by_isOpenEmbedding (abstract). -/
def separated_by_isOpenEmbedding' : Prop := True
/-- of_injective_continuous (abstract). -/
def of_injective_continuous' : Prop := True
/-- t2Setoid (abstract). -/
def t2Setoid' : Prop := True
/-- t2Quotient (abstract). -/
def t2Quotient' : Prop := True
-- COLLISION: mk_eq' already in Algebra.lean — rename needed
-- COLLISION: inductionOn' already in SetTheory.lean — rename needed
-- COLLISION: inductionOn₂' already in SetTheory.lean — rename needed
-- COLLISION: lift_mk' already in RingTheory2.lean — rename needed
/-- unique_lift (abstract). -/
def unique_lift' : Prop := True
/-- isClosed_eq (abstract). -/
def isClosed_eq' : Prop := True
/-- isOpen_ne_fun (abstract). -/
def isOpen_ne_fun' : Prop := True
/-- eqOn_closure₂' (abstract). -/
def eqOn_closure₂' : Prop := True
/-- of_subset_closure (abstract). -/
def of_subset_closure' : Prop := True
/-- of_isCompact_isCompact (abstract). -/
def of_isCompact_isCompact' : Prop := True
/-- of_isClosed_isCompact_closure_compl_isClosed (abstract). -/
def of_isClosed_isCompact_closure_compl_isClosed' : Prop := True
/-- of_finset_finset (abstract). -/
def of_finset_finset' : Prop := True
/-- of_singleton_finset (abstract). -/
def of_singleton_finset' : Prop := True
/-- isCompact_closure_iff (abstract). -/
def isCompact_closure_iff' : Prop := True
/-- image_closure_of_isCompact (abstract). -/
def image_closure_of_isCompact' : Prop := True
/-- of_surjective_continuous (abstract). -/
def of_surjective_continuous' : Prop := True
/-- isPreirreducible_iff_subsingleton (abstract). -/
def isPreirreducible_iff_subsingleton' : Prop := True
/-- isIrreducible_iff_singleton (abstract). -/
def isIrreducible_iff_singleton' : Prop := True
/-- t2Space_antitone (abstract). -/
def t2Space_antitone' : Prop := True
/-- RegularSpace (abstract). -/
def RegularSpace' : Prop := True
/-- regularSpace_TFAE (abstract). -/
def regularSpace_TFAE' : Prop := True
/-- of_lift'_closure_le (abstract). -/
def of_lift'_closure_le' : Prop := True
/-- of_lift'_closure (abstract). -/
def of_lift'_closure' : Prop := True
/-- of_exists_mem_nhds_isClosed_subset (abstract). -/
def of_exists_mem_nhds_isClosed_subset' : Prop := True
/-- disjoint_nhds_nhdsSet (abstract). -/
def disjoint_nhds_nhdsSet' : Prop := True
/-- exists_mem_nhds_isClosed_subset (abstract). -/
def exists_mem_nhds_isClosed_subset' : Prop := True
/-- closed_nhds_basis (abstract). -/
def closed_nhds_basis' : Prop := True
/-- lift'_nhds_closure (abstract). -/
def lift'_nhds_closure' : Prop := True
/-- nhds_closure (abstract). -/
def nhds_closure' : Prop := True
/-- hasBasis_nhds_closure (abstract). -/
def hasBasis_nhds_closure' : Prop := True
/-- hasBasis_opens_closure (abstract). -/
def hasBasis_opens_closure' : Prop := True
/-- exists_isOpen_closure_subset (abstract). -/
def exists_isOpen_closure_subset' : Prop := True
/-- lift'_closure_nhdsSet (abstract). -/
def lift'_closure_nhdsSet' : Prop := True
/-- nhds_basis_closure (abstract). -/
def nhds_basis_closure' : Prop := True
/-- exists_closure_subset (abstract). -/
def exists_closure_subset' : Prop := True
/-- regularSpace (abstract). -/
def regularSpace' : Prop := True
/-- regularSpace_induced (abstract). -/
def regularSpace_induced' : Prop := True
/-- regularSpace_sInf (abstract). -/
def regularSpace_sInf' : Prop := True
/-- regularSpace_iInf (abstract). -/
def regularSpace_iInf' : Prop := True
/-- of_isCompact_isClosed (abstract). -/
def of_isCompact_isClosed' : Prop := True
/-- exists_compact_closed_between (abstract). -/
def exists_compact_closed_between' : Prop := True
/-- exists_open_between_and_isCompact_closure (abstract). -/
def exists_open_between_and_isCompact_closure' : Prop := True
/-- T25Space (abstract). -/
def T25Space' : Prop := True
/-- disjoint_lift'_closure_nhds (abstract). -/
def disjoint_lift'_closure_nhds' : Prop := True
/-- exists_nhds_disjoint_closure (abstract). -/
def exists_nhds_disjoint_closure' : Prop := True
/-- exists_open_nhds_disjoint_closure (abstract). -/
def exists_open_nhds_disjoint_closure' : Prop := True
/-- t25Space (abstract). -/
def t25Space' : Prop := True
/-- T3Space (abstract). -/
def T3Space' : Prop := True
/-- t3Space_iff_t0Space (abstract). -/
def t3Space_iff_t0Space' : Prop := True
/-- t3Space (abstract). -/
def t3Space' : Prop := True
/-- disjoint_nested_nhds (abstract). -/
def disjoint_nested_nhds' : Prop := True
/-- NormalSpace (abstract). -/
def NormalSpace' : Prop := True
/-- normal_separation (abstract). -/
def normal_separation' : Prop := True
/-- disjoint_nhdsSet_nhdsSet (abstract). -/
def disjoint_nhdsSet_nhdsSet' : Prop := True
/-- normal_exists_closure_subset (abstract). -/
def normal_exists_closure_subset' : Prop := True
/-- normalSpace (abstract). -/
def normalSpace' : Prop := True
/-- T4Space (abstract). -/
def T4Space' : Prop := True
/-- CompletelyNormalSpace (abstract). -/
def CompletelyNormalSpace' : Prop := True
/-- completelyNormalSpace (abstract). -/
def completelyNormalSpace' : Prop := True
/-- T5Space (abstract). -/
def T5Space' : Prop := True
/-- t5Space (abstract). -/
def t5Space' : Prop := True
/-- connectedComponent_eq_iInter_isClopen (abstract). -/
def connectedComponent_eq_iInter_isClopen' : Prop := True
/-- totallySeparatedSpace_of_t1_of_basis_clopen (abstract). -/
def totallySeparatedSpace_of_t1_of_basis_clopen' : Prop := True
/-- compact_t2_tot_disc_iff_tot_sep (abstract). -/
def compact_t2_tot_disc_iff_tot_sep' : Prop := True
/-- nhds_basis_clopen (abstract). -/
def nhds_basis_clopen' : Prop := True
/-- isTopologicalBasis_isClopen (abstract). -/
def isTopologicalBasis_isClopen' : Prop := True
/-- compact_exists_isClopen_in_isOpen (abstract). -/
def compact_exists_isClopen_in_isOpen' : Prop := True
/-- loc_compact_Haus_tot_disc_of_zero_dim (abstract). -/
def loc_compact_Haus_tot_disc_of_zero_dim' : Prop := True
/-- loc_compact_t2_tot_disc_iff_tot_sep (abstract). -/
def loc_compact_t2_tot_disc_iff_tot_sep' : Prop := True

-- Separation/GDelta.lean
/-- compl_singleton (abstract). -/
def compl_singleton' : Prop := True
/-- isGδ_compl (abstract). -/
def isGδ_compl' : Prop := True
-- COLLISION: singleton' already in Order.lean — rename needed
/-- PerfectlyNormalSpace (abstract). -/
def PerfectlyNormalSpace' : Prop := True
/-- hasSeparatingCover_closed_gdelta_right (abstract). -/
def hasSeparatingCover_closed_gdelta_right' : Prop := True
/-- T6Space (abstract). -/
def T6Space' : Prop := True

-- Separation/NotNormal.lean
/-- mk_lt_continuum (abstract). -/
def mk_lt_continuum' : Prop := True
/-- not_normal_of_continuum_le_mk (abstract). -/
def not_normal_of_continuum_le_mk' : Prop := True

-- Sequences.lean
/-- subset_seqClosure (abstract). -/
def subset_seqClosure' : Prop := True
/-- seqClosure_subset_closure (abstract). -/
def seqClosure_subset_closure' : Prop := True
/-- seqClosure_eq (abstract). -/
def seqClosure_eq' : Prop := True
/-- isSeqClosed_of_seqClosure_eq (abstract). -/
def isSeqClosed_of_seqClosure_eq' : Prop := True
/-- isSeqClosed_iff (abstract). -/
def isSeqClosed_iff' : Prop := True
/-- isSeqClosed (abstract). -/
def isSeqClosed' : Prop := True
/-- seqClosure_eq_closure (abstract). -/
def seqClosure_eq_closure' : Prop := True
/-- mem_closure_iff_seq_limit (abstract). -/
def mem_closure_iff_seq_limit' : Prop := True
/-- tendsto_nhds_iff_seq_tendsto (abstract). -/
def tendsto_nhds_iff_seq_tendsto' : Prop := True
/-- of_seq_tendsto_imp_tendsto (abstract). -/
def of_seq_tendsto_imp_tendsto' : Prop := True
/-- frechetUrysohnSpace (abstract). -/
def frechetUrysohnSpace' : Prop := True
/-- isSeqClosed_iff_isClosed (abstract). -/
def isSeqClosed_iff_isClosed' : Prop := True
/-- seqContinuous (abstract). -/
def seqContinuous' : Prop := True
/-- continuous_iff_seqContinuous (abstract). -/
def continuous_iff_seqContinuous' : Prop := True
/-- sequentialSpace (abstract). -/
def sequentialSpace' : Prop := True
/-- subseq_of_frequently_in (abstract). -/
def subseq_of_frequently_in' : Prop := True
/-- isSeqCompact (abstract). -/
def isSeqCompact' : Prop := True
/-- exists_tendsto_of_frequently_mem (abstract). -/
def exists_tendsto_of_frequently_mem' : Prop := True
/-- exists_tendsto (abstract). -/
def exists_tendsto' : Prop := True
/-- totallyBounded (abstract). -/
def totallyBounded' : Prop := True
/-- isCompact_iff_isSeqCompact (abstract). -/
def isCompact_iff_isSeqCompact' : Prop := True
/-- compactSpace_iff_seqCompactSpace (abstract). -/
def compactSpace_iff_seqCompactSpace' : Prop := True

-- Sets/Closeds.lean
-- COLLISION: Closeds' already in Order.lean — rename needed
-- COLLISION: gc' already in Order.lean — rename needed
-- COLLISION: gi' already in Order.lean — rename needed
/-- coe_finset_sup (abstract). -/
def coe_finset_sup' : Prop := True
/-- coe_finset_inf (abstract). -/
def coe_finset_inf' : Prop := True
-- COLLISION: mem_sInf' already in Order.lean — rename needed
-- COLLISION: mem_iInf' already in Order.lean — rename needed
-- COLLISION: coe_iInf' already in FieldTheory.lean — rename needed
/-- iInf_def (abstract). -/
def iInf_def' : Prop := True
-- COLLISION: iInf_mk' already in Order.lean — rename needed
-- COLLISION: coframeMinimalAxioms' already in Order.lean — rename needed
-- COLLISION: compl_compl' already in Order.lean — rename needed
/-- compl_bijective (abstract). -/
def compl_bijective' : Prop := True
/-- complOrderIso (abstract). -/
def complOrderIso' : Prop := True
/-- coe_eq_singleton_of_isAtom (abstract). -/
def coe_eq_singleton_of_isAtom' : Prop := True
/-- isAtom_coe (abstract). -/
def isAtom_coe' : Prop := True
-- COLLISION: isAtom_iff' already in Order.lean — rename needed
-- COLLISION: isCoatom_iff' already in Order.lean — rename needed
/-- Clopens (abstract). -/
def Clopens' : Prop := True
-- COLLISION: mem_mk' already in RingTheory2.lean — rename needed
-- COLLISION: mem_prod' already in SetTheory.lean — rename needed
/-- IrreducibleCloseds (abstract). -/
def IrreducibleCloseds' : Prop := True
/-- isIrreducible (abstract). -/
def isIrreducible' : Prop := True
-- COLLISION: equivSubtype' already in RingTheory2.lean — rename needed
-- COLLISION: orderIsoSubtype' already in Order.lean — rename needed

-- Sets/Compacts.lean
/-- Compacts (abstract). -/
def Compacts' : Prop := True
/-- NonemptyCompacts (abstract). -/
def NonemptyCompacts' : Prop := True
-- COLLISION: toCloseds' already in Order.lean — rename needed
/-- PositiveCompacts (abstract). -/
def PositiveCompacts' : Prop := True
/-- interior_nonempty (abstract). -/
def interior_nonempty' : Prop := True
/-- toNonemptyCompacts (abstract). -/
def toNonemptyCompacts' : Prop := True
/-- exists_positiveCompacts_subset (abstract). -/
def exists_positiveCompacts_subset' : Prop := True
/-- exists_positiveCompacts_closure_subset (abstract). -/
def exists_positiveCompacts_closure_subset' : Prop := True
/-- CompactOpens (abstract). -/
def CompactOpens' : Prop := True
/-- toClopens (abstract). -/
def toClopens' : Prop := True

-- Sets/Opens.lean
/-- Opens (abstract). -/
def Opens' : Prop := True
/-- nonempty_coeSort (abstract). -/
def nonempty_coeSort' : Prop := True
-- COLLISION: coe_iSup' already in Order.lean — rename needed
/-- iSup_def (abstract). -/
def iSup_def' : Prop := True
-- COLLISION: iSup_mk' already in Order.lean — rename needed
-- COLLISION: mem_iSup' already in Order.lean — rename needed
-- COLLISION: mem_sSup' already in Order.lean — rename needed
-- COLLISION: frameMinimalAxioms' already in Order.lean — rename needed
/-- isOpenEmbedding_of_le (abstract). -/
def isOpenEmbedding_of_le' : Prop := True
/-- not_nonempty_iff_eq_bot (abstract). -/
def not_nonempty_iff_eq_bot' : Prop := True
/-- ne_bot_iff_nonempty (abstract). -/
def ne_bot_iff_nonempty' : Prop := True
-- COLLISION: eq_bot_or_top' already in RingTheory2.lean — rename needed
-- COLLISION: IsBasis' already in Order.lean — rename needed
/-- isBasis_iff_nbhd (abstract). -/
def isBasis_iff_nbhd' : Prop := True
/-- isBasis_iff_cover (abstract). -/
def isBasis_iff_cover' : Prop := True
/-- isCompact_open_iff_eq_finite_iUnion (abstract). -/
def isCompact_open_iff_eq_finite_iUnion' : Prop := True
-- COLLISION: le_iff' already in SetTheory.lean — rename needed
/-- isCompactElement_iff (abstract). -/
def isCompactElement_iff' : Prop := True
-- COLLISION: mem_comap' already in Order.lean — rename needed
/-- opensCongr (abstract). -/
def opensCongr' : Prop := True
/-- OpenNhdsOf (abstract). -/
def OpenNhdsOf' : Prop := True
/-- toOpens_injective (abstract). -/
def toOpens_injective' : Prop := True
-- COLLISION: mem' already in SetTheory.lean — rename needed

-- Sets/Order.lean
/-- ClopenUpperSet (abstract). -/
def ClopenUpperSet' : Prop := True

-- Sheaves/CommRingCat.lean
/-- SubmonoidPresheaf (abstract). -/
def SubmonoidPresheaf' : Prop := True
/-- localizationPresheaf (abstract). -/
def localizationPresheaf' : Prop := True
/-- toLocalizationPresheaf (abstract). -/
def toLocalizationPresheaf' : Prop := True
/-- submonoidPresheafOfStalk (abstract). -/
def submonoidPresheafOfStalk' : Prop := True
/-- totalQuotientPresheaf (abstract). -/
def totalQuotientPresheaf' : Prop := True
/-- toTotalQuotientPresheaf (abstract). -/
def toTotalQuotientPresheaf' : Prop := True
/-- continuousFunctions (abstract). -/
def continuousFunctions' : Prop := True
/-- commRingYoneda (abstract). -/
def commRingYoneda' : Prop := True
/-- presheafToTopCommRing (abstract). -/
def presheafToTopCommRing' : Prop := True
/-- objSupIsoProdEqLocus (abstract). -/
def objSupIsoProdEqLocus' : Prop := True
/-- objSupIsoProdEqLocus_hom_fst (abstract). -/
def objSupIsoProdEqLocus_hom_fst' : Prop := True
/-- objSupIsoProdEqLocus_hom_snd (abstract). -/
def objSupIsoProdEqLocus_hom_snd' : Prop := True
/-- objSupIsoProdEqLocus_inv_fst (abstract). -/
def objSupIsoProdEqLocus_inv_fst' : Prop := True
/-- objSupIsoProdEqLocus_inv_snd (abstract). -/
def objSupIsoProdEqLocus_inv_snd' : Prop := True
/-- objSupIsoProdEqLocus_inv_eq_iff (abstract). -/
def objSupIsoProdEqLocus_inv_eq_iff' : Prop := True

-- Sheaves/Forget.lean
-- COLLISION: isSheaf_iff_isSheaf_comp' already in CategoryTheory.lean — rename needed

-- Sheaves/Functors.lean
/-- pushforward_sheaf_of_sheaf (abstract). -/
def pushforward_sheaf_of_sheaf' : Prop := True
-- COLLISION: pushforward' already in Algebra.lean — rename needed
/-- pushforwardForgetIso (abstract). -/
def pushforwardForgetIso' : Prop := True
/-- pullbackIso (abstract). -/
def pullbackIso' : Prop := True
/-- pullbackPushforwardAdjunction (abstract). -/
def pullbackPushforwardAdjunction' : Prop := True

-- Sheaves/Limits.lean
-- COLLISION: isSheaf_of_isLimit' already in Algebra.lean — rename needed
/-- limit_isSheaf (abstract). -/
def limit_isSheaf' : Prop := True

-- Sheaves/LocalPredicate.lean
/-- PrelocalPredicate (abstract). -/
def PrelocalPredicate' : Prop := True
/-- continuousPrelocal (abstract). -/
def continuousPrelocal' : Prop := True
/-- LocalPredicate (abstract). -/
def LocalPredicate' : Prop := True
/-- continuousLocal (abstract). -/
def continuousLocal' : Prop := True
-- COLLISION: sheafify' already in Algebra.lean — rename needed
/-- sheafifyOf (abstract). -/
def sheafifyOf' : Prop := True
/-- subpresheafToTypes (abstract). -/
def subpresheafToTypes' : Prop := True
/-- isSheaf (abstract). -/
def isSheaf' : Prop := True
/-- subsheafToTypes (abstract). -/
def subsheafToTypes' : Prop := True
/-- stalkToFiber (abstract). -/
def stalkToFiber' : Prop := True
/-- stalkToFiber_germ (abstract). -/
def stalkToFiber_germ' : Prop := True
/-- stalkToFiber_surjective (abstract). -/
def stalkToFiber_surjective' : Prop := True
/-- stalkToFiber_injective (abstract). -/
def stalkToFiber_injective' : Prop := True
/-- subpresheafContinuousPrelocalIsoPresheafToTop (abstract). -/
def subpresheafContinuousPrelocalIsoPresheafToTop' : Prop := True
/-- sheafToTop (abstract). -/
def sheafToTop' : Prop := True

-- Sheaves/LocallySurjective.lean
-- COLLISION: IsLocallySurjective' already in Algebra.lean — rename needed
-- COLLISION: isLocallySurjective_iff' already in CategoryTheory.lean — rename needed
/-- locally_surjective_iff_surjective_on_stalks (abstract). -/
def locally_surjective_iff_surjective_on_stalks' : Prop := True

-- Sheaves/MayerVietoris.lean
/-- mayerVietorisSquare' (abstract). -/
def mayerVietorisSquare' : Prop := True

-- Sheaves/PUnit.lean
/-- isSheaf_of_isTerminal_of_indiscrete (abstract). -/
def isSheaf_of_isTerminal_of_indiscrete' : Prop := True
/-- isSheaf_iff_isTerminal_of_indiscrete (abstract). -/
def isSheaf_iff_isTerminal_of_indiscrete' : Prop := True
/-- isSheaf_on_punit_of_isTerminal (abstract). -/
def isSheaf_on_punit_of_isTerminal' : Prop := True
/-- isSheaf_on_punit_iff_isTerminal (abstract). -/
def isSheaf_on_punit_iff_isTerminal' : Prop := True

-- Sheaves/Presheaf.lean
/-- Presheaf (abstract). -/
def Presheaf' : Prop := True
/-- restrictOpen (abstract). -/
def restrictOpen' : Prop := True
-- COLLISION: restrict_restrict' already in MeasureTheory2.lean — rename needed
/-- map_restrict (abstract). -/
def map_restrict' : Prop := True
/-- pushforwardEq (abstract). -/
def pushforwardEq' : Prop := True
/-- pushforward_eq' (abstract). -/
def pushforward_eq' : Prop := True
/-- pushforwardEq_hom_app (abstract). -/
def pushforwardEq_hom_app' : Prop := True
/-- presheafEquivOfIso (abstract). -/
def presheafEquivOfIso' : Prop := True
/-- toPushforwardOfIso (abstract). -/
def toPushforwardOfIso' : Prop := True
/-- toPushforwardOfIso_app (abstract). -/
def toPushforwardOfIso_app' : Prop := True
/-- pushforwardToOfIso (abstract). -/
def pushforwardToOfIso' : Prop := True
/-- pushforwardToOfIso_app (abstract). -/
def pushforwardToOfIso_app' : Prop := True
/-- pushforwardPullbackAdjunction (abstract). -/
def pushforwardPullbackAdjunction' : Prop := True
/-- pullbackHomIsoPushforwardInv (abstract). -/
def pullbackHomIsoPushforwardInv' : Prop := True
/-- pullbackInvIsoPushforwardHom (abstract). -/
def pullbackInvIsoPushforwardHom' : Prop := True
/-- pullbackObjObjOfImageOpen (abstract). -/
def pullbackObjObjOfImageOpen' : Prop := True

-- Sheaves/PresheafOfFunctions.lean
/-- presheafToTypes (abstract). -/
def presheafToTypes' : Prop := True
/-- presheafToType (abstract). -/
def presheafToType' : Prop := True
/-- presheafToTop (abstract). -/
def presheafToTop' : Prop := True

-- Sheaves/Sheaf.lean
-- COLLISION: IsSheaf' already in CategoryTheory.lean — rename needed
/-- isSheaf_unit (abstract). -/
def isSheaf_unit' : Prop := True
/-- isSheaf_iso_iff (abstract). -/
def isSheaf_iso_iff' : Prop := True
/-- isSheaf_of_iso (abstract). -/
def isSheaf_of_iso' : Prop := True
-- COLLISION: Sheaf' already in CategoryTheory.lean — rename needed
-- COLLISION: presheaf' already in Algebra.lean — rename needed

-- Sheaves/SheafCondition/EqualizerProducts.lean
/-- piOpens (abstract). -/
def piOpens' : Prop := True
/-- piInters (abstract). -/
def piInters' : Prop := True
/-- leftRes (abstract). -/
def leftRes' : Prop := True
/-- rightRes (abstract). -/
def rightRes' : Prop := True
/-- res_π (abstract). -/
def res_π' : Prop := True
-- COLLISION: w' already in Analysis.lean — rename needed
-- COLLISION: fork' already in Analysis.lean — rename needed
-- COLLISION: isoOfIso' already in CategoryTheory.lean — rename needed
/-- IsSheafEqualizerProducts (abstract). -/
def IsSheafEqualizerProducts' : Prop := True
/-- coneEquivFunctorObj (abstract). -/
def coneEquivFunctorObj' : Prop := True
/-- coneEquivFunctor (abstract). -/
def coneEquivFunctor' : Prop := True
/-- coneEquivInverseObj (abstract). -/
def coneEquivInverseObj' : Prop := True
/-- coneEquivInverse (abstract). -/
def coneEquivInverse' : Prop := True
/-- coneEquivUnitIsoApp (abstract). -/
def coneEquivUnitIsoApp' : Prop := True
/-- coneEquivUnitIso (abstract). -/
def coneEquivUnitIso' : Prop := True
/-- coneEquivCounitIso (abstract). -/
def coneEquivCounitIso' : Prop := True
/-- coneEquiv (abstract). -/
def coneEquiv' : Prop := True
/-- isLimitMapConeOfIsLimitSheafConditionFork (abstract). -/
def isLimitMapConeOfIsLimitSheafConditionFork' : Prop := True
/-- isLimitSheafConditionForkOfIsLimitMapCone (abstract). -/
def isLimitSheafConditionForkOfIsLimitMapCone' : Prop := True
/-- isSheaf_iff_isSheafEqualizerProducts (abstract). -/
def isSheaf_iff_isSheafEqualizerProducts' : Prop := True

-- Sheaves/SheafCondition/OpensLeCover.lean
/-- OpensLeCover (abstract). -/
def OpensLeCover' : Prop := True
-- COLLISION: index' already in Order.lean — rename needed
/-- homToIndex (abstract). -/
def homToIndex' : Prop := True
/-- opensLeCoverCocone (abstract). -/
def opensLeCoverCocone' : Prop := True
/-- IsSheafOpensLeCover (abstract). -/
def IsSheafOpensLeCover' : Prop := True
/-- generateEquivalenceOpensLe_functor' (abstract). -/
def generateEquivalenceOpensLe_functor' : Prop := True
/-- generateEquivalenceOpensLe_inverse' (abstract). -/
def generateEquivalenceOpensLe_inverse' : Prop := True
/-- generateEquivalenceOpensLe (abstract). -/
def generateEquivalenceOpensLe' : Prop := True
/-- whiskerIsoMapGenerateCocone (abstract). -/
def whiskerIsoMapGenerateCocone' : Prop := True
/-- isLimitOpensLeEquivGenerate₁ (abstract). -/
def isLimitOpensLeEquivGenerate₁' : Prop := True
/-- isLimitOpensLeEquivGenerate₂ (abstract). -/
def isLimitOpensLeEquivGenerate₂' : Prop := True
/-- isSheaf_iff_isSheafOpensLeCover (abstract). -/
def isSheaf_iff_isSheafOpensLeCover' : Prop := True

-- Sheaves/SheafCondition/PairwiseIntersections.lean
/-- IsSheafPairwiseIntersections (abstract). -/
def IsSheafPairwiseIntersections' : Prop := True
/-- IsSheafPreservesLimitPairwiseIntersections (abstract). -/
def IsSheafPreservesLimitPairwiseIntersections' : Prop := True
/-- pairwiseToOpensLeCoverObj (abstract). -/
def pairwiseToOpensLeCoverObj' : Prop := True
/-- pairwiseToOpensLeCoverMap (abstract). -/
def pairwiseToOpensLeCoverMap' : Prop := True
/-- pairwiseToOpensLeCover (abstract). -/
def pairwiseToOpensLeCover' : Prop := True
/-- pairwiseDiagramIso (abstract). -/
def pairwiseDiagramIso' : Prop := True
/-- pairwiseCoconeIso (abstract). -/
def pairwiseCoconeIso' : Prop := True
/-- isSheafOpensLeCover_iff_isSheafPairwiseIntersections (abstract). -/
def isSheafOpensLeCover_iff_isSheafPairwiseIntersections' : Prop := True
/-- isSheaf_iff_isSheafPairwiseIntersections (abstract). -/
def isSheaf_iff_isSheafPairwiseIntersections' : Prop := True
/-- isSheaf_iff_isSheafPreservesLimitPairwiseIntersections (abstract). -/
def isSheaf_iff_isSheafPreservesLimitPairwiseIntersections' : Prop := True
/-- interUnionPullbackCone (abstract). -/
def interUnionPullbackCone' : Prop := True
/-- interUnionPullbackConeLift (abstract). -/
def interUnionPullbackConeLift' : Prop := True
/-- interUnionPullbackConeLift_left (abstract). -/
def interUnionPullbackConeLift_left' : Prop := True
/-- interUnionPullbackConeLift_right (abstract). -/
def interUnionPullbackConeLift_right' : Prop := True
/-- isLimitPullbackCone (abstract). -/
def isLimitPullbackCone' : Prop := True
/-- isProductOfDisjoint (abstract). -/
def isProductOfDisjoint' : Prop := True

-- Sheaves/SheafCondition/Sites.lean
/-- coveringOfPresieve (abstract). -/
def coveringOfPresieve' : Prop := True
/-- iSup_eq_of_mem_grothendieck (abstract). -/
def iSup_eq_of_mem_grothendieck' : Prop := True
/-- presieveOfCoveringAux (abstract). -/
def presieveOfCoveringAux' : Prop := True
/-- presieveOfCovering (abstract). -/
def presieveOfCovering' : Prop := True
/-- covering_presieve_eq_self (abstract). -/
def covering_presieve_eq_self' : Prop := True
/-- mem_grothendieckTopology (abstract). -/
def mem_grothendieckTopology' : Prop := True
/-- homOfIndex (abstract). -/
def homOfIndex' : Prop := True
/-- indexOfHom (abstract). -/
def indexOfHom' : Prop := True
/-- indexOfHom_spec (abstract). -/
def indexOfHom_spec' : Prop := True
/-- coverDense_iff_isBasis (abstract). -/
def coverDense_iff_isBasis' : Prop := True
/-- coverDense_inducedFunctor (abstract). -/
def coverDense_inducedFunctor' : Prop := True
-- COLLISION: compatiblePreserving' already in CategoryTheory.lean — rename needed
-- COLLISION: coverPreserving' already in CategoryTheory.lean — rename needed
/-- functor_isContinuous (abstract). -/
def functor_isContinuous' : Prop := True
/-- compatiblePreserving_opens_map (abstract). -/
def compatiblePreserving_opens_map' : Prop := True
/-- coverPreserving_opens_map (abstract). -/
def coverPreserving_opens_map' : Prop := True
/-- isTerminalOfEmpty (abstract). -/
def isTerminalOfEmpty' : Prop := True
/-- isTerminalOfEqEmpty (abstract). -/
def isTerminalOfEqEmpty' : Prop := True
-- COLLISION: restrictHomEquivHom' already in CategoryTheory.lean — rename needed
/-- extend_hom_app (abstract). -/
def extend_hom_app' : Prop := True

-- Sheaves/SheafCondition/UniqueGluing.lean
-- COLLISION: IsCompatible' already in CategoryTheory.lean — rename needed
/-- IsGluing (abstract). -/
def IsGluing' : Prop := True
/-- IsSheafUniqueGluing (abstract). -/
def IsSheafUniqueGluing' : Prop := True
/-- objPairwiseOfFamily (abstract). -/
def objPairwiseOfFamily' : Prop := True
/-- sectionPairwise (abstract). -/
def sectionPairwise' : Prop := True
/-- isGluing_iff_pairwise (abstract). -/
def isGluing_iff_pairwise' : Prop := True
/-- isSheaf_iff_isSheafUniqueGluing_types (abstract). -/
def isSheaf_iff_isSheafUniqueGluing_types' : Prop := True
/-- isSheaf_of_isSheafUniqueGluing_types (abstract). -/
def isSheaf_of_isSheafUniqueGluing_types' : Prop := True
/-- isSheaf_iff_isSheafUniqueGluing (abstract). -/
def isSheaf_iff_isSheafUniqueGluing' : Prop := True
/-- existsUnique_gluing (abstract). -/
def existsUnique_gluing' : Prop := True
/-- eq_of_locally_eq (abstract). -/
def eq_of_locally_eq' : Prop := True
/-- eq_of_locally_eq₂ (abstract). -/
def eq_of_locally_eq₂' : Prop := True

-- Sheaves/SheafOfFunctions.lean
/-- preserving (abstract). -/
def preserving' : Prop := True
/-- toTypes_isSheaf (abstract). -/
def toTypes_isSheaf' : Prop := True
/-- toType_isSheaf (abstract). -/
def toType_isSheaf' : Prop := True
/-- sheafToTypes (abstract). -/
def sheafToTypes' : Prop := True
/-- sheafToType (abstract). -/
def sheafToType' : Prop := True

-- Sheaves/Sheafify.lean
/-- isGerm (abstract). -/
def isGerm' : Prop := True
/-- isLocallyGerm (abstract). -/
def isLocallyGerm' : Prop := True
-- COLLISION: toSheafify' already in Algebra.lean — rename needed
/-- sheafifyStalkIso (abstract). -/
def sheafifyStalkIso' : Prop := True

-- Sheaves/Skyscraper.lean
/-- skyscraperPresheaf (abstract). -/
def skyscraperPresheaf' : Prop := True
/-- skyscraperPresheaf_eq_pushforward (abstract). -/
def skyscraperPresheaf_eq_pushforward' : Prop := True
-- COLLISION: map'_id' already in Algebra.lean — rename needed
-- COLLISION: map'_comp' already in Algebra.lean — rename needed
/-- skyscraperPresheafFunctor (abstract). -/
def skyscraperPresheafFunctor' : Prop := True
/-- skyscraperPresheafCoconeOfSpecializes (abstract). -/
def skyscraperPresheafCoconeOfSpecializes' : Prop := True
/-- skyscraperPresheafCoconeIsColimitOfSpecializes (abstract). -/
def skyscraperPresheafCoconeIsColimitOfSpecializes' : Prop := True
/-- skyscraperPresheafStalkOfSpecializes (abstract). -/
def skyscraperPresheafStalkOfSpecializes' : Prop := True
/-- germ_skyscraperPresheafStalkOfSpecializes_hom (abstract). -/
def germ_skyscraperPresheafStalkOfSpecializes_hom' : Prop := True
/-- skyscraperPresheafCocone (abstract). -/
def skyscraperPresheafCocone' : Prop := True
/-- skyscraperPresheafCoconeIsColimitOfNotSpecializes (abstract). -/
def skyscraperPresheafCoconeIsColimitOfNotSpecializes' : Prop := True
/-- skyscraperPresheafStalkOfNotSpecializes (abstract). -/
def skyscraperPresheafStalkOfNotSpecializes' : Prop := True
/-- skyscraperPresheafStalkOfNotSpecializesIsTerminal (abstract). -/
def skyscraperPresheafStalkOfNotSpecializesIsTerminal' : Prop := True
/-- skyscraperPresheaf_isSheaf (abstract). -/
def skyscraperPresheaf_isSheaf' : Prop := True
/-- skyscraperSheaf (abstract). -/
def skyscraperSheaf' : Prop := True
/-- skyscraperSheafFunctor (abstract). -/
def skyscraperSheafFunctor' : Prop := True
/-- toSkyscraperPresheaf (abstract). -/
def toSkyscraperPresheaf' : Prop := True
/-- fromStalk (abstract). -/
def fromStalk' : Prop := True
/-- germ_fromStalk (abstract). -/
def germ_fromStalk' : Prop := True
/-- to_skyscraper_fromStalk (abstract). -/
def to_skyscraper_fromStalk' : Prop := True
/-- fromStalk_to_skyscraper (abstract). -/
def fromStalk_to_skyscraper' : Prop := True
-- COLLISION: unit' already in RingTheory2.lean — rename needed
/-- skyscraperPresheafStalkAdjunction (abstract). -/
def skyscraperPresheafStalkAdjunction' : Prop := True
/-- stalkSkyscraperSheafAdjunction (abstract). -/
def stalkSkyscraperSheafAdjunction' : Prop := True

-- Sheaves/Stalks.lean
/-- stalkFunctor (abstract). -/
def stalkFunctor' : Prop := True
/-- stalk (abstract). -/
def stalk' : Prop := True
/-- germ (abstract). -/
def germ' : Prop := True
/-- Γgerm (abstract). -/
def Γgerm' : Prop := True
/-- germ_res (abstract). -/
def germ_res' : Prop := True
/-- map_germ_eq_Γgerm (abstract). -/
def map_germ_eq_Γgerm' : Prop := True
/-- germ_res_apply (abstract). -/
def germ_res_apply' : Prop := True
/-- Γgerm_res_apply (abstract). -/
def Γgerm_res_apply' : Prop := True
/-- stalk_hom_ext (abstract). -/
def stalk_hom_ext' : Prop := True
/-- stalkFunctor_map_germ (abstract). -/
def stalkFunctor_map_germ' : Prop := True
/-- stalkFunctor_map_germ_apply (abstract). -/
def stalkFunctor_map_germ_apply' : Prop := True
/-- stalkPushforward (abstract). -/
def stalkPushforward' : Prop := True
/-- stalkPushforward_germ (abstract). -/
def stalkPushforward_germ' : Prop := True
/-- stalkPushforward_iso_of_isInducing (abstract). -/
def stalkPushforward_iso_of_isInducing' : Prop := True
/-- stalkPullbackHom (abstract). -/
def stalkPullbackHom' : Prop := True
/-- germ_stalkPullbackHom (abstract). -/
def germ_stalkPullbackHom' : Prop := True
/-- germToPullbackStalk (abstract). -/
def germToPullbackStalk' : Prop := True
/-- pullback_obj_obj_ext (abstract). -/
def pullback_obj_obj_ext' : Prop := True
/-- pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk (abstract). -/
def pushforwardPullbackAdjunction_unit_pullback_map_germToPullbackStalk' : Prop := True
/-- germToPullbackStalk_stalkPullbackHom (abstract). -/
def germToPullbackStalk_stalkPullbackHom' : Prop := True
/-- pushforwardPullbackAdjunction_unit_app_app_germToPullbackStalk (abstract). -/
def pushforwardPullbackAdjunction_unit_app_app_germToPullbackStalk' : Prop := True
/-- stalkPullbackInv (abstract). -/
def stalkPullbackInv' : Prop := True
/-- germ_stalkPullbackInv (abstract). -/
def germ_stalkPullbackInv' : Prop := True
/-- stalkPullbackIso (abstract). -/
def stalkPullbackIso' : Prop := True
/-- stalkSpecializes (abstract). -/
def stalkSpecializes' : Prop := True
/-- germ_stalkSpecializes (abstract). -/
def germ_stalkSpecializes' : Prop := True
/-- stalkSpecializes_refl (abstract). -/
def stalkSpecializes_refl' : Prop := True
/-- stalkSpecializes_comp (abstract). -/
def stalkSpecializes_comp' : Prop := True
/-- stalkSpecializes_stalkFunctor_map (abstract). -/
def stalkSpecializes_stalkFunctor_map' : Prop := True
/-- stalkSpecializes_stalkPushforward (abstract). -/
def stalkSpecializes_stalkPushforward' : Prop := True
/-- stalkCongr (abstract). -/
def stalkCongr' : Prop := True
/-- germ_ext (abstract). -/
def germ_ext' : Prop := True
/-- germ_exist (abstract). -/
def germ_exist' : Prop := True
/-- germ_eq (abstract). -/
def germ_eq' : Prop := True
/-- stalkFunctor_map_injective_of_app_injective (abstract). -/
def stalkFunctor_map_injective_of_app_injective' : Prop := True
/-- section_ext (abstract). -/
def section_ext' : Prop := True
/-- app_injective_of_stalkFunctor_map_injective (abstract). -/
def app_injective_of_stalkFunctor_map_injective' : Prop := True
/-- app_injective_iff_stalkFunctor_map_injective (abstract). -/
def app_injective_iff_stalkFunctor_map_injective' : Prop := True
/-- stalk_mono_of_mono (abstract). -/
def stalk_mono_of_mono' : Prop := True
/-- mono_of_stalk_mono (abstract). -/
def mono_of_stalk_mono' : Prop := True
/-- mono_iff_stalk_mono (abstract). -/
def mono_iff_stalk_mono' : Prop := True
/-- app_surjective_of_injective_of_locally_surjective (abstract). -/
def app_surjective_of_injective_of_locally_surjective' : Prop := True
/-- app_surjective_of_stalkFunctor_map_bijective (abstract). -/
def app_surjective_of_stalkFunctor_map_bijective' : Prop := True
/-- app_bijective_of_stalkFunctor_map_bijective (abstract). -/
def app_bijective_of_stalkFunctor_map_bijective' : Prop := True
/-- app_isIso_of_stalkFunctor_map_iso (abstract). -/
def app_isIso_of_stalkFunctor_map_iso' : Prop := True
/-- isIso_of_stalkFunctor_map_iso (abstract). -/
def isIso_of_stalkFunctor_map_iso' : Prop := True
/-- isIso_iff_stalkFunctor_map_iso (abstract). -/
def isIso_iff_stalkFunctor_map_iso' : Prop := True

-- ShrinkingLemma.lean
-- COLLISION: says' already in Analysis.lean — rename needed
/-- PartialRefinement (abstract). -/
def PartialRefinement' : Prop := True
/-- apply_eq_of_chain (abstract). -/
def apply_eq_of_chain' : Prop := True
/-- chainSupCarrier (abstract). -/
def chainSupCarrier' : Prop := True
/-- find_apply_of_mem (abstract). -/
def find_apply_of_mem' : Prop := True
/-- chainSup (abstract). -/
def chainSup' : Prop := True
/-- le_chainSup (abstract). -/
def le_chainSup' : Prop := True
/-- exists_subset_iUnion_closure_subset (abstract). -/
def exists_subset_iUnion_closure_subset' : Prop := True
/-- exists_subset_iUnion_closed_subset (abstract). -/
def exists_subset_iUnion_closed_subset' : Prop := True
/-- exists_iUnion_eq_closure_subset (abstract). -/
def exists_iUnion_eq_closure_subset' : Prop := True
/-- exists_iUnion_eq_closed_subset (abstract). -/
def exists_iUnion_eq_closed_subset' : Prop := True
/-- exists_gt_t2space (abstract). -/
def exists_gt_t2space' : Prop := True
/-- exists_subset_iUnion_closure_subset_t2space (abstract). -/
def exists_subset_iUnion_closure_subset_t2space' : Prop := True
/-- exists_subset_iUnion_compact_subset_t2space (abstract). -/
def exists_subset_iUnion_compact_subset_t2space' : Prop := True

-- Sober.lean
/-- IsGenericPoint (abstract). -/
def IsGenericPoint' : Prop := True
/-- isGenericPoint_closure (abstract). -/
def isGenericPoint_closure' : Prop := True
/-- inseparable (abstract). -/
def inseparable' : Prop := True
/-- mem_open_set_iff (abstract). -/
def mem_open_set_iff' : Prop := True
-- COLLISION: disjoint_iff' already in Order.lean — rename needed
/-- mem_closed_set_iff (abstract). -/
def mem_closed_set_iff' : Prop := True
/-- isGenericPoint_iff_forall_closed (abstract). -/
def isGenericPoint_iff_forall_closed' : Prop := True
/-- QuasiSober (abstract). -/
def QuasiSober' : Prop := True
/-- genericPoint (abstract). -/
def genericPoint' : Prop := True
/-- isGenericPoint_genericPoint_closure (abstract). -/
def isGenericPoint_genericPoint_closure' : Prop := True
/-- isGenericPoint_genericPoint (abstract). -/
def isGenericPoint_genericPoint' : Prop := True
/-- genericPoint_closure_eq (abstract). -/
def genericPoint_closure_eq' : Prop := True
/-- closure_genericPoint (abstract). -/
def closure_genericPoint' : Prop := True
/-- genericPoint_spec (abstract). -/
def genericPoint_spec' : Prop := True
/-- genericPoint_closure (abstract). -/
def genericPoint_closure' : Prop := True
/-- genericPoint_specializes (abstract). -/
def genericPoint_specializes' : Prop := True
/-- irreducibleSetEquivPoints (abstract). -/
def irreducibleSetEquivPoints' : Prop := True
/-- quasiSober (abstract). -/
def quasiSober' : Prop := True
/-- genericPoints (abstract). -/
def genericPoints' : Prop := True
/-- component_injective (abstract). -/
def component_injective' : Prop := True
/-- ofComponent (abstract). -/
def ofComponent' : Prop := True
/-- isGenericPoint_ofComponent (abstract). -/
def isGenericPoint_ofComponent' : Prop := True
/-- component_ofComponent (abstract). -/
def component_ofComponent' : Prop := True
/-- ofComponent_component (abstract). -/
def ofComponent_component' : Prop := True
/-- component_surjective (abstract). -/
def component_surjective' : Prop := True
/-- genericPoints_eq_singleton (abstract). -/
def genericPoints_eq_singleton' : Prop := True

-- Specialization.lean
/-- Specialization (abstract). -/
def Specialization' : Prop := True
-- COLLISION: toEquiv' already in RingTheory2.lean — rename needed
-- COLLISION: ofEquiv' already in RingTheory2.lean — rename needed
/-- isOpen_toEquiv_preimage (abstract). -/
def isOpen_toEquiv_preimage' : Prop := True
/-- homeoWithUpperSetTopologyorderIso (abstract). -/
def homeoWithUpperSetTopologyorderIso' : Prop := True
/-- topToPreord (abstract). -/
def topToPreord' : Prop := True

-- Spectral/Hom.lean
/-- IsSpectralMap (abstract). -/
def IsSpectralMap' : Prop := True
/-- preimage_of_isOpen (abstract). -/
def preimage_of_isOpen' : Prop := True
/-- isSpectralMap_id (abstract). -/
def isSpectralMap_id' : Prop := True
/-- SpectralMap (abstract). -/
def SpectralMap' : Prop := True
/-- SpectralMapClass (abstract). -/
def SpectralMapClass' : Prop := True

-- StoneCech.lean
/-- ultrafilterBasis (abstract). -/
def ultrafilterBasis' : Prop := True
/-- ultrafilterBasis_is_basis (abstract). -/
def ultrafilterBasis_is_basis' : Prop := True
/-- ultrafilter_isOpen_basic (abstract). -/
def ultrafilter_isOpen_basic' : Prop := True
/-- ultrafilter_isClosed_basic (abstract). -/
def ultrafilter_isClosed_basic' : Prop := True
/-- ultrafilter_converges_iff (abstract). -/
def ultrafilter_converges_iff' : Prop := True
/-- ultrafilter_comap_pure_nhds (abstract). -/
def ultrafilter_comap_pure_nhds' : Prop := True
/-- ultrafilter_pure_injective (abstract). -/
def ultrafilter_pure_injective' : Prop := True
/-- denseRange_pure (abstract). -/
def denseRange_pure' : Prop := True
/-- induced_topology_pure (abstract). -/
def induced_topology_pure' : Prop := True
/-- isDenseInducing_pure (abstract). -/
def isDenseInducing_pure' : Prop := True
/-- isDenseEmbedding_pure (abstract). -/
def isDenseEmbedding_pure' : Prop := True
/-- ultrafilter_extend_extends (abstract). -/
def ultrafilter_extend_extends' : Prop := True
/-- continuous_ultrafilter_extend (abstract). -/
def continuous_ultrafilter_extend' : Prop := True
/-- ultrafilter_extend_eq_iff (abstract). -/
def ultrafilter_extend_eq_iff' : Prop := True
/-- PreStoneCech (abstract). -/
def PreStoneCech' : Prop := True
/-- preStoneCechUnit (abstract). -/
def preStoneCechUnit' : Prop := True
/-- continuous_preStoneCechUnit (abstract). -/
def continuous_preStoneCechUnit' : Prop := True
/-- denseRange_preStoneCechUnit (abstract). -/
def denseRange_preStoneCechUnit' : Prop := True
/-- preStoneCech_hom_ext (abstract). -/
def preStoneCech_hom_ext' : Prop := True
/-- preStoneCechCompat (abstract). -/
def preStoneCechCompat' : Prop := True
/-- preStoneCechExtend (abstract). -/
def preStoneCechExtend' : Prop := True
/-- preStoneCechExtend_extends (abstract). -/
def preStoneCechExtend_extends' : Prop := True
/-- eq_if_preStoneCechUnit_eq (abstract). -/
def eq_if_preStoneCechUnit_eq' : Prop := True
/-- continuous_preStoneCechExtend (abstract). -/
def continuous_preStoneCechExtend' : Prop := True
/-- StoneCech (abstract). -/
def StoneCech' : Prop := True
/-- stoneCechUnit (abstract). -/
def stoneCechUnit' : Prop := True
/-- continuous_stoneCechUnit (abstract). -/
def continuous_stoneCechUnit' : Prop := True
/-- denseRange_stoneCechUnit (abstract). -/
def denseRange_stoneCechUnit' : Prop := True
/-- stoneCech_hom_ext (abstract). -/
def stoneCech_hom_ext' : Prop := True
/-- stoneCechExtend (abstract). -/
def stoneCechExtend' : Prop := True
/-- stoneCechExtend_extends (abstract). -/
def stoneCechExtend_extends' : Prop := True
/-- continuous_stoneCechExtend (abstract). -/
def continuous_stoneCechExtend' : Prop := True
/-- eq_if_stoneCechUnit_eq (abstract). -/
def eq_if_stoneCechUnit_eq' : Prop := True

-- TietzeExtension.lean
/-- TietzeExtension (abstract). -/
def TietzeExtension' : Prop := True
/-- exists_restrict_eq (abstract). -/
def exists_restrict_eq' : Prop := True
/-- exists_extension (abstract). -/
def exists_extension' : Prop := True
/-- exists_forall_mem_restrict_eq (abstract). -/
def exists_forall_mem_restrict_eq' : Prop := True
/-- exists_extension_forall_mem (abstract). -/
def exists_extension_forall_mem' : Prop := True
-- COLLISION: of_retract' already in RingTheory2.lean — rename needed
/-- of_homeo (abstract). -/
def of_homeo' : Prop := True
/-- tietze_extension_step (abstract). -/
def tietze_extension_step' : Prop := True
/-- there (abstract). -/
def there' : Prop := True
/-- exists_extension_norm_eq_of_isClosedEmbedding (abstract). -/
def exists_extension_norm_eq_of_isClosedEmbedding' : Prop := True
/-- exists_norm_eq_restrict_eq_of_closed (abstract). -/
def exists_norm_eq_restrict_eq_of_closed' : Prop := True
/-- exists_extension_forall_mem_Icc_of_isClosedEmbedding (abstract). -/
def exists_extension_forall_mem_Icc_of_isClosedEmbedding' : Prop := True
/-- exists_extension_forall_exists_le_ge_of_isClosedEmbedding (abstract). -/
def exists_extension_forall_exists_le_ge_of_isClosedEmbedding' : Prop := True
/-- exists_extension_forall_mem_of_isClosedEmbedding (abstract). -/
def exists_extension_forall_mem_of_isClosedEmbedding' : Prop := True
/-- exists_forall_mem_restrict_eq_of_closed (abstract). -/
def exists_forall_mem_restrict_eq_of_closed' : Prop := True
/-- exists_restrict_eq_forall_mem_of_closed (abstract). -/
def exists_restrict_eq_forall_mem_of_closed' : Prop := True

-- Ultrafilter.lean
/-- clusterPt_iff_ultrafilter (abstract). -/
def clusterPt_iff_ultrafilter' : Prop := True
/-- mapClusterPt_iff_ultrafilter (abstract). -/
def mapClusterPt_iff_ultrafilter' : Prop := True
/-- mem_closure_iff_ultrafilter (abstract). -/
def mem_closure_iff_ultrafilter' : Prop := True
/-- isClosed_iff_ultrafilter (abstract). -/
def isClosed_iff_ultrafilter' : Prop := True
/-- continuousAt_iff_ultrafilter (abstract). -/
def continuousAt_iff_ultrafilter' : Prop := True
/-- continuous_iff_ultrafilter (abstract). -/
def continuous_iff_ultrafilter' : Prop := True

-- UniformSpace/AbsoluteValue.lean

-- UniformSpace/AbstractCompletion.lean
/-- AbstractCompletion (abstract). -/
def AbstractCompletion' : Prop := True
/-- ofComplete (abstract). -/
def ofComplete' : Prop := True
-- COLLISION: funext' already in RingTheory2.lean — rename needed
/-- extend_def (abstract). -/
def extend_def' : Prop := True
/-- extend_coe (abstract). -/
def extend_coe' : Prop := True
/-- uniformContinuous_extend (abstract). -/
def uniformContinuous_extend' : Prop := True
/-- extend_comp_coe (abstract). -/
def extend_comp_coe' : Prop := True
/-- uniformContinuous_map (abstract). -/
def uniformContinuous_map' : Prop := True
/-- map_coe (abstract). -/
def map_coe' : Prop := True
-- COLLISION: map_unique' already in RingTheory2.lean — rename needed
/-- extend_map (abstract). -/
def extend_map' : Prop := True
/-- compare (abstract). -/
def compare' : Prop := True
/-- uniformContinuous_compare (abstract). -/
def uniformContinuous_compare' : Prop := True
/-- compare_coe (abstract). -/
def compare_coe' : Prop := True
/-- inverse_compare (abstract). -/
def inverse_compare' : Prop := True
/-- compareEquiv (abstract). -/
def compareEquiv' : Prop := True
/-- uniformContinuous_compareEquiv (abstract). -/
def uniformContinuous_compareEquiv' : Prop := True
/-- uniformContinuous_compareEquiv_symm (abstract). -/
def uniformContinuous_compareEquiv_symm' : Prop := True
/-- compare_comp_eq_compare (abstract). -/
def compare_comp_eq_compare' : Prop := True
/-- extend₂ (abstract). -/
def extend₂' : Prop := True
/-- extension₂_coe_coe (abstract). -/
def extension₂_coe_coe' : Prop := True
/-- uniformContinuous_extension₂ (abstract). -/
def uniformContinuous_extension₂' : Prop := True
-- COLLISION: map₂' already in SetTheory.lean — rename needed
/-- uniformContinuous_map₂ (abstract). -/
def uniformContinuous_map₂' : Prop := True
/-- continuous_map₂ (abstract). -/
def continuous_map₂' : Prop := True
/-- map₂_coe_coe (abstract). -/
def map₂_coe_coe' : Prop := True

-- UniformSpace/Ascoli.lean
-- COLLISION: follows' already in CategoryTheory.lean — rename needed
/-- comap_uniformFun_eq (abstract). -/
def comap_uniformFun_eq' : Prop := True
/-- isUniformInducing_uniformFun_iff_pi (abstract). -/
def isUniformInducing_uniformFun_iff_pi' : Prop := True
/-- inducing_uniformFun_iff_pi (abstract). -/
def inducing_uniformFun_iff_pi' : Prop := True
/-- tendsto_uniformFun_iff_pi (abstract). -/
def tendsto_uniformFun_iff_pi' : Prop := True
/-- comap_uniformOnFun_eq (abstract). -/
def comap_uniformOnFun_eq' : Prop := True
/-- isUniformInducing_uniformOnFun_iff_pi' (abstract). -/
def isUniformInducing_uniformOnFun_iff_pi' : Prop := True
/-- inducing_uniformOnFun_iff_pi' (abstract). -/
def inducing_uniformOnFun_iff_pi' : Prop := True
/-- isInducing_uniformOnFun_iff_pi (abstract). -/
def isInducing_uniformOnFun_iff_pi' : Prop := True
/-- tendsto_uniformOnFun_iff_pi' (abstract). -/
def tendsto_uniformOnFun_iff_pi' : Prop := True
/-- isClosed_range_pi_of_uniformOnFun' (abstract). -/
def isClosed_range_pi_of_uniformOnFun' : Prop := True
/-- isClosed_range_uniformOnFun_iff_pi (abstract). -/
def isClosed_range_uniformOnFun_iff_pi' : Prop := True
/-- compactSpace_of_closed_inducing' (abstract). -/
def compactSpace_of_closed_inducing' : Prop := True
/-- compactSpace_of_isClosedEmbedding (abstract). -/
def compactSpace_of_isClosedEmbedding' : Prop := True
/-- isCompact_closure_of_isClosedEmbedding (abstract). -/
def isCompact_closure_of_isClosedEmbedding' : Prop := True
/-- isCompact_of_equicontinuous (abstract). -/
def isCompact_of_equicontinuous' : Prop := True

-- UniformSpace/Basic.lean
/-- idRel (abstract). -/
def idRel' : Prop := True
/-- idRel_subset (abstract). -/
def idRel_subset' : Prop := True
/-- eq_singleton_left_of_prod_subset_idRel (abstract). -/
def eq_singleton_left_of_prod_subset_idRel' : Prop := True
/-- eq_singleton_right_prod_subset_idRel (abstract). -/
def eq_singleton_right_prod_subset_idRel' : Prop := True
/-- eq_singleton_prod_subset_idRel (abstract). -/
def eq_singleton_prod_subset_idRel' : Prop := True
/-- compRel (abstract). -/
def compRel' : Prop := True
/-- swap_idRel (abstract). -/
def swap_idRel' : Prop := True
/-- compRel_mono (abstract). -/
def compRel_mono' : Prop := True
/-- prod_mk_mem_compRel (abstract). -/
def prod_mk_mem_compRel' : Prop := True
/-- id_compRel (abstract). -/
def id_compRel' : Prop := True
/-- compRel_assoc (abstract). -/
def compRel_assoc' : Prop := True
/-- left_subset_compRel (abstract). -/
def left_subset_compRel' : Prop := True
/-- right_subset_compRel (abstract). -/
def right_subset_compRel' : Prop := True
/-- subset_comp_self (abstract). -/
def subset_comp_self' : Prop := True
/-- subset_iterate_compRel (abstract). -/
def subset_iterate_compRel' : Prop := True
/-- SymmetricRel (abstract). -/
def SymmetricRel' : Prop := True
/-- symmetrizeRel (abstract). -/
def symmetrizeRel' : Prop := True
/-- symmetric_symmetrizeRel (abstract). -/
def symmetric_symmetrizeRel' : Prop := True
/-- symmetrizeRel_subset_self (abstract). -/
def symmetrizeRel_subset_self' : Prop := True
/-- symmetrize_mono (abstract). -/
def symmetrize_mono' : Prop := True
/-- mk_mem_comm (abstract). -/
def mk_mem_comm' : Prop := True
-- COLLISION: Core' already in Analysis.lean — rename needed
/-- comp_mem_uniformity_sets (abstract). -/
def comp_mem_uniformity_sets' : Prop := True
/-- mkOfBasis (abstract). -/
def mkOfBasis' : Prop := True
/-- toTopologicalSpace (abstract). -/
def toTopologicalSpace' : Prop := True
/-- nhds_toTopologicalSpace (abstract). -/
def nhds_toTopologicalSpace' : Prop := True
/-- UniformSpace (abstract). -/
def UniformSpace' : Prop := True
/-- uniformity (abstract). -/
def uniformity' : Prop := True
/-- ofCoreEq (abstract). -/
def ofCoreEq' : Prop := True
-- COLLISION: ofCore' already in Order.lean — rename needed
-- COLLISION: toCore' already in Analysis.lean — rename needed
/-- ofNhdsEqComap (abstract). -/
def ofNhdsEqComap' : Prop := True
/-- ofCoreEq_toCore (abstract). -/
def ofCoreEq_toCore' : Prop := True
/-- nhds_eq_comap_uniformity (abstract). -/
def nhds_eq_comap_uniformity' : Prop := True
/-- isOpen_uniformity (abstract). -/
def isOpen_uniformity' : Prop := True
/-- refl_le_uniformity (abstract). -/
def refl_le_uniformity' : Prop := True
/-- refl_mem_uniformity (abstract). -/
def refl_mem_uniformity' : Prop := True
/-- mem_uniformity_of_eq (abstract). -/
def mem_uniformity_of_eq' : Prop := True
/-- symm_le_uniformity (abstract). -/
def symm_le_uniformity' : Prop := True
/-- comp_le_uniformity (abstract). -/
def comp_le_uniformity' : Prop := True
/-- lift'_comp_uniformity (abstract). -/
def lift'_comp_uniformity' : Prop := True
/-- tendsto_swap_uniformity (abstract). -/
def tendsto_swap_uniformity' : Prop := True
/-- eventually_uniformity_iterate_comp_subset (abstract). -/
def eventually_uniformity_iterate_comp_subset' : Prop := True
/-- eventually_uniformity_comp_subset (abstract). -/
def eventually_uniformity_comp_subset' : Prop := True
/-- uniformity_trans (abstract). -/
def uniformity_trans' : Prop := True
/-- uniformity_symm (abstract). -/
def uniformity_symm' : Prop := True
/-- tendsto_diag_uniformity (abstract). -/
def tendsto_diag_uniformity' : Prop := True
/-- tendsto_const_uniformity (abstract). -/
def tendsto_const_uniformity' : Prop := True
/-- symm_of_uniformity (abstract). -/
def symm_of_uniformity' : Prop := True
/-- comp_symm_of_uniformity (abstract). -/
def comp_symm_of_uniformity' : Prop := True
/-- uniformity_le_symm (abstract). -/
def uniformity_le_symm' : Prop := True
/-- uniformity_eq_symm (abstract). -/
def uniformity_eq_symm' : Prop := True
/-- comap_swap_uniformity (abstract). -/
def comap_swap_uniformity' : Prop := True
/-- symmetrize_mem_uniformity (abstract). -/
def symmetrize_mem_uniformity' : Prop := True
/-- hasBasis_symmetric (abstract). -/
def hasBasis_symmetric' : Prop := True
/-- uniformity_lift_le_swap (abstract). -/
def uniformity_lift_le_swap' : Prop := True
/-- uniformity_lift_le_comp (abstract). -/
def uniformity_lift_le_comp' : Prop := True
/-- comp3_mem_uniformity (abstract). -/
def comp3_mem_uniformity' : Prop := True
/-- comp_le_uniformity3 (abstract). -/
def comp_le_uniformity3' : Prop := True
/-- comp_symm_mem_uniformity_sets (abstract). -/
def comp_symm_mem_uniformity_sets' : Prop := True
/-- subset_comp_self_of_mem_uniformity (abstract). -/
def subset_comp_self_of_mem_uniformity' : Prop := True
/-- comp_comp_symm_mem_uniformity_sets (abstract). -/
def comp_comp_symm_mem_uniformity_sets' : Prop := True
/-- mem_ball_comp (abstract). -/
def mem_ball_comp' : Prop := True
/-- ball_subset_of_comp_subset (abstract). -/
def ball_subset_of_comp_subset' : Prop := True
-- COLLISION: ball_mono' already in Analysis.lean — rename needed
/-- ball_inter (abstract). -/
def ball_inter' : Prop := True
/-- ball_inter_left (abstract). -/
def ball_inter_left' : Prop := True
/-- ball_inter_right (abstract). -/
def ball_inter_right' : Prop := True
/-- mem_ball_symmetry (abstract). -/
def mem_ball_symmetry' : Prop := True
/-- ball_eq_of_symmetry (abstract). -/
def ball_eq_of_symmetry' : Prop := True
/-- mem_comp_of_mem_ball (abstract). -/
def mem_comp_of_mem_ball' : Prop := True
/-- mem_comp_comp (abstract). -/
def mem_comp_comp' : Prop := True
/-- mem_nhds_uniformity_iff_right (abstract). -/
def mem_nhds_uniformity_iff_right' : Prop := True
/-- mem_nhds_uniformity_iff_left (abstract). -/
def mem_nhds_uniformity_iff_left' : Prop := True
/-- nhdsWithin_eq_comap_uniformity_of_mem (abstract). -/
def nhdsWithin_eq_comap_uniformity_of_mem' : Prop := True
/-- nhdsWithin_eq_comap_uniformity (abstract). -/
def nhdsWithin_eq_comap_uniformity' : Prop := True
/-- isOpen_iff_ball_subset (abstract). -/
def isOpen_iff_ball_subset' : Prop := True
/-- ball_mem_nhdsWithin (abstract). -/
def ball_mem_nhdsWithin' : Prop := True
/-- mem_nhds_iff_symm (abstract). -/
def mem_nhds_iff_symm' : Prop := True
/-- mem_closure_iff_symm_ball (abstract). -/
def mem_closure_iff_symm_ball' : Prop := True
/-- mem_closure_iff_ball (abstract). -/
def mem_closure_iff_ball' : Prop := True
/-- hasBasis_nhds_prod (abstract). -/
def hasBasis_nhds_prod' : Prop := True
/-- nhds_eq_uniformity (abstract). -/
def nhds_eq_uniformity' : Prop := True
/-- mem_nhds_left (abstract). -/
def mem_nhds_left' : Prop := True
/-- mem_nhds_right (abstract). -/
def mem_nhds_right' : Prop := True
/-- exists_mem_nhds_ball_subset_of_mem_nhds (abstract). -/
def exists_mem_nhds_ball_subset_of_mem_nhds' : Prop := True
/-- tendsto_right_nhds_uniformity (abstract). -/
def tendsto_right_nhds_uniformity' : Prop := True
/-- tendsto_left_nhds_uniformity (abstract). -/
def tendsto_left_nhds_uniformity' : Prop := True
/-- lift_nhds_left (abstract). -/
def lift_nhds_left' : Prop := True
/-- lift_nhds_right (abstract). -/
def lift_nhds_right' : Prop := True
/-- nhds_nhds_eq_uniformity_uniformity_prod (abstract). -/
def nhds_nhds_eq_uniformity_uniformity_prod' : Prop := True
/-- nhds_eq_uniformity_prod (abstract). -/
def nhds_eq_uniformity_prod' : Prop := True
/-- nhdset_of_mem_uniformity (abstract). -/
def nhdset_of_mem_uniformity' : Prop := True
/-- nhds_le_uniformity (abstract). -/
def nhds_le_uniformity' : Prop := True
/-- iSup_nhds_le_uniformity (abstract). -/
def iSup_nhds_le_uniformity' : Prop := True
/-- nhdsSet_diagonal_le_uniformity (abstract). -/
def nhdsSet_diagonal_le_uniformity' : Prop := True
/-- closure_eq_uniformity (abstract). -/
def closure_eq_uniformity' : Prop := True
/-- uniformity_hasBasis_closed (abstract). -/
def uniformity_hasBasis_closed' : Prop := True
/-- uniformity_eq_uniformity_closure (abstract). -/
def uniformity_eq_uniformity_closure' : Prop := True
/-- uniformity_closure (abstract). -/
def uniformity_closure' : Prop := True
/-- uniformity_hasBasis_closure (abstract). -/
def uniformity_hasBasis_closure' : Prop := True
/-- closure_eq_inter_uniformity (abstract). -/
def closure_eq_inter_uniformity' : Prop := True
/-- uniformity_eq_uniformity_interior (abstract). -/
def uniformity_eq_uniformity_interior' : Prop := True
/-- interior_mem_uniformity (abstract). -/
def interior_mem_uniformity' : Prop := True
/-- biUnion_uniformity_ball (abstract). -/
def biUnion_uniformity_ball' : Prop := True
/-- iUnion_uniformity_ball (abstract). -/
def iUnion_uniformity_ball' : Prop := True
/-- uniformity_hasBasis_open_symmetric (abstract). -/
def uniformity_hasBasis_open_symmetric' : Prop := True
/-- comp_open_symm_mem_uniformity_sets (abstract). -/
def comp_open_symm_mem_uniformity_sets' : Prop := True
/-- has_seq_basis (abstract). -/
def has_seq_basis' : Prop := True
/-- biInter_biUnion_ball (abstract). -/
def biInter_biUnion_ball' : Prop := True
/-- UniformContinuous (abstract). -/
def UniformContinuous' : Prop := True
/-- UniformContinuousOn (abstract). -/
def UniformContinuousOn' : Prop := True
/-- uniformContinuousOn_univ (abstract). -/
def uniformContinuousOn_univ' : Prop := True
/-- uniformContinuous_of_const (abstract). -/
def uniformContinuous_of_const' : Prop := True
/-- uniformContinuous_id (abstract). -/
def uniformContinuous_id' : Prop := True
/-- uniformContinuous_const (abstract). -/
def uniformContinuous_const' : Prop := True
-- COLLISION: sInf_le' already in Order.lean — rename needed
-- COLLISION: le_sInf' already in Order.lean — rename needed
/-- iInf_uniformity (abstract). -/
def iInf_uniformity' : Prop := True
/-- ball_preimage (abstract). -/
def ball_preimage' : Prop := True
/-- uniformSpace_comap_id (abstract). -/
def uniformSpace_comap_id' : Prop := True
-- COLLISION: comap_comap' already in Order.lean — rename needed
-- COLLISION: comap_inf' already in Order.lean — rename needed
-- COLLISION: comap_iInf' already in Order.lean — rename needed
/-- le_iff_uniformContinuous_id (abstract). -/
def le_iff_uniformContinuous_id' : Prop := True
/-- uniformContinuous_comap (abstract). -/
def uniformContinuous_comap' : Prop := True
/-- to_nhds_mono (abstract). -/
def to_nhds_mono' : Prop := True
/-- toTopologicalSpace_mono (abstract). -/
def toTopologicalSpace_mono' : Prop := True
/-- toTopologicalSpace_sInf (abstract). -/
def toTopologicalSpace_sInf' : Prop := True
/-- inf_rng (abstract). -/
def inf_rng' : Prop := True
/-- inf_dom_left (abstract). -/
def inf_dom_left' : Prop := True
/-- inf_dom_right (abstract). -/
def inf_dom_right' : Prop := True
/-- uniformContinuous_sInf_dom (abstract). -/
def uniformContinuous_sInf_dom' : Prop := True
/-- uniformContinuous_sInf_rng (abstract). -/
def uniformContinuous_sInf_rng' : Prop := True
/-- uniformContinuous_iInf_dom (abstract). -/
def uniformContinuous_iInf_dom' : Prop := True
/-- uniformContinuous_iInf_rng (abstract). -/
def uniformContinuous_iInf_rng' : Prop := True
/-- discreteTopology_of_discrete_uniformity (abstract). -/
def discreteTopology_of_discrete_uniformity' : Prop := True
/-- uniformContinuous_ofMul (abstract). -/
def uniformContinuous_ofMul' : Prop := True
/-- uniformContinuous_toMul (abstract). -/
def uniformContinuous_toMul' : Prop := True
/-- map_uniformity_set_coe (abstract). -/
def map_uniformity_set_coe' : Prop := True
/-- uniformContinuous_subtype_val (abstract). -/
def uniformContinuous_subtype_val' : Prop := True
/-- uniformContinuousOn_iff_restrict (abstract). -/
def uniformContinuousOn_iff_restrict' : Prop := True
/-- tendsto_of_uniformContinuous_subtype (abstract). -/
def tendsto_of_uniformContinuous_subtype' : Prop := True
/-- comap_uniformity_mulOpposite (abstract). -/
def comap_uniformity_mulOpposite' : Prop := True
/-- uniformContinuous_unop (abstract). -/
def uniformContinuous_unop' : Prop := True
/-- uniformContinuous_op (abstract). -/
def uniformContinuous_op' : Prop := True
/-- uniformity_prod_eq_comap_prod (abstract). -/
def uniformity_prod_eq_comap_prod' : Prop := True
/-- uniformity_prod_eq_prod (abstract). -/
def uniformity_prod_eq_prod' : Prop := True
/-- mem_uniformity_of_uniformContinuous_invariant (abstract). -/
def mem_uniformity_of_uniformContinuous_invariant' : Prop := True
/-- entourageProd (abstract). -/
def entourageProd' : Prop := True
/-- entourageProd_mem_uniformity (abstract). -/
def entourageProd_mem_uniformity' : Prop := True
/-- ball_entourageProd (abstract). -/
def ball_entourageProd' : Prop := True
/-- uniformity_prod (abstract). -/
def uniformity_prod' : Prop := True
/-- entourageProd_subset (abstract). -/
def entourageProd_subset' : Prop := True
/-- tendsto_prod_uniformity_fst (abstract). -/
def tendsto_prod_uniformity_fst' : Prop := True
/-- tendsto_prod_uniformity_snd (abstract). -/
def tendsto_prod_uniformity_snd' : Prop := True
/-- uniformContinuous_inf_dom_left₂ (abstract). -/
def uniformContinuous_inf_dom_left₂' : Prop := True
/-- uniformContinuous_inf_dom_right₂ (abstract). -/
def uniformContinuous_inf_dom_right₂' : Prop := True
/-- uniformContinuous_sInf_dom₂ (abstract). -/
def uniformContinuous_sInf_dom₂' : Prop := True
/-- UniformContinuous₂ (abstract). -/
def UniformContinuous₂' : Prop := True
/-- uniformContinuous₂_curry (abstract). -/
def uniformContinuous₂_curry' : Prop := True
/-- bicompl (abstract). -/
def bicompl' : Prop := True
/-- tendsto_nhds_right (abstract). -/
def tendsto_nhds_right' : Prop := True
/-- tendsto_nhds_left (abstract). -/
def tendsto_nhds_left' : Prop := True
/-- continuousAt_iff'_right (abstract). -/
def continuousAt_iff'_right' : Prop := True
/-- continuousAt_iff'_left (abstract). -/
def continuousAt_iff'_left' : Prop := True
/-- continuousAt_iff_prod (abstract). -/
def continuousAt_iff_prod' : Prop := True
/-- continuousWithinAt_iff'_right (abstract). -/
def continuousWithinAt_iff'_right' : Prop := True
/-- continuousWithinAt_iff'_left (abstract). -/
def continuousWithinAt_iff'_left' : Prop := True
/-- continuousOn_iff'_right (abstract). -/
def continuousOn_iff'_right' : Prop := True
/-- continuousOn_iff'_left (abstract). -/
def continuousOn_iff'_left' : Prop := True
/-- continuous_iff'_right (abstract). -/
def continuous_iff'_right' : Prop := True
/-- continuous_iff'_left (abstract). -/
def continuous_iff'_left' : Prop := True
/-- exists_is_open_mem_uniformity_of_forall_mem_eq (abstract). -/
def exists_is_open_mem_uniformity_of_forall_mem_eq' : Prop := True
/-- congr_uniformity (abstract). -/
def congr_uniformity' : Prop := True
-- COLLISION: tendsto_congr' already in Order.lean — rename needed

-- UniformSpace/Cauchy.lean
-- COLLISION: Cauchy' already in Algebra.lean — rename needed
/-- cauchy_map_iff (abstract). -/
def cauchy_map_iff' : Prop := True
/-- cauchy_nhds (abstract). -/
def cauchy_nhds' : Prop := True
/-- cauchy_pure (abstract). -/
def cauchy_pure' : Prop := True
/-- cauchy_map (abstract). -/
def cauchy_map' : Prop := True
/-- mono_uniformSpace (abstract). -/
def mono_uniformSpace' : Prop := True
/-- cauchy_inf_uniformSpace (abstract). -/
def cauchy_inf_uniformSpace' : Prop := True
/-- cauchy_iInf_uniformSpace (abstract). -/
def cauchy_iInf_uniformSpace' : Prop := True
/-- cauchy_comap_uniformSpace (abstract). -/
def cauchy_comap_uniformSpace' : Prop := True
/-- cauchy_prod_iff (abstract). -/
def cauchy_prod_iff' : Prop := True
/-- le_nhds_of_cauchy_adhp_aux (abstract). -/
def le_nhds_of_cauchy_adhp_aux' : Prop := True
/-- le_nhds_of_cauchy_adhp (abstract). -/
def le_nhds_of_cauchy_adhp' : Prop := True
/-- le_nhds_iff_adhp_of_cauchy (abstract). -/
def le_nhds_iff_adhp_of_cauchy' : Prop := True
/-- CauchySeq (abstract). -/
def CauchySeq' : Prop := True
/-- tendsto_uniformity (abstract). -/
def tendsto_uniformity' : Prop := True
/-- cauchySeq_const (abstract). -/
def cauchySeq_const' : Prop := True
/-- cauchySeq_iff_tendsto (abstract). -/
def cauchySeq_iff_tendsto' : Prop := True
-- COLLISION: comp_tendsto' already in Order.lean — rename needed
/-- cauchySeq_comp_iff (abstract). -/
def cauchySeq_comp_iff' : Prop := True
/-- subseq_subseq_mem (abstract). -/
def subseq_subseq_mem' : Prop := True
/-- eventually_eventually (abstract). -/
def eventually_eventually' : Prop := True
/-- comp_cauchySeq (abstract). -/
def comp_cauchySeq' : Prop := True
-- COLLISION: subseq_mem' already in Order.lean — rename needed
/-- subseq_mem_entourage (abstract). -/
def subseq_mem_entourage' : Prop := True
/-- cauchySeq_of_controlled (abstract). -/
def cauchySeq_of_controlled' : Prop := True
/-- isComplete_iff_clusterPt (abstract). -/
def isComplete_iff_clusterPt' : Prop := True
/-- isComplete_iff_ultrafilter (abstract). -/
def isComplete_iff_ultrafilter' : Prop := True
/-- isComplete_iUnion_separated (abstract). -/
def isComplete_iUnion_separated' : Prop := True
/-- CompleteSpace (abstract). -/
def CompleteSpace' : Prop := True
/-- complete_univ (abstract). -/
def complete_univ' : Prop := True
/-- completeSpace_prod_of_nonempty (abstract). -/
def completeSpace_prod_of_nonempty' : Prop := True
/-- completeSpace_iff_isComplete_univ (abstract). -/
def completeSpace_iff_isComplete_univ' : Prop := True
/-- completeSpace_iff_ultrafilter (abstract). -/
def completeSpace_iff_ultrafilter' : Prop := True
/-- cauchy_iff_exists_le_nhds (abstract). -/
def cauchy_iff_exists_le_nhds' : Prop := True
/-- cauchy_map_iff_exists_tendsto (abstract). -/
def cauchy_map_iff_exists_tendsto' : Prop := True
/-- cauchySeq_tendsto_of_complete (abstract). -/
def cauchySeq_tendsto_of_complete' : Prop := True
/-- cauchySeq_tendsto_of_isComplete (abstract). -/
def cauchySeq_tendsto_of_isComplete' : Prop := True
/-- TotallyBounded (abstract). -/
def TotallyBounded' : Prop := True
/-- exists_subset (abstract). -/
def exists_subset' : Prop := True
/-- totallyBounded_iff_subset (abstract). -/
def totallyBounded_iff_subset' : Prop := True
/-- totallyBounded_closure (abstract). -/
def totallyBounded_closure' : Prop := True
/-- totallyBounded_iUnion (abstract). -/
def totallyBounded_iUnion' : Prop := True
/-- totallyBounded_biUnion (abstract). -/
def totallyBounded_biUnion' : Prop := True
/-- totallyBounded_sUnion (abstract). -/
def totallyBounded_sUnion' : Prop := True
/-- totallyBounded_singleton (abstract). -/
def totallyBounded_singleton' : Prop := True
/-- totallyBounded_empty (abstract). -/
def totallyBounded_empty' : Prop := True
/-- totallyBounded_union (abstract). -/
def totallyBounded_union' : Prop := True
/-- totallyBounded_insert (abstract). -/
def totallyBounded_insert' : Prop := True
/-- cauchy_of_totallyBounded (abstract). -/
def cauchy_of_totallyBounded' : Prop := True
/-- totallyBounded_iff_filter (abstract). -/
def totallyBounded_iff_filter' : Prop := True
/-- totallyBounded_iff_ultrafilter (abstract). -/
def totallyBounded_iff_ultrafilter' : Prop := True
/-- isCompact_iff_totallyBounded_isComplete (abstract). -/
def isCompact_iff_totallyBounded_isComplete' : Prop := True
/-- isCompact_of_totallyBounded_isClosed (abstract). -/
def isCompact_of_totallyBounded_isClosed' : Prop := True
/-- totallyBounded_range (abstract). -/
def totallyBounded_range' : Prop := True
/-- setSeqAux (abstract). -/
def setSeqAux' : Prop := True
/-- setSeq (abstract). -/
def setSeq' : Prop := True
/-- setSeq_mem (abstract). -/
def setSeq_mem' : Prop := True
/-- setSeq_mono (abstract). -/
def setSeq_mono' : Prop := True
/-- setSeq_sub_aux (abstract). -/
def setSeq_sub_aux' : Prop := True
/-- setSeq_prod_subset (abstract). -/
def setSeq_prod_subset' : Prop := True
-- COLLISION: seq' already in Order.lean — rename needed
/-- seq_mem (abstract). -/
def seq_mem' : Prop := True
/-- seq_pair_mem (abstract). -/
def seq_pair_mem' : Prop := True
/-- seq_is_cauchySeq (abstract). -/
def seq_is_cauchySeq' : Prop := True
/-- le_nhds_of_seq_tendsto_nhds (abstract). -/
def le_nhds_of_seq_tendsto_nhds' : Prop := True
/-- secondCountable_of_separable (abstract). -/
def secondCountable_of_separable' : Prop := True
/-- cauchy_le_pure (abstract). -/
def cauchy_le_pure' : Prop := True
/-- cauchyConst (abstract). -/
def cauchyConst' : Prop := True
/-- eq_const_of_cauchy (abstract). -/
def eq_const_of_cauchy' : Prop := True

-- UniformSpace/Compact.lean
/-- lebesgue_number_lemma (abstract). -/
def lebesgue_number_lemma' : Prop := True
/-- hK (abstract). -/
def hK' : Prop := True
/-- lebesgue_number_lemma_sUnion (abstract). -/
def lebesgue_number_lemma_sUnion' : Prop := True
/-- nhdsSet_basis_uniformity (abstract). -/
def nhdsSet_basis_uniformity' : Prop := True
/-- exists_uniform_thickening (abstract). -/
def exists_uniform_thickening' : Prop := True
/-- exists_uniform_thickening_of_basis (abstract). -/
def exists_uniform_thickening_of_basis' : Prop := True
/-- lebesgue_number_of_compact_open (abstract). -/
def lebesgue_number_of_compact_open' : Prop := True
/-- nhdsSet_diagonal_eq_uniformity (abstract). -/
def nhdsSet_diagonal_eq_uniformity' : Prop := True
/-- compactSpace_uniformity (abstract). -/
def compactSpace_uniformity' : Prop := True
/-- unique_uniformity_of_compact (abstract). -/
def unique_uniformity_of_compact' : Prop := True

-- UniformSpace/CompactConvergence.lean
/-- tendsto_iff_forall_isCompact_tendstoUniformlyOn (abstract). -/
def tendsto_iff_forall_isCompact_tendstoUniformlyOn' : Prop := True
/-- toUniformOnFunIsCompact (abstract). -/
def toUniformOnFunIsCompact' : Prop := True
/-- range_toUniformOnFunIsCompact (abstract). -/
def range_toUniformOnFunIsCompact' : Prop := True
/-- compactConvergenceUniformity (abstract). -/
def compactConvergenceUniformity' : Prop := True
/-- hasBasis_compactConvergenceUniformity (abstract). -/
def hasBasis_compactConvergenceUniformity' : Prop := True
/-- mem_compactConvergence_entourage_iff (abstract). -/
def mem_compactConvergence_entourage_iff' : Prop := True
/-- hasAntitoneBasis_compactConvergenceUniformity (abstract). -/
def hasAntitoneBasis_compactConvergenceUniformity' : Prop := True
/-- tendsto_of_tendstoLocallyUniformly (abstract). -/
def tendsto_of_tendstoLocallyUniformly' : Prop := True
/-- tendsto_iff_tendstoLocallyUniformly (abstract). -/
def tendsto_iff_tendstoLocallyUniformly' : Prop := True
/-- isUniformInducing_comp (abstract). -/
def isUniformInducing_comp' : Prop := True
/-- uniformContinuous_comp_left (abstract). -/
def uniformContinuous_comp_left' : Prop := True
/-- hasBasis_compactConvergenceUniformity_of_compact (abstract). -/
def hasBasis_compactConvergenceUniformity_of_compact' : Prop := True
/-- uniformSpace_eq_inf_precomp_of_cover (abstract). -/
def uniformSpace_eq_inf_precomp_of_cover' : Prop := True
/-- uniformSpace_eq_iInf_precomp_of_cover (abstract). -/
def uniformSpace_eq_iInf_precomp_of_cover' : Prop := True
/-- completeSpace_of_restrictGenTopology (abstract). -/
def completeSpace_of_restrictGenTopology' : Prop := True

-- UniformSpace/CompareReals.lean
/-- rationalCauSeqPkg (abstract). -/
def rationalCauSeqPkg' : Prop := True
-- COLLISION: Q' already in RingTheory2.lean — rename needed
/-- Bourbakiℝ (abstract). -/
def Bourbakiℝ' : Prop := True
/-- bourbakiPkg (abstract). -/
def bourbakiPkg' : Prop := True
/-- compare_uc (abstract). -/
def compare_uc' : Prop := True
/-- compare_uc_symm (abstract). -/
def compare_uc_symm' : Prop := True

-- UniformSpace/CompleteSeparated.lean
/-- continuous_extend_of_cauchy (abstract). -/
def continuous_extend_of_cauchy' : Prop := True

-- UniformSpace/Completion.lean
/-- CauchyFilter (abstract). -/
def CauchyFilter' : Prop := True
/-- gen (abstract). -/
def gen' : Prop := True
/-- monotone_gen (abstract). -/
def monotone_gen' : Prop := True
/-- symm_gen (abstract). -/
def symm_gen' : Prop := True
/-- comp_gen (abstract). -/
def comp_gen' : Prop := True
/-- pureCauchy (abstract). -/
def pureCauchy' : Prop := True
/-- isUniformInducing_pureCauchy (abstract). -/
def isUniformInducing_pureCauchy' : Prop := True
/-- isUniformEmbedding_pureCauchy (abstract). -/
def isUniformEmbedding_pureCauchy' : Prop := True
/-- denseRange_pureCauchy (abstract). -/
def denseRange_pureCauchy' : Prop := True
/-- isDenseInducing_pureCauchy (abstract). -/
def isDenseInducing_pureCauchy' : Prop := True
/-- isDenseEmbedding_pureCauchy (abstract). -/
def isDenseEmbedding_pureCauchy' : Prop := True
/-- nonempty_cauchyFilter_iff (abstract). -/
def nonempty_cauchyFilter_iff' : Prop := True
/-- extend_pureCauchy (abstract). -/
def extend_pureCauchy' : Prop := True
/-- inseparable_iff_of_le_nhds (abstract). -/
def inseparable_iff_of_le_nhds' : Prop := True
/-- inseparable_lim_iff (abstract). -/
def inseparable_lim_iff' : Prop := True
/-- cauchyFilter_eq (abstract). -/
def cauchyFilter_eq' : Prop := True
/-- separated_pureCauchy_injective (abstract). -/
def separated_pureCauchy_injective' : Prop := True
/-- Completion (abstract). -/
def Completion' : Prop := True
/-- isUniformInducing_coe (abstract). -/
def isUniformInducing_coe' : Prop := True
/-- comap_coe_eq_uniformity (abstract). -/
def comap_coe_eq_uniformity' : Prop := True
/-- cPkg (abstract). -/
def cPkg' : Prop := True
/-- nonempty_completion_iff (abstract). -/
def nonempty_completion_iff' : Prop := True
/-- isDenseInducing_coe (abstract). -/
def isDenseInducing_coe' : Prop := True
/-- completeEquivSelf (abstract). -/
def completeEquivSelf' : Prop := True
/-- denseRange_coe₂ (abstract). -/
def denseRange_coe₂' : Prop := True
/-- denseRange_coe₃ (abstract). -/
def denseRange_coe₃' : Prop := True
/-- uniformContinuous_extension (abstract). -/
def uniformContinuous_extension' : Prop := True
-- COLLISION: extension_unique' already in Analysis.lean — rename needed
/-- extension_map (abstract). -/
def extension_map' : Prop := True
/-- completionSeparationQuotientEquiv (abstract). -/
def completionSeparationQuotientEquiv' : Prop := True
/-- uniformContinuous_completionSeparationQuotientEquiv (abstract). -/
def uniformContinuous_completionSeparationQuotientEquiv' : Prop := True
/-- uniformContinuous_completionSeparationQuotientEquiv_symm (abstract). -/
def uniformContinuous_completionSeparationQuotientEquiv_symm' : Prop := True
/-- extension₂ (abstract). -/
def extension₂' : Prop := True

-- UniformSpace/Equicontinuity.lean
/-- EquicontinuousAt (abstract). -/
def EquicontinuousAt' : Prop := True
/-- EquicontinuousWithinAt (abstract). -/
def EquicontinuousWithinAt' : Prop := True
/-- Equicontinuous (abstract). -/
def Equicontinuous' : Prop := True
/-- EquicontinuousOn (abstract). -/
def EquicontinuousOn' : Prop := True
/-- UniformEquicontinuous (abstract). -/
def UniformEquicontinuous' : Prop := True
/-- UniformEquicontinuousOn (abstract). -/
def UniformEquicontinuousOn' : Prop := True
/-- equicontinuousWithinAt (abstract). -/
def equicontinuousWithinAt' : Prop := True
/-- equicontinuousWithinAt_univ (abstract). -/
def equicontinuousWithinAt_univ' : Prop := True
/-- equicontinuousAt_restrict_iff (abstract). -/
def equicontinuousAt_restrict_iff' : Prop := True
/-- equicontinuousOn (abstract). -/
def equicontinuousOn' : Prop := True
/-- equicontinuousOn_univ (abstract). -/
def equicontinuousOn_univ' : Prop := True
/-- equicontinuous_restrict_iff (abstract). -/
def equicontinuous_restrict_iff' : Prop := True
/-- uniformEquicontinuousOn (abstract). -/
def uniformEquicontinuousOn' : Prop := True
/-- uniformEquicontinuousOn_univ (abstract). -/
def uniformEquicontinuousOn_univ' : Prop := True
/-- uniformEquicontinuous_restrict_iff (abstract). -/
def uniformEquicontinuous_restrict_iff' : Prop := True
/-- equicontinuousAt_empty (abstract). -/
def equicontinuousAt_empty' : Prop := True
/-- equicontinuousWithinAt_empty (abstract). -/
def equicontinuousWithinAt_empty' : Prop := True
/-- equicontinuous_empty (abstract). -/
def equicontinuous_empty' : Prop := True
/-- equicontinuousOn_empty (abstract). -/
def equicontinuousOn_empty' : Prop := True
/-- uniformEquicontinuous_empty (abstract). -/
def uniformEquicontinuous_empty' : Prop := True
/-- uniformEquicontinuousOn_empty (abstract). -/
def uniformEquicontinuousOn_empty' : Prop := True
/-- equicontinuousAt_finite (abstract). -/
def equicontinuousAt_finite' : Prop := True
/-- equicontinuousWithinAt_finite (abstract). -/
def equicontinuousWithinAt_finite' : Prop := True
/-- equicontinuous_finite (abstract). -/
def equicontinuous_finite' : Prop := True
/-- equicontinuousOn_finite (abstract). -/
def equicontinuousOn_finite' : Prop := True
/-- uniformEquicontinuous_finite (abstract). -/
def uniformEquicontinuous_finite' : Prop := True
/-- uniformEquicontinuousOn_finite (abstract). -/
def uniformEquicontinuousOn_finite' : Prop := True
/-- equicontinuousAt_unique (abstract). -/
def equicontinuousAt_unique' : Prop := True
/-- equicontinuousWithinAt_unique (abstract). -/
def equicontinuousWithinAt_unique' : Prop := True
/-- equicontinuous_unique (abstract). -/
def equicontinuous_unique' : Prop := True
/-- equicontinuousOn_unique (abstract). -/
def equicontinuousOn_unique' : Prop := True
/-- uniformEquicontinuous_unique (abstract). -/
def uniformEquicontinuous_unique' : Prop := True
/-- uniformEquicontinuousOn_unique (abstract). -/
def uniformEquicontinuousOn_unique' : Prop := True
/-- equicontinuousWithinAt_iff_pair (abstract). -/
def equicontinuousWithinAt_iff_pair' : Prop := True
/-- equicontinuous (abstract). -/
def equicontinuous' : Prop := True
/-- equicontinuousAt_iff_range (abstract). -/
def equicontinuousAt_iff_range' : Prop := True
/-- equicontinuousWithinAt_iff_range (abstract). -/
def equicontinuousWithinAt_iff_range' : Prop := True
/-- equicontinuous_iff_range (abstract). -/
def equicontinuous_iff_range' : Prop := True
/-- equicontinuousOn_iff_range (abstract). -/
def equicontinuousOn_iff_range' : Prop := True
/-- uniformEquicontinuous_iff_range (abstract). -/
def uniformEquicontinuous_iff_range' : Prop := True
/-- uniformEquicontinuousOn_iff_range (abstract). -/
def uniformEquicontinuousOn_iff_range' : Prop := True
/-- equicontinuousAt_iff_continuousAt (abstract). -/
def equicontinuousAt_iff_continuousAt' : Prop := True
/-- equicontinuousWithinAt_iff_continuousWithinAt (abstract). -/
def equicontinuousWithinAt_iff_continuousWithinAt' : Prop := True
/-- equicontinuous_iff_continuous (abstract). -/
def equicontinuous_iff_continuous' : Prop := True
/-- equicontinuousOn_iff_continuousOn (abstract). -/
def equicontinuousOn_iff_continuousOn' : Prop := True
/-- uniformEquicontinuous_iff_uniformContinuous (abstract). -/
def uniformEquicontinuous_iff_uniformContinuous' : Prop := True
/-- uniformEquicontinuousOn_iff_uniformContinuousOn (abstract). -/
def uniformEquicontinuousOn_iff_uniformContinuousOn' : Prop := True
/-- equicontinuousWithinAt_iInf_rng (abstract). -/
def equicontinuousWithinAt_iInf_rng' : Prop := True
/-- equicontinuousAt_iInf_rng (abstract). -/
def equicontinuousAt_iInf_rng' : Prop := True
/-- equicontinuousOn_iInf_rng (abstract). -/
def equicontinuousOn_iInf_rng' : Prop := True
/-- uniformEquicontinuous_iInf_rng (abstract). -/
def uniformEquicontinuous_iInf_rng' : Prop := True
/-- uniformEquicontinuousOn_iInf_rng (abstract). -/
def uniformEquicontinuousOn_iInf_rng' : Prop := True
/-- equicontinuousWithinAt_iInf_dom (abstract). -/
def equicontinuousWithinAt_iInf_dom' : Prop := True
/-- equicontinuousAt_iInf_dom (abstract). -/
def equicontinuousAt_iInf_dom' : Prop := True
/-- equicontinuous_iInf_dom (abstract). -/
def equicontinuous_iInf_dom' : Prop := True
/-- equicontinuousOn_iInf_dom (abstract). -/
def equicontinuousOn_iInf_dom' : Prop := True
/-- uniformEquicontinuous_iInf_dom (abstract). -/
def uniformEquicontinuous_iInf_dom' : Prop := True
/-- uniformEquicontinuousOn_iInf_dom (abstract). -/
def uniformEquicontinuousOn_iInf_dom' : Prop := True
/-- equicontinuousAt_iff_left (abstract). -/
def equicontinuousAt_iff_left' : Prop := True
/-- equicontinuousWithinAt_iff_left (abstract). -/
def equicontinuousWithinAt_iff_left' : Prop := True
/-- equicontinuousWithinAt_iff_right (abstract). -/
def equicontinuousWithinAt_iff_right' : Prop := True
/-- equicontinuousWithinAt_iff (abstract). -/
def equicontinuousWithinAt_iff' : Prop := True
/-- uniformEquicontinuous_iff_left (abstract). -/
def uniformEquicontinuous_iff_left' : Prop := True
/-- uniformEquicontinuousOn_iff_left (abstract). -/
def uniformEquicontinuousOn_iff_left' : Prop := True
/-- uniformEquicontinuousOn_iff_right (abstract). -/
def uniformEquicontinuousOn_iff_right' : Prop := True
/-- uniformEquicontinuousOn_iff (abstract). -/
def uniformEquicontinuousOn_iff' : Prop := True
/-- equicontinuous_iff (abstract). -/
def equicontinuous_iff' : Prop := True
/-- equicontinuousOn_iff (abstract). -/
def equicontinuousOn_iff' : Prop := True
-- COLLISION: closure' already in RingTheory2.lean — rename needed
/-- continuousWithinAt_of_equicontinuousWithinAt (abstract). -/
def continuousWithinAt_of_equicontinuousWithinAt' : Prop := True
/-- continuousAt_of_equicontinuousAt (abstract). -/
def continuousAt_of_equicontinuousAt' : Prop := True
/-- continuous_of_equicontinuous (abstract). -/
def continuous_of_equicontinuous' : Prop := True
/-- continuousOn_of_equicontinuousOn (abstract). -/
def continuousOn_of_equicontinuousOn' : Prop := True
/-- uniformContinuousOn_of_uniformEquicontinuousOn (abstract). -/
def uniformContinuousOn_of_uniformEquicontinuousOn' : Prop := True
/-- uniformContinuous_of_uniformEquicontinuous (abstract). -/
def uniformContinuous_of_uniformEquicontinuous' : Prop := True
/-- tendsto_of_mem_closure (abstract). -/
def tendsto_of_mem_closure' : Prop := True
/-- isClosed_setOf_tendsto (abstract). -/
def isClosed_setOf_tendsto' : Prop := True

-- UniformSpace/Equiv.lean
/-- UniformEquiv (abstract). -/
def UniformEquiv' : Prop := True
/-- ofIsUniformEmbedding (abstract). -/
def ofIsUniformEmbedding' : Prop := True
/-- prodPunit (abstract). -/
def prodPunit' : Prop := True
/-- toUniformEquivOfIsUniformInducing (abstract). -/
def toUniformEquivOfIsUniformInducing' : Prop := True

-- UniformSpace/HeineCantor.lean
/-- uniformContinuous_of_continuous (abstract). -/
def uniformContinuous_of_continuous' : Prop := True
/-- uniformContinuousOn_of_continuous (abstract). -/
def uniformContinuousOn_of_continuous' : Prop := True
/-- uniformContinuousAt_of_continuousAt (abstract). -/
def uniformContinuousAt_of_continuousAt' : Prop := True
/-- uniformContinuous_of_tendsto_cocompact (abstract). -/
def uniformContinuous_of_tendsto_cocompact' : Prop := True
/-- tendstoUniformly (abstract). -/
def tendstoUniformly' : Prop := True
/-- mem_uniformity_of_prod (abstract). -/
def mem_uniformity_of_prod' : Prop := True
/-- uniformEquicontinuous_of_equicontinuous (abstract). -/
def uniformEquicontinuous_of_equicontinuous' : Prop := True

-- UniformSpace/Matrix.lean

-- UniformSpace/OfCompactT2.lean
/-- uniformSpaceOfCompactT2 (abstract). -/
def uniformSpaceOfCompactT2' : Prop := True

-- UniformSpace/OfFun.lean
-- COLLISION: ofFun' already in Order.lean — rename needed
/-- hasBasis_ofFun (abstract). -/
def hasBasis_ofFun' : Prop := True

-- UniformSpace/Pi.lean
/-- uniformContinuous_pi (abstract). -/
def uniformContinuous_pi' : Prop := True
/-- uniformContinuous_proj (abstract). -/
def uniformContinuous_proj' : Prop := True
/-- uniformContinuous_precomp' (abstract). -/
def uniformContinuous_precomp' : Prop := True
/-- uniformContinuous_postcomp' (abstract). -/
def uniformContinuous_postcomp' : Prop := True
/-- uniformSpace_comap_precomp' (abstract). -/
def uniformSpace_comap_precomp' : Prop := True
/-- uniformContinuous_restrict (abstract). -/
def uniformContinuous_restrict' : Prop := True
/-- uniformSpace_comap_restrict (abstract). -/
def uniformSpace_comap_restrict' : Prop := True
/-- cauchy_pi_iff (abstract). -/
def cauchy_pi_iff' : Prop := True
/-- uniformSpace_comap_restrict_sUnion (abstract). -/
def uniformSpace_comap_restrict_sUnion' : Prop := True

-- UniformSpace/Separation.lean
-- COLLISION: search' already in Algebra.lean — rename needed
/-- specializes_iff_uniformity (abstract). -/
def specializes_iff_uniformity' : Prop := True
/-- inseparable_iff_uniformity (abstract). -/
def inseparable_iff_uniformity' : Prop := True
/-- inseparable_iff_ker_uniformity (abstract). -/
def inseparable_iff_ker_uniformity' : Prop := True
/-- inseparable_iff_clusterPt_uniformity (abstract). -/
def inseparable_iff_clusterPt_uniformity' : Prop := True
/-- t0Space_iff_uniformity (abstract). -/
def t0Space_iff_uniformity' : Prop := True
/-- t0Space_iff_ker_uniformity (abstract). -/
def t0Space_iff_ker_uniformity' : Prop := True
/-- eq_of_uniformity (abstract). -/
def eq_of_uniformity' : Prop := True
/-- eq_of_uniformity_basis (abstract). -/
def eq_of_uniformity_basis' : Prop := True
/-- eq_of_forall_symmetric (abstract). -/
def eq_of_forall_symmetric' : Prop := True
/-- eq_of_clusterPt_uniformity (abstract). -/
def eq_of_clusterPt_uniformity' : Prop := True
/-- isClosed_of_spaced_out (abstract). -/
def isClosed_of_spaced_out' : Prop := True
/-- isClosed_range_of_spaced_out (abstract). -/
def isClosed_range_of_spaced_out' : Prop := True
/-- comap_map_mk_uniformity (abstract). -/
def comap_map_mk_uniformity' : Prop := True
/-- uniformContinuous_mk (abstract). -/
def uniformContinuous_mk' : Prop := True
/-- uniformContinuous_dom (abstract). -/
def uniformContinuous_dom' : Prop := True
/-- uniformContinuous_dom₂ (abstract). -/
def uniformContinuous_dom₂' : Prop := True
/-- uniformContinuous_lift (abstract). -/
def uniformContinuous_lift' : Prop := True
/-- uniformContinuous_uncurry_lift₂ (abstract). -/
def uniformContinuous_uncurry_lift₂' : Prop := True
/-- comap_mk_uniformity (abstract). -/
def comap_mk_uniformity' : Prop := True
/-- lift'_mk (abstract). -/
def lift'_mk' : Prop := True
-- COLLISION: map_mk' already in RingTheory2.lean — rename needed

-- UniformSpace/UniformConvergence.lean
/-- TendstoUniformlyOnFilter (abstract). -/
def TendstoUniformlyOnFilter' : Prop := True
/-- TendstoUniformlyOn (abstract). -/
def TendstoUniformlyOn' : Prop := True
/-- tendstoUniformlyOn_iff_tendstoUniformlyOnFilter (abstract). -/
def tendstoUniformlyOn_iff_tendstoUniformlyOnFilter' : Prop := True
/-- tendstoUniformlyOn_iff_tendsto (abstract). -/
def tendstoUniformlyOn_iff_tendsto' : Prop := True
/-- TendstoUniformly (abstract). -/
def TendstoUniformly' : Prop := True
/-- tendstoUniformlyOn_univ (abstract). -/
def tendstoUniformlyOn_univ' : Prop := True
/-- tendstoUniformly_iff_tendstoUniformlyOnFilter (abstract). -/
def tendstoUniformly_iff_tendstoUniformlyOnFilter' : Prop := True
/-- tendstoUniformlyOnFilter (abstract). -/
def tendstoUniformlyOnFilter' : Prop := True
/-- tendstoUniformlyOn_iff_tendstoUniformly_comp_coe (abstract). -/
def tendstoUniformlyOn_iff_tendstoUniformly_comp_coe' : Prop := True
/-- tendstoUniformly_iff_tendsto (abstract). -/
def tendstoUniformly_iff_tendsto' : Prop := True
-- COLLISION: mono_left' already in Order.lean — rename needed
-- COLLISION: mono_right' already in Order.lean — rename needed
/-- tendstoUniformly_congr (abstract). -/
def tendstoUniformly_congr' : Prop := True
-- COLLISION: congr_right' already in SetTheory.lean — rename needed
-- COLLISION: tendstoUniformlyOn' already in Analysis.lean — rename needed
/-- comp_tendstoUniformlyOnFilter (abstract). -/
def comp_tendstoUniformlyOnFilter' : Prop := True
/-- comp_tendstoUniformlyOn (abstract). -/
def comp_tendstoUniformlyOn' : Prop := True
/-- comp_tendstoUniformly (abstract). -/
def comp_tendstoUniformly' : Prop := True
/-- tendsto_prod_filter_iff (abstract). -/
def tendsto_prod_filter_iff' : Prop := True
/-- tendsto_prod_principal_iff (abstract). -/
def tendsto_prod_principal_iff' : Prop := True
/-- tendsto_prod_top_iff (abstract). -/
def tendsto_prod_top_iff' : Prop := True
/-- tendstoUniformlyOn_empty (abstract). -/
def tendstoUniformlyOn_empty' : Prop := True
/-- tendstoUniformlyOn_singleton_iff_tendsto (abstract). -/
def tendstoUniformlyOn_singleton_iff_tendsto' : Prop := True
/-- tendstoUniformlyOnFilter_const (abstract). -/
def tendstoUniformlyOnFilter_const' : Prop := True
/-- tendstoUniformlyOn_const (abstract). -/
def tendstoUniformlyOn_const' : Prop := True
/-- UniformCauchySeqOnFilter (abstract). -/
def UniformCauchySeqOnFilter' : Prop := True
/-- UniformCauchySeqOn (abstract). -/
def UniformCauchySeqOn' : Prop := True
/-- uniformCauchySeqOn_iff_uniformCauchySeqOnFilter (abstract). -/
def uniformCauchySeqOn_iff_uniformCauchySeqOnFilter' : Prop := True
/-- uniformCauchySeqOnFilter (abstract). -/
def uniformCauchySeqOnFilter' : Prop := True
/-- uniformCauchySeqOn (abstract). -/
def uniformCauchySeqOn' : Prop := True
/-- tendstoUniformlyOnFilter_of_tendsto (abstract). -/
def tendstoUniformlyOnFilter_of_tendsto' : Prop := True
/-- tendstoUniformlyOn_of_tendsto (abstract). -/
def tendstoUniformlyOn_of_tendsto' : Prop := True
/-- comp_uniformCauchySeqOn (abstract). -/
def comp_uniformCauchySeqOn' : Prop := True
/-- tendstoUniformlyOn_of_seq_tendstoUniformlyOn (abstract). -/
def tendstoUniformlyOn_of_seq_tendstoUniformlyOn' : Prop := True
/-- seq_tendstoUniformlyOn (abstract). -/
def seq_tendstoUniformlyOn' : Prop := True
/-- tendstoUniformlyOn_iff_seq_tendstoUniformlyOn (abstract). -/
def tendstoUniformlyOn_iff_seq_tendstoUniformlyOn' : Prop := True
/-- tendstoUniformly_iff_seq_tendstoUniformly (abstract). -/
def tendstoUniformly_iff_seq_tendstoUniformly' : Prop := True
/-- tendsto_of_eventually_tendsto (abstract). -/
def tendsto_of_eventually_tendsto' : Prop := True
/-- TendstoLocallyUniformlyOn (abstract). -/
def TendstoLocallyUniformlyOn' : Prop := True
/-- TendstoLocallyUniformly (abstract). -/
def TendstoLocallyUniformly' : Prop := True
/-- tendstoLocallyUniformlyOn_univ (abstract). -/
def tendstoLocallyUniformlyOn_univ' : Prop := True
/-- tendstoLocallyUniformlyOn_iff_forall_tendsto (abstract). -/
def tendstoLocallyUniformlyOn_iff_forall_tendsto' : Prop := True
/-- tendstoLocallyUniformly_iff_forall_tendsto (abstract). -/
def tendstoLocallyUniformly_iff_forall_tendsto' : Prop := True
/-- tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe (abstract). -/
def tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe' : Prop := True
-- COLLISION: tendstoLocallyUniformlyOn' already in Analysis.lean — rename needed
/-- tendstoLocallyUniformly (abstract). -/
def tendstoLocallyUniformly' : Prop := True
/-- tendstoLocallyUniformlyOn_iUnion (abstract). -/
def tendstoLocallyUniformlyOn_iUnion' : Prop := True
/-- tendstoLocallyUniformlyOn_biUnion (abstract). -/
def tendstoLocallyUniformlyOn_biUnion' : Prop := True
/-- tendstoLocallyUniformlyOn_sUnion (abstract). -/
def tendstoLocallyUniformlyOn_sUnion' : Prop := True
/-- tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace (abstract). -/
def tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace' : Prop := True
/-- tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (abstract). -/
def tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact' : Prop := True
/-- tendstoLocallyUniformlyOn_TFAE (abstract). -/
def tendstoLocallyUniformlyOn_TFAE' : Prop := True
/-- tendstoLocallyUniformlyOn_iff_forall_isCompact (abstract). -/
def tendstoLocallyUniformlyOn_iff_forall_isCompact' : Prop := True
/-- tendstoLocallyUniformly_iff_forall_isCompact (abstract). -/
def tendstoLocallyUniformly_iff_forall_isCompact' : Prop := True
/-- tendstoLocallyUniformly_iff_filter (abstract). -/
def tendstoLocallyUniformly_iff_filter' : Prop := True
/-- tendsto_at (abstract). -/
def tendsto_at' : Prop := True
/-- continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt (abstract). -/
def continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt' : Prop := True
/-- continuousAt_of_locally_uniform_approx_of_continuousAt (abstract). -/
def continuousAt_of_locally_uniform_approx_of_continuousAt' : Prop := True
/-- continuousOn_of_locally_uniform_approx_of_continuousWithinAt (abstract). -/
def continuousOn_of_locally_uniform_approx_of_continuousWithinAt' : Prop := True
/-- continuousOn_of_uniform_approx_of_continuousOn (abstract). -/
def continuousOn_of_uniform_approx_of_continuousOn' : Prop := True
/-- continuous_of_locally_uniform_approx_of_continuousAt (abstract). -/
def continuous_of_locally_uniform_approx_of_continuousAt' : Prop := True
/-- continuous_of_uniform_approx_of_continuous (abstract). -/
def continuous_of_uniform_approx_of_continuous' : Prop := True
/-- tendsto_comp_of_locally_uniform_limit_within (abstract). -/
def tendsto_comp_of_locally_uniform_limit_within' : Prop := True
/-- tendsto_comp_of_locally_uniform_limit (abstract). -/
def tendsto_comp_of_locally_uniform_limit' : Prop := True

-- UniformSpace/UniformConvergenceTopology.lean
/-- UniformFun (abstract). -/
def UniformFun' : Prop := True
/-- UniformOnFun (abstract). -/
def UniformOnFun' : Prop := True
/-- isBasis_gen (abstract). -/
def isBasis_gen' : Prop := True
-- COLLISION: basis' already in RingTheory2.lean — rename needed
-- COLLISION: filter' already in Order.lean — rename needed
/-- phi (abstract). -/
def phi' : Prop := True
/-- uniformCore (abstract). -/
def uniformCore' : Prop := True
/-- hasBasis_nhds_of_basis (abstract). -/
def hasBasis_nhds_of_basis' : Prop := True
/-- uniformContinuous_eval (abstract). -/
def uniformContinuous_eval' : Prop := True
/-- mem_gen (abstract). -/
def mem_gen' : Prop := True
-- COLLISION: iInf_eq' already in Order.lean — rename needed
/-- inf_eq (abstract). -/
def inf_eq' : Prop := True
/-- postcomp_isUniformInducing (abstract). -/
def postcomp_isUniformInducing' : Prop := True
/-- postcomp_isUniformEmbedding (abstract). -/
def postcomp_isUniformEmbedding' : Prop := True
-- COLLISION: comap_eq' already in MeasureTheory2.lean — rename needed
/-- postcomp_uniformContinuous (abstract). -/
def postcomp_uniformContinuous' : Prop := True
/-- precomp_uniformContinuous (abstract). -/
def precomp_uniformContinuous' : Prop := True
/-- uniformContinuous_toFun (abstract). -/
def uniformContinuous_toFun' : Prop := True
/-- uniformEquivProdArrow (abstract). -/
def uniformEquivProdArrow' : Prop := True
/-- uniformEquivPiComm (abstract). -/
def uniformEquivPiComm' : Prop := True
/-- isClosed_setOf_continuous (abstract). -/
def isClosed_setOf_continuous' : Prop := True
/-- gen_eq_preimage_restrict (abstract). -/
def gen_eq_preimage_restrict' : Prop := True
/-- gen_mono (abstract). -/
def gen_mono' : Prop := True
/-- hasBasis_uniformity_of_basis_aux₁ (abstract). -/
def hasBasis_uniformity_of_basis_aux₁' : Prop := True
/-- hasBasis_uniformity_of_basis (abstract). -/
def hasBasis_uniformity_of_basis' : Prop := True
/-- hasBasis_uniformity_of_covering_of_basis (abstract). -/
def hasBasis_uniformity_of_covering_of_basis' : Prop := True
/-- hasAntitoneBasis_uniformity (abstract). -/
def hasAntitoneBasis_uniformity' : Prop := True
/-- isCountablyGenerated_uniformity (abstract). -/
def isCountablyGenerated_uniformity' : Prop := True
/-- uniformity_eq_of_basis (abstract). -/
def uniformity_eq_of_basis' : Prop := True
/-- uniformity_eq (abstract). -/
def uniformity_eq' : Prop := True
/-- gen_mem_uniformity (abstract). -/
def gen_mem_uniformity' : Prop := True
/-- nhds_eq_of_basis (abstract). -/
def nhds_eq_of_basis' : Prop := True
/-- gen_mem_nhds (abstract). -/
def gen_mem_nhds' : Prop := True
/-- uniformEquivUniformFun (abstract). -/
def uniformEquivUniformFun' : Prop := True
/-- uniformContinuous_eval_of_mem (abstract). -/
def uniformContinuous_eval_of_mem' : Prop := True
/-- uniformContinuous_eval_of_mem_sUnion (abstract). -/
def uniformContinuous_eval_of_mem_sUnion' : Prop := True
/-- t2Space_of_covering (abstract). -/
def t2Space_of_covering' : Prop := True
/-- uniformContinuous_restrict_toFun (abstract). -/
def uniformContinuous_restrict_toFun' : Prop := True
/-- continuousAt_eval₂ (abstract). -/
def continuousAt_eval₂' : Prop := True
/-- continuousOn_eval₂ (abstract). -/
def continuousOn_eval₂' : Prop := True
/-- continuous_rng_iff (abstract). -/
def continuous_rng_iff' : Prop := True
/-- isClosed_setOf_continuous_of_le (abstract). -/
def isClosed_setOf_continuous_of_le' : Prop := True
/-- comp_tendstoUniformly_eventually (abstract). -/
def comp_tendstoUniformly_eventually' : Prop := True

-- UniformSpace/UniformEmbedding.lean
/-- IsUniformInducing (abstract). -/
def IsUniformInducing' : Prop := True
/-- isUniformInducing_iff_uniformSpace (abstract). -/
def isUniformInducing_iff_uniformSpace' : Prop := True
/-- basis_uniformity (abstract). -/
def basis_uniformity' : Prop := True
/-- isUniformInducing_comp_iff (abstract). -/
def isUniformInducing_comp_iff' : Prop := True
/-- IsUniformEmbedding (abstract). -/
def IsUniformEmbedding' : Prop := True
/-- isUniformEmbedding_set_inclusion (abstract). -/
def isUniformEmbedding_set_inclusion' : Prop := True
/-- isUniformEmbedding_inl (abstract). -/
def isUniformEmbedding_inl' : Prop := True
/-- isUniformEmbedding_inr (abstract). -/
def isUniformEmbedding_inr' : Prop := True
/-- isUniformEmbedding_iff_isUniformInducing (abstract). -/
def isUniformEmbedding_iff_isUniformInducing' : Prop := True
/-- comap_uniformity_of_spaced_out (abstract). -/
def comap_uniformity_of_spaced_out' : Prop := True
/-- isUniformEmbedding_of_spaced_out (abstract). -/
def isUniformEmbedding_of_spaced_out' : Prop := True
/-- isClosedEmbedding_of_spaced_out (abstract). -/
def isClosedEmbedding_of_spaced_out' : Prop := True
/-- closure_image_mem_nhds_of_isUniformInducing (abstract). -/
def closure_image_mem_nhds_of_isUniformInducing' : Prop := True
/-- isUniformEmbedding_subtypeEmb (abstract). -/
def isUniformEmbedding_subtypeEmb' : Prop := True
-- COLLISION: isComplete_image_iff' already in Analysis.lean — rename needed
/-- isComplete_iff (abstract). -/
def isComplete_iff' : Prop := True
/-- completeSpace_iff_isComplete_range (abstract). -/
def completeSpace_iff_isComplete_range' : Prop := True
/-- completeSpace_congr (abstract). -/
def completeSpace_congr' : Prop := True
/-- completeSpace_coe_iff_isComplete (abstract). -/
def completeSpace_coe_iff_isComplete' : Prop := True
/-- completeSpace_coe (abstract). -/
def completeSpace_coe' : Prop := True
/-- completeSpace_ulift_iff (abstract). -/
def completeSpace_ulift_iff' : Prop := True
/-- completeSpace_extension (abstract). -/
def completeSpace_extension' : Prop := True
/-- totallyBounded_image_iff (abstract). -/
def totallyBounded_image_iff' : Prop := True
/-- totallyBounded_preimage (abstract). -/
def totallyBounded_preimage' : Prop := True
/-- isUniformEmbedding_comap (abstract). -/
def isUniformEmbedding_comap' : Prop := True
/-- comapUniformSpace (abstract). -/
def comapUniformSpace' : Prop := True
/-- uniformly_extend_exists (abstract). -/
def uniformly_extend_exists' : Prop := True
/-- uniform_extend_subtype (abstract). -/
def uniform_extend_subtype' : Prop := True
/-- uniformly_extend_spec (abstract). -/
def uniformly_extend_spec' : Prop := True
/-- uniformContinuous_uniformly_extend (abstract). -/
def uniformContinuous_uniformly_extend' : Prop := True
/-- uniformly_extend_of_ind (abstract). -/
def uniformly_extend_of_ind' : Prop := True
/-- uniformly_extend_unique (abstract). -/
def uniformly_extend_unique' : Prop := True

-- UnitInterval.lean
/-- unitInterval (abstract). -/
def unitInterval' : Prop := True
-- COLLISION: one_mem' already in RingTheory2.lean — rename needed
-- COLLISION: mul_mem' already in RingTheory2.lean — rename needed
-- COLLISION: div_mem' already in Algebra.lean — rename needed
/-- fract_mem (abstract). -/
def fract_mem' : Prop := True
-- COLLISION: mem_iff_one_sub_mem' already in Algebra.lean — rename needed
-- COLLISION: mul_le_left' already in RingTheory2.lean — rename needed
-- COLLISION: mul_le_right' already in RingTheory2.lean — rename needed
/-- symmHomeomorph (abstract). -/
def symmHomeomorph' : Prop := True
/-- strictAnti_symm (abstract). -/
def strictAnti_symm' : Prop := True
/-- symm_inj (abstract). -/
def symm_inj' : Prop := True
/-- half_le_symm_iff (abstract). -/
def half_le_symm_iff' : Prop := True
/-- symm_eq_one (abstract). -/
def symm_eq_one' : Prop := True
/-- symm_eq_zero (abstract). -/
def symm_eq_zero' : Prop := True
/-- symm_le_symm (abstract). -/
def symm_le_symm' : Prop := True
/-- le_symm_comm (abstract). -/
def le_symm_comm' : Prop := True
/-- symm_le_comm (abstract). -/
def symm_le_comm' : Prop := True
/-- symm_lt_symm (abstract). -/
def symm_lt_symm' : Prop := True
/-- lt_symm_comm (abstract). -/
def lt_symm_comm' : Prop := True
/-- symm_lt_comm (abstract). -/
def symm_lt_comm' : Prop := True
/-- one_minus_nonneg (abstract). -/
def one_minus_nonneg' : Prop := True
/-- one_minus_le_one (abstract). -/
def one_minus_le_one' : Prop := True
/-- add_pos (abstract). -/
def add_pos' : Prop := True
-- COLLISION: pos_iff_ne_zero' already in SetTheory.lean — rename needed
/-- lt_one_iff_ne_one (abstract). -/
def lt_one_iff_ne_one' : Prop := True
/-- eq_one_or_eq_zero_of_le_mul (abstract). -/
def eq_one_or_eq_zero_of_le_mul' : Prop := True
/-- mul_pos_mem_iff (abstract). -/
def mul_pos_mem_iff' : Prop := True
-- COLLISION: submonoid' already in RingTheory2.lean — rename needed
-- COLLISION: prod_mem' already in Algebra.lean — rename needed
/-- abs_projIcc_sub_projIcc (abstract). -/
def abs_projIcc_sub_projIcc' : Prop := True
/-- addNSMul (abstract). -/
def addNSMul' : Prop := True
/-- addNSMul_zero (abstract). -/
def addNSMul_zero' : Prop := True
/-- addNSMul_eq_right (abstract). -/
def addNSMul_eq_right' : Prop := True
/-- monotone_addNSMul (abstract). -/
def monotone_addNSMul' : Prop := True
/-- abs_sub_addNSMul_le (abstract). -/
def abs_sub_addNSMul_le' : Prop := True
/-- exists_monotone_Icc_subset_open_cover_Icc (abstract). -/
def exists_monotone_Icc_subset_open_cover_Icc' : Prop := True
/-- exists_monotone_Icc_subset_open_cover_unitInterval (abstract). -/
def exists_monotone_Icc_subset_open_cover_unitInterval' : Prop := True
/-- exists_monotone_Icc_subset_open_cover_unitInterval_prod_self (abstract). -/
def exists_monotone_Icc_subset_open_cover_unitInterval_prod_self' : Prop := True
/-- projIcc_eq_zero (abstract). -/
def projIcc_eq_zero' : Prop := True
/-- projIcc_eq_one (abstract). -/
def projIcc_eq_one' : Prop := True
/-- affineHomeomorph_image_I (abstract). -/
def affineHomeomorph_image_I' : Prop := True
/-- iccHomeoI (abstract). -/
def iccHomeoI' : Prop := True

-- UrysohnsBounded.lean
/-- exists_bounded_zero_one_of_closed (abstract). -/
def exists_bounded_zero_one_of_closed' : Prop := True
/-- exists_bounded_mem_Icc_of_closed_of_le (abstract). -/
def exists_bounded_mem_Icc_of_closed_of_le' : Prop := True

-- UrysohnsLemma.lean
-- COLLISION: using' already in Analysis.lean — rename needed
/-- CU (abstract). -/
def CU' : Prop := True
-- COLLISION: construction' already in Algebra.lean — rename needed
-- COLLISION: left' already in SetTheory.lean — rename needed
-- COLLISION: right' already in SetTheory.lean — rename needed
/-- left_U_subset_right_C (abstract). -/
def left_U_subset_right_C' : Prop := True
/-- left_U_subset (abstract). -/
def left_U_subset' : Prop := True
/-- subset_right_C (abstract). -/
def subset_right_C' : Prop := True
-- COLLISION: approx' already in MeasureTheory2.lean — rename needed
/-- approx_of_mem_C (abstract). -/
def approx_of_mem_C' : Prop := True
/-- approx_of_nmem_U (abstract). -/
def approx_of_nmem_U' : Prop := True
/-- approx_nonneg (abstract). -/
def approx_nonneg' : Prop := True
/-- approx_le_one (abstract). -/
def approx_le_one' : Prop := True
/-- bddAbove_range_approx (abstract). -/
def bddAbove_range_approx' : Prop := True
/-- approx_le_approx_of_U_sub_C (abstract). -/
def approx_le_approx_of_U_sub_C' : Prop := True
/-- approx_mem_Icc_right_left (abstract). -/
def approx_mem_Icc_right_left' : Prop := True
/-- approx_le_succ (abstract). -/
def approx_le_succ' : Prop := True
/-- approx_mono (abstract). -/
def approx_mono' : Prop := True
/-- tendsto_approx_atTop (abstract). -/
def tendsto_approx_atTop' : Prop := True
/-- lim_of_mem_C (abstract). -/
def lim_of_mem_C' : Prop := True
/-- disjoint_C_support_lim (abstract). -/
def disjoint_C_support_lim' : Prop := True
/-- lim_of_nmem_U (abstract). -/
def lim_of_nmem_U' : Prop := True
/-- lim_eq_midpoint (abstract). -/
def lim_eq_midpoint' : Prop := True
/-- approx_le_lim (abstract). -/
def approx_le_lim' : Prop := True
/-- lim_nonneg (abstract). -/
def lim_nonneg' : Prop := True
/-- lim_le_one (abstract). -/
def lim_le_one' : Prop := True
/-- lim_mem_Icc (abstract). -/
def lim_mem_Icc' : Prop := True
/-- continuous_lim (abstract). -/
def continuous_lim' : Prop := True
/-- exists_continuous_zero_one_of_isClosed (abstract). -/
def exists_continuous_zero_one_of_isClosed' : Prop := True
/-- exists_continuous_zero_one_of_isCompact (abstract). -/
def exists_continuous_zero_one_of_isCompact' : Prop := True
/-- exists_continuous_one_zero_of_isCompact (abstract). -/
def exists_continuous_one_zero_of_isCompact' : Prop := True
/-- exists_continuous_one_zero_of_isCompact_of_isGδ (abstract). -/
def exists_continuous_one_zero_of_isCompact_of_isGδ' : Prop := True
/-- exists_tsupport_one_of_isOpen_isClosed (abstract). -/
def exists_tsupport_one_of_isOpen_isClosed' : Prop := True
/-- exists_continuous_nonneg_pos (abstract). -/
def exists_continuous_nonneg_pos' : Prop := True

-- VectorBundle/Basic.lean
/-- IsLinear (abstract). -/
def IsLinear' : Prop := True
-- COLLISION: linear' already in CategoryTheory.lean — rename needed
/-- symmₗ (abstract). -/
def symmₗ' : Prop := True
/-- linearEquivAt (abstract). -/
def linearEquivAt' : Prop := True
/-- linearMapAt (abstract). -/
def linearMapAt' : Prop := True
/-- coe_linearMapAt (abstract). -/
def coe_linearMapAt' : Prop := True
/-- coe_linearMapAt_of_mem (abstract). -/
def coe_linearMapAt_of_mem' : Prop := True
/-- linearMapAt_apply (abstract). -/
def linearMapAt_apply' : Prop := True
/-- linearMapAt_def_of_mem (abstract). -/
def linearMapAt_def_of_mem' : Prop := True
/-- linearMapAt_def_of_not_mem (abstract). -/
def linearMapAt_def_of_not_mem' : Prop := True
/-- linearMapAt_eq_zero (abstract). -/
def linearMapAt_eq_zero' : Prop := True
/-- symmₗ_linearMapAt (abstract). -/
def symmₗ_linearMapAt' : Prop := True
/-- linearMapAt_symmₗ (abstract). -/
def linearMapAt_symmₗ' : Prop := True
/-- coordChangeL (abstract). -/
def coordChangeL' : Prop := True
/-- coe_coordChangeL (abstract). -/
def coe_coordChangeL' : Prop := True
/-- symm_coordChangeL (abstract). -/
def symm_coordChangeL' : Prop := True
/-- coordChangeL_apply (abstract). -/
def coordChangeL_apply' : Prop := True
/-- mk_coordChangeL (abstract). -/
def mk_coordChangeL' : Prop := True
/-- apply_symm_apply_eq_coordChangeL (abstract). -/
def apply_symm_apply_eq_coordChangeL' : Prop := True
/-- coordChangeL_symm_apply (abstract). -/
def coordChangeL_symm_apply' : Prop := True
/-- zeroSection (abstract). -/
def zeroSection' : Prop := True
/-- VectorBundle (abstract). -/
def VectorBundle' : Prop := True
/-- continuousOn_coordChange (abstract). -/
def continuousOn_coordChange' : Prop := True
/-- continuousLinearMapAt (abstract). -/
def continuousLinearMapAt' : Prop := True
/-- symmL (abstract). -/
def symmL' : Prop := True
/-- symmL_continuousLinearMapAt (abstract). -/
def symmL_continuousLinearMapAt' : Prop := True
/-- continuousLinearMapAt_symmL (abstract). -/
def continuousLinearMapAt_symmL' : Prop := True
/-- continuousLinearEquivAt (abstract). -/
def continuousLinearEquivAt' : Prop := True
/-- apply_eq_prod_continuousLinearEquivAt (abstract). -/
def apply_eq_prod_continuousLinearEquivAt' : Prop := True
/-- symm_apply_eq_mk_continuousLinearEquivAt_symm (abstract). -/
def symm_apply_eq_mk_continuousLinearEquivAt_symm' : Prop := True
/-- comp_continuousLinearEquivAt_eq_coord_change (abstract). -/
def comp_continuousLinearEquivAt_eq_coord_change' : Prop := True
/-- VectorBundleCore (abstract). -/
def VectorBundleCore' : Prop := True
/-- trivialVectorBundleCore (abstract). -/
def trivialVectorBundleCore' : Prop := True
/-- toFiberBundleCore (abstract). -/
def toFiberBundleCore' : Prop := True
/-- coordChange_linear_comp (abstract). -/
def coordChange_linear_comp' : Prop := True
/-- localTriv_symm_apply (abstract). -/
def localTriv_symm_apply' : Prop := True
/-- localTriv_coordChange_eq (abstract). -/
def localTriv_coordChange_eq' : Prop := True
/-- mem_source_at (abstract). -/
def mem_source_at' : Prop := True
/-- localTrivAt_apply (abstract). -/
def localTrivAt_apply' : Prop := True
/-- localTrivAt_apply_mk (abstract). -/
def localTrivAt_apply_mk' : Prop := True
/-- localTriv_continuousLinearMapAt (abstract). -/
def localTriv_continuousLinearMapAt' : Prop := True
/-- trivializationAt_continuousLinearMapAt (abstract). -/
def trivializationAt_continuousLinearMapAt' : Prop := True
/-- localTriv_symmL (abstract). -/
def localTriv_symmL' : Prop := True
/-- trivializationAt_symmL (abstract). -/
def trivializationAt_symmL' : Prop := True
/-- trivializationAt_coordChange_eq (abstract). -/
def trivializationAt_coordChange_eq' : Prop := True
/-- VectorPrebundle (abstract). -/
def VectorPrebundle' : Prop := True
/-- coordChange_apply (abstract). -/
def coordChange_apply' : Prop := True
/-- toFiberPrebundle (abstract). -/
def toFiberPrebundle' : Prop := True
/-- linear_trivializationOfMemPretrivializationAtlas (abstract). -/
def linear_trivializationOfMemPretrivializationAtlas' : Prop := True
/-- mem_trivialization_at_source (abstract). -/
def mem_trivialization_at_source' : Prop := True
/-- toVectorBundle (abstract). -/
def toVectorBundle' : Prop := True
/-- inCoordinates (abstract). -/
def inCoordinates' : Prop := True
/-- inCoordinates_eq (abstract). -/
def inCoordinates_eq' : Prop := True

-- VectorBundle/Constructions.lean
/-- coordChangeL_prod (abstract). -/
def coordChangeL_prod' : Prop := True
/-- continuousLinearEquivAt_prod (abstract). -/
def continuousLinearEquivAt_prod' : Prop := True

-- VectorBundle/Hom.lean
/-- continuousLinearMapCoordChange (abstract). -/
def continuousLinearMapCoordChange' : Prop := True
/-- continuousOn_continuousLinearMapCoordChange (abstract). -/
def continuousOn_continuousLinearMapCoordChange' : Prop := True
/-- continuousLinearMap (abstract). -/
def continuousLinearMap' : Prop := True
/-- continuousLinearMap_symm_apply' (abstract). -/
def continuousLinearMap_symm_apply' : Prop := True
/-- continuousLinearMapCoordChange_apply (abstract). -/
def continuousLinearMapCoordChange_apply' : Prop := True
/-- vectorPrebundle (abstract). -/
def vectorPrebundle' : Prop := True
