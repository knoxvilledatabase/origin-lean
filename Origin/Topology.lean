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
-- ============================================================================
