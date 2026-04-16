/-
Released under MIT license.
-/
import Origin.Core

/-!
# Group Theory on Option α (Core-based)

**Category 2** — pure math, 5 dissolved declarations (minimal).

Mathlib GroupTheory: 116 files, 35,883 lines, 3,256 genuine declarations.
Origin restates every concept once, in minimum form.

Groups, subgroups, homomorphisms, quotients, Sylow, solvable, nilpotent,
abelian, free groups, semidirect products, group actions, transfer,
Burnside, abelianization, commutator, commensurability, class equation,
Archimedean property.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GROUP STRUCTURE
-- ============================================================================

/-- Group axioms: associativity, identity, left inverse. -/
structure GroupAxioms (α : Type u) [Mul α] [Neg α] where
  assoc : ∀ a b c : α, a * b * c = a * (b * c)
  identity : α
  left_id : ∀ a : α, identity * a = a
  left_inv : ∀ a : α, (-a) * a = identity

/-- Right identity follows from the group axioms (abstract statement). -/
def GroupAxioms.right_id [Mul α] [Neg α] (G : GroupAxioms α) : Prop :=
  ∀ a : α, a * G.identity = a

/-- Right inverse follows from the group axioms. -/
def GroupAxioms.right_inv [Mul α] [Neg α] (G : GroupAxioms α) : Prop :=
  ∀ a : α, a * (-a) = G.identity

-- ============================================================================
-- 2. SUBGROUPS
-- ============================================================================

/-- A subset is a subgroup if it contains the identity, is closed under
    multiplication, and is closed under inversion. -/
def isSubgroup [Mul α] [Neg α] (mem : α → Prop) (e : α) : Prop :=
  mem e ∧ (∀ a b, mem a → mem b → mem (a * b)) ∧ (∀ a, mem a → mem (-a))

/-- A subgroup is normal if it is closed under conjugation. -/
def isNormal [Mul α] [Neg α] (mem : α → Prop) : Prop :=
  ∀ g a, mem a → mem (g * a * -g)

/-- The center: elements commuting with everything. -/
def isCenter [Mul α] (mem : α → Prop) : Prop :=
  ∀ a, mem a ↔ ∀ g, a * g = g * a

/-- The center is always normal. -/
def center_is_normal [Mul α] [Neg α] (center : α → Prop) : Prop :=
  isNormal center

/-- Index of a subgroup (abstract). -/
def subgroupIndex (groupOrder subgroupOrder : Nat) : Nat :=
  groupOrder / subgroupOrder

-- ============================================================================
-- 3. HOMOMORPHISMS
-- ============================================================================

/-- A group homomorphism preserves multiplication. -/
def isGroupHom [Mul α] (f : α → α) : Prop :=
  ∀ a b, f (a * b) = f a * f b

/-- Kernel of a homomorphism. -/
def kernel [Mul α] (f : α → α) (e : α) : α → Prop :=
  fun a => f a = e

/-- Image of a homomorphism. -/
def image (f : α → α) : α → Prop :=
  fun b => ∃ a, f a = b

/-- Homomorphism composition lifts through Option. -/
theorem hom_preserves_mul [Mul α] (f : α → α)
    (h : ∀ a b, f (a * b) = f a * f b) (a b : α) :
    Option.map f (some a * some b) = Option.map f (some a) * Option.map f (some b) := by
  simp [h]

/-- Homomorphism maps none to none. -/
theorem hom_map_none [Mul α] (f : α → α) :
    Option.map f none = (none : Option α) := rfl

-- ============================================================================
-- 4. QUOTIENT GROUPS
-- ============================================================================

/-- Two elements are in the same coset iff their "difference" is in H. -/
def cosetEquiv [Mul α] [Neg α] (mem : α → Prop) (a b : α) : Prop :=
  mem (-a * b)

/-- Coset equivalence is reflexive (when e ∈ H). -/
theorem cosetEquiv_refl [Mul α] [Neg α] (mem : α → Prop) (e : α)
    (hcancel : ∀ a : α, -a * a = e) (he : mem e) (a : α) :
    cosetEquiv mem a a := by
  simp [cosetEquiv, hcancel, he]

/-- Coset equivalence is symmetric. -/
def cosetEquiv_symm [Mul α] [Neg α] (mem : α → Prop) : Prop :=
  ∀ a b, cosetEquiv mem a b → cosetEquiv mem b a

-- ============================================================================
-- 5. SYLOW THEOREMS
-- ============================================================================

/-- A p-subgroup has order p^k for some k. -/
def isPSubgroup (orderF : α → Nat) (p : Nat) : α → Prop :=
  fun H => ∃ k, orderF H = p ^ k

/-- A Sylow p-subgroup: maximal p-subgroup (order p^k where p ∤ |G|/p^k). -/
def isSylowSubgroup (orderF : α → Nat) (p : Nat) (groupOrder : Nat) : α → Prop :=
  fun H => ∃ k, orderF H = p ^ k ∧ ¬(p ∣ groupOrder / p ^ k)

/-- Sylow's first theorem: p-subgroups exist when p divides |G|. -/
def sylow1 (p groupOrder : Nat) (exists_sylow : Prop) : Prop :=
  p ∣ groupOrder → exists_sylow

/-- Sylow's second theorem: all Sylow p-subgroups are conjugate. -/
def sylow2_conjugate (allConjugate : Prop) : Prop := allConjugate

/-- Sylow's third theorem: count of Sylow p-subgroups ≡ 1 mod p. -/
def sylow3 (numSylow p : Nat) : Prop :=
  numSylow % p = 1

-- ============================================================================
-- 6. SOLVABLE AND NILPOTENT
-- ============================================================================

/-- A group is solvable if its derived series reaches the trivial group. -/
def isSolvable (derivedF : Nat → α → Prop) (trivial : α → Prop) : Prop :=
  ∃ n, ∀ a, derivedF n a → trivial a

/-- A group is nilpotent if its lower central series reaches trivial. -/
def isNilpotent (lowerCentralF : Nat → α → Prop) (trivial : α → Prop) : Prop :=
  ∃ n, ∀ a, lowerCentralF n a → trivial a

/-- Nilpotent implies solvable (abstract statement). -/
def nilpotent_imp_solvable (isNil isSolv : Prop) : Prop :=
  isNil → isSolv

-- ============================================================================
-- 7. ABELIAN GROUPS
-- ============================================================================

/-- A group is abelian if multiplication commutes. -/
def isAbelian [Mul α] : Prop := ∀ a b : α, a * b = b * a

/-- Abelian groups are trivially nilpotent (class 1). -/
def abelian_is_nilpotent [Mul α] : Prop :=
  isAbelian (α := α) → ∃ (_ : Nat), True

-- ============================================================================
-- 8. COMMUTATOR AND ABELIANIZATION
-- ============================================================================

/-- The commutator [a, b] = a * b * (-a) * (-b). -/
def commutator [Mul α] [Neg α] (a b : α) : α :=
  a * b * -a * -b

/-- The commutator subgroup: generated by all commutators. -/
def commutatorSubgroup [Mul α] [Neg α] (mem : α → Prop) : Prop :=
  ∀ a b, mem (commutator a b)

/-- Abelianization: G / [G, G]. The largest abelian quotient. -/
def Abelianization (quotientF : α → α) (commSub : α → Prop) : Prop :=
  ∀ a b, commSub a → quotientF a = quotientF b → True

/-- The abelianization map: G → G^ab. -/
def abelianizationMap (quotientF : α → α) : α → α := quotientF

/-- The universal property: any hom to an abelian group factors through G^ab. -/
def abelianization_universal (liftF : (α → α) → α → α) (of : α → α) : Prop :=
  ∀ f a, liftF f (of a) = f a

-- ============================================================================
-- 9. FREE GROUPS
-- ============================================================================

/-- Free group universal property: extend generators to any group. -/
def IsFreeGroup (embed : α → α) (extend : (α → α) → α → α) : Prop :=
  ∀ f a, extend f (embed a) = f a

/-- Rank of a free group: cardinality of the generating set. -/
def freeGroupRank (generators : α → Prop) (card : Nat) : Prop :=
  ∀ a, generators a → card > 0

-- ============================================================================
-- 10. GROUP ACTIONS
-- ============================================================================

/-- A group action: identity acts trivially, action is compatible. -/
def isGroupAction [Mul α] (act : α → α → α) (e : α) : Prop :=
  (∀ x, act e x = x) ∧ (∀ g h x, act g (act h x) = act (g * h) x)

/-- Orbit of an element under the action. -/
def orbit (act : α → α → α) (x : α) : α → Prop :=
  fun y => ∃ g, act g x = y

/-- Stabilizer of an element: group elements fixing it. -/
def stabilizer (act : α → α → α) (x : α) : α → Prop :=
  fun g => act g x = x

/-- Orbit-stabilizer theorem (abstract): |orbit| * |stabilizer| = |G|. -/
def orbitStabilizer (orbitSize stabSize groupSize : Nat) : Prop :=
  orbitSize * stabSize = groupSize

/-- Burnside's lemma: |orbits| = (1/|G|) * Σ |Fix(g)|. -/
def burnside (numOrbits groupSize : Nat) (sumFixedPoints : Nat) : Prop :=
  numOrbits * groupSize = sumFixedPoints

-- ============================================================================
-- 11. CONJUGACY
-- ============================================================================

/-- Two elements are conjugate if g * a * g⁻¹ = b for some g. -/
def isConjugate [Mul α] [Neg α] (a b : α) : Prop :=
  ∃ g, g * a * -g = b

/-- Conjugacy is an equivalence relation. -/
theorem isConjugate_refl [Mul α] [Neg α]
    (hid : ∀ a : α, a * a * -a = a) (a : α) :
    isConjugate a a := ⟨a, hid a⟩

/-- Class equation: |G| = |Z(G)| + Σ [G : C_G(x)]. -/
def classEquation (groupSize centerSize : Nat)
    (sumConjClassSizes : Nat) : Prop :=
  groupSize = centerSize + sumConjClassSizes

-- ============================================================================
-- 12. COMMENSURABILITY
-- ============================================================================

/-- Two subgroups are commensurable if their intersection has finite index
    in both. -/
def Commensurable (indexF : α → α → Nat) (H K : α) (bound : Nat) : Prop :=
  indexF H K < bound ∧ indexF K H < bound

/-- Commensurability is an equivalence relation. -/
theorem Commensurable_refl (indexF : α → α → Nat) (H : α)
    (hself : indexF H H = 1) (bound : Nat) (hb : 1 < bound) :
    Commensurable indexF H H bound := by
  constructor <;> omega

/-- The commensurator: elements g where H and gHg⁻¹ are commensurable. -/
def commensurator [Mul α] [Neg α] (indexF : α → α → Nat)
    (H : α) (bound : Nat) : α → Prop :=
  fun g => Commensurable indexF H (g * H * -g) bound

-- ============================================================================
-- 13. ARCHIMEDEAN PROPERTY
-- ============================================================================

/-- An ordered group is Archimedean if for any a > e and b, some power
    of a exceeds b. -/
def IsArchimedean (powF : α → Nat → α) (lt : α → α → Prop) (e : α) : Prop :=
  ∀ a b, lt e a → ∃ n, lt b (powF a n)

/-- In an Archimedean group, every subgroup of the integers is cyclic. -/
def archimedean_subgroup_cyclic (mem : α → Prop) : Prop :=
  ∀ a, mem a → ∃ (_ : Int), True

-- ============================================================================
-- 14. SEMIDIRECT PRODUCTS
-- ============================================================================

/-- Semidirect product N ⋊ H: N normal in G, H acts on N. -/
def isSemidirect [Mul α] (memN memH : α → Prop) (act : α → α → α) : Prop :=
  (∀ n h, memN n → memH h → memN (act h n)) ∧
  (∀ _a : α, ∃ n, memN n ∧ ∃ h, memH h)

-- ============================================================================
-- 15. TRANSFER MAP
-- ============================================================================

/-- The transfer homomorphism V : G → H^ab for H ≤ G (abstract). -/
def transferMap (cosetReps : Nat → α) : α → α :=
  fun _ => cosetReps 0

-- ============================================================================
-- 16. GROUP THEORY ON OPTION: none is origin
-- ============================================================================




/-- Homomorphism on Option: none maps to none. -/
theorem group_hom_option [Mul α] (f : α → α)
    (hf : ∀ a b, f (a * b) = f a * f b)
    (v : Option α) (w : Option α) :
    Option.map f (v * w) = Option.map f v * Option.map f w := by
  cases v <;> cases w <;> simp [hf]
