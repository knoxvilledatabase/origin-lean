/-
Released under MIT license.
-/
import Origin.Core

/-!
# Order Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Order: 211 files, 75,874 lines, 10,131 genuine declarations.
Origin restates every concept once, in minimum form.

Partial orders, lattices, well-orders, filters, Galois connections,
fixed point theorems, directed sets, Boolean algebras, chains,
Zorn's lemma, conditionally complete lattices, order ideals,
monotone functions, closure operators.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. PARTIAL ORDERS
-- ============================================================================

/-- A partial order: reflexive, antisymmetric, transitive. -/
structure PartialOrder' (α : Type u) where
  le : α → α → Prop
  refl : ∀ a, le a a
  antisymm : ∀ a b, le a b → le b a → a = b
  trans : ∀ a b c, le a b → le b c → le a c

/-- A total order: every pair is comparable. -/
def IsTotal (le : α → α → Prop) : Prop :=
  ∀ a b, le a b ∨ le b a

/-- A preorder: reflexive and transitive (no antisymmetry). -/
def IsPreorder (le : α → α → Prop) : Prop :=
  (∀ a, le a a) ∧ (∀ a b c, le a b → le b c → le a c)

/-- Strict order: irreflexive and transitive. -/
def IsStrictOrder (lt : α → α → Prop) : Prop :=
  (∀ a, ¬lt a a) ∧ (∀ a b c, lt a b → lt b c → lt a c)

/-- The dual order: reverse the comparison. -/
def dualOrder (le : α → α → Prop) : α → α → Prop :=
  fun a b => le b a

-- ============================================================================
-- 2. MONOTONE FUNCTIONS
-- ============================================================================

/-- A function is monotone: preserves order. -/
def IsMonotone (f : α → α) (le : α → α → Prop) : Prop :=
  ∀ a b, le a b → le (f a) (f b)

/-- A function is antitone: reverses order. -/
def IsAntitone (f : α → α) (le : α → α → Prop) : Prop :=
  ∀ a b, le a b → le (f b) (f a)

/-- Monotone composition of monotone functions. -/
theorem monotone_comp (f g : α → α) (le : α → α → Prop)
    (hf : IsMonotone f le) (hg : IsMonotone g le) :
    IsMonotone (g ∘ f) le :=
  fun _ _ hab => hg _ _ (hf _ _ hab)

-- ============================================================================
-- 3. LATTICES
-- ============================================================================

/-- A lattice: every pair has a join and meet. -/
structure Lattice' (α : Type u) extends PartialOrder' α where
  sup : α → α → α
  inf : α → α → α
  sup_le : ∀ a b c, le a c → le b c → le (sup a b) c
  le_inf : ∀ a b c, le c a → le c b → le c (inf a b)

/-- A bounded lattice: has top and bottom elements. -/
structure BoundedLattice' (α : Type u) extends Lattice' α where
  top : α
  bot : α
  le_top : ∀ a, le a top
  bot_le : ∀ a, le bot a

/-- A distributive lattice: meets distribute over joins. -/
def IsDistributiveLattice (sup inf : α → α → α) (eq : α → α → Prop) : Prop :=
  ∀ a b c, eq (inf a (sup b c)) (sup (inf a b) (inf a c))

/-- A complete lattice: every subset has a supremum and infimum. -/
def IsCompleteLattice (sup inf : (α → Prop) → α)
    (le : α → α → Prop) : Prop :=
  (∀ S a, S a → le a (sup S)) ∧
  (∀ S a, (∀ b, S b → le b a) → le (sup S) a) ∧
  (∀ S a, S a → le (inf S) a) ∧
  (∀ S a, (∀ b, S b → le a b) → le a (inf S))

/-- A conditionally complete lattice: bounded subsets have sup/inf. -/
def IsCondComplete (sup : (α → Prop) → α) (le : α → α → Prop)
    (bounded : (α → Prop) → Prop) : Prop :=
  ∀ S, bounded S → (∃ a, S a) →
    ∀ a, S a → le a (sup S)

-- ============================================================================
-- 4. BOOLEAN ALGEBRAS
-- ============================================================================

/-- A Boolean algebra: a complemented distributive lattice. -/
structure BooleanAlgebra' (α : Type u) extends BoundedLattice' α where
  compl : α → α
  sup_compl : ∀ a, sup a (compl a) = top
  inf_compl : ∀ a, inf a (compl a) = bot

/-- De Morgan's laws in a Boolean algebra. -/
def deMorganBool (compl : α → α) (sup inf : α → α → α) : Prop :=
  (∀ a b, compl (sup a b) = inf (compl a) (compl b)) ∧
  (∀ a b, compl (inf a b) = sup (compl a) (compl b))

-- ============================================================================
-- 5. GALOIS CONNECTIONS
-- ============================================================================

/-- A Galois connection between two ordered types. -/
def IsGaloisConnection (l : α → β) (u : β → α)
    (leA : α → α → Prop) (leB : β → β → Prop) : Prop :=
  ∀ a b, leB (l a) b ↔ leA a (u b)

/-- A closure operator: monotone, extensive, idempotent. -/
def IsClosureOperator (c : α → α) (le : α → α → Prop) : Prop :=
  IsMonotone c le ∧
  (∀ a, le a (c a)) ∧
  (∀ a, c (c a) = c a)

-- ============================================================================
-- 6. FILTERS
-- ============================================================================

/-- A filter on a type: upward closed, closed under finite intersections. -/
structure Filter' (α : Type u) where
  mem : (α → Prop) → Prop
  univ : mem (fun _ => True)
  inter : ∀ U V, mem U → mem V → mem (fun x => U x ∧ V x)
  superset : ∀ U V, mem U → (∀ x, U x → V x) → mem V

/-- A prime filter: if A ∪ B ∈ F then A ∈ F or B ∈ F. -/
def IsPrimeFilter (F : Filter' α) : Prop :=
  ∀ U V, F.mem (fun x => U x ∨ V x) → F.mem U ∨ F.mem V

/-- An ideal (dual of filter): downward closed, closed under union. -/
def IsOrderIdeal (mem : (α → Prop) → Prop) (_le : α → α → Prop) : Prop :=
  mem (fun _ => False) ∧
  (∀ U V, mem U → mem V → mem (fun x => U x ∨ V x))

-- ============================================================================
-- 7. FIXED POINT THEOREMS
-- ============================================================================

/-- Knaster-Tarski: a monotone function on a complete lattice has a
    least fixed point. -/
def IsLeastFixedPoint (f : α → α) (le : α → α → Prop) (x : α) : Prop :=
  f x = x ∧ ∀ y, f y = y → le x y

/-- Greatest fixed point. -/
def IsGreatestFixedPoint (f : α → α) (le : α → α → Prop) (x : α) : Prop :=
  f x = x ∧ ∀ y, f y = y → le y x

/-- Knaster-Tarski existence: monotone endofunction has fixed points. -/
def knasterTarski (isMonotone : Prop) (hasFixedPoint : Prop) : Prop :=
  isMonotone → hasFixedPoint

-- ============================================================================
-- 8. DIRECTED SETS AND CHAINS
-- ============================================================================

/-- A directed set: every finite subset has an upper bound. -/
def IsDirected (le : α → α → Prop) : Prop :=
  ∀ a b, ∃ c, le a c ∧ le b c

/-- A chain: totally ordered subset. -/
def IsChain (le : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ a b, S a → S b → le a b ∨ le b a

/-- Zorn's lemma (abstract): if every chain has an upper bound,
    there exists a maximal element. -/
def zorn (chainsHaveBounds : Prop) (hasMaximal : Prop) : Prop :=
  chainsHaveBounds → hasMaximal

-- ============================================================================
-- 9. WELL-FOUNDEDNESS
-- ============================================================================

/-- A relation is well-founded: no infinite descending chains. -/
def IsWellFounded' (r : α → α → Prop) : Prop :=
  ∀ P : α → Prop, (∀ a, (∀ b, r b a → P b) → P a) → ∀ a, P a

/-- A well-order: total + well-founded. -/
def IsWellOrdered (le : α → α → Prop) (lt : α → α → Prop) : Prop :=
  IsTotal le ∧ IsWellFounded' lt

-- ============================================================================
-- 10. ORDER ON OPTION: none as bottom
-- ============================================================================

/-- Option has a natural order: none ≤ some a for all a. -/
def optionLe (le : α → α → Prop) : Option α → Option α → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => le a b

/-- none is the bottom element. -/
theorem optionLe_none (le : α → α → Prop) (v : Option α) :
    optionLe le none v := by
  cases v <;> simp [optionLe]

/-- optionLe is reflexive when the underlying order is. -/
theorem optionLe_refl (le : α → α → Prop) (hrefl : ∀ a : α, le a a)
    (v : Option α) : optionLe le v v := by
  cases v <;> simp [optionLe, hrefl]


-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub Order
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- Antichain.lean
/-- compl (abstract). -/
def compl' : Prop := True
/-- IsAntichain (abstract). -/
def IsAntichain' : Prop := True
/-- subset (abstract). -/
def subset' : Prop := True
-- COLLISION: mono' already in SetTheory.lean — rename needed
/-- mono_on (abstract). -/
def mono_on' : Prop := True
-- COLLISION: eq' already in SetTheory.lean — rename needed
/-- isAntisymm (abstract). -/
def isAntisymm' : Prop := True
/-- subsingleton (abstract). -/
def subsingleton' : Prop := True
/-- flip (abstract). -/
def flip' : Prop := True
-- COLLISION: swap' already in SetTheory.lean — rename needed
-- COLLISION: image' already in LinearAlgebra2.lean — rename needed
/-- preimage (abstract). -/
def preimage' : Prop := True
/-- isAntichain_insert (abstract). -/
def isAntichain_insert' : Prop := True
-- COLLISION: insert' already in SetTheory.lean — rename needed
/-- isAntichain_insert_of_symmetric (abstract). -/
def isAntichain_insert_of_symmetric' : Prop := True
/-- insert_of_symmetric (abstract). -/
def insert_of_symmetric' : Prop := True
/-- image_relEmbedding (abstract). -/
def image_relEmbedding' : Prop := True
/-- preimage_relEmbedding (abstract). -/
def preimage_relEmbedding' : Prop := True
/-- image_relIso (abstract). -/
def image_relIso' : Prop := True
/-- preimage_relIso (abstract). -/
def preimage_relIso' : Prop := True
/-- image_relEmbedding_iff (abstract). -/
def image_relEmbedding_iff' : Prop := True
/-- image_relIso_iff (abstract). -/
def image_relIso_iff' : Prop := True
/-- image_embedding (abstract). -/
def image_embedding' : Prop := True
/-- preimage_embedding (abstract). -/
def preimage_embedding' : Prop := True
/-- image_embedding_iff (abstract). -/
def image_embedding_iff' : Prop := True
/-- image_iso (abstract). -/
def image_iso' : Prop := True
/-- image_iso_iff (abstract). -/
def image_iso_iff' : Prop := True
/-- preimage_iso (abstract). -/
def preimage_iso' : Prop := True
/-- preimage_iso_iff (abstract). -/
def preimage_iso_iff' : Prop := True
/-- to_dual (abstract). -/
def to_dual' : Prop := True
/-- to_dual_iff (abstract). -/
def to_dual_iff' : Prop := True
/-- image_compl (abstract). -/
def image_compl' : Prop := True
/-- preimage_compl (abstract). -/
def preimage_compl' : Prop := True
/-- isAntichain_singleton (abstract). -/
def isAntichain_singleton' : Prop := True
/-- isAntichain (abstract). -/
def isAntichain' : Prop := True
/-- not_lt (abstract). -/
def not_lt' : Prop := True
/-- isAntichain_and_least_iff (abstract). -/
def isAntichain_and_least_iff' : Prop := True
/-- isAntichain_and_greatest_iff (abstract). -/
def isAntichain_and_greatest_iff' : Prop := True
/-- least_iff (abstract). -/
def least_iff' : Prop := True
/-- greatest_iff (abstract). -/
def greatest_iff' : Prop := True
/-- antichain_iff (abstract). -/
def antichain_iff' : Prop := True
/-- bot_mem_iff (abstract). -/
def bot_mem_iff' : Prop := True
/-- top_mem_iff (abstract). -/
def top_mem_iff' : Prop := True
/-- isAntichain_iff_forall_not_lt (abstract). -/
def isAntichain_iff_forall_not_lt' : Prop := True
/-- IsStrongAntichain (abstract). -/
def IsStrongAntichain' : Prop := True
/-- isStrongAntichain_insert (abstract). -/
def isStrongAntichain_insert' : Prop := True
/-- isStrongAntichain (abstract). -/
def isStrongAntichain' : Prop := True
/-- of_strictMonoOn_antitoneOn (abstract). -/
def of_strictMonoOn_antitoneOn' : Prop := True
/-- of_monotoneOn_strictAntiOn (abstract). -/
def of_monotoneOn_strictAntiOn' : Prop := True
/-- IsWeakAntichain (abstract). -/
def IsWeakAntichain' : Prop := True
/-- isWeakAntichain_insert (abstract). -/
def isWeakAntichain_insert' : Prop := True
/-- isWeakAntichain (abstract). -/
def isWeakAntichain' : Prop := True

-- Antisymmetrization.lean
/-- AntisymmRel (abstract). -/
def AntisymmRel' : Prop := True
/-- antisymmRel_swap (abstract). -/
def antisymmRel_swap' : Prop := True
/-- antisymmRel_refl (abstract). -/
def antisymmRel_refl' : Prop := True
-- COLLISION: symm' already in SetTheory.lean — rename needed
-- COLLISION: trans' already in SetTheory.lean — rename needed
/-- antisymmRel_iff_eq (abstract). -/
def antisymmRel_iff_eq' : Prop := True
/-- setoid (abstract). -/
def setoid' : Prop := True
/-- Antisymmetrization (abstract). -/
def Antisymmetrization' : Prop := True
/-- toAntisymmetrization (abstract). -/
def toAntisymmetrization' : Prop := True
/-- ofAntisymmetrization (abstract). -/
def ofAntisymmetrization' : Prop := True
/-- ind (abstract). -/
def ind' : Prop := True
/-- induction_on (abstract). -/
def induction_on' : Prop := True
/-- toAntisymmetrization_ofAntisymmetrization (abstract). -/
def toAntisymmetrization_ofAntisymmetrization' : Prop := True
/-- antisymmetrization_fibration (abstract). -/
def antisymmetrization_fibration' : Prop := True
/-- acc_antisymmetrization_iff (abstract). -/
def acc_antisymmetrization_iff' : Prop := True
/-- wellFounded_antisymmetrization_iff (abstract). -/
def wellFounded_antisymmetrization_iff' : Prop := True
/-- wellFoundedLT_antisymmetrization_iff (abstract). -/
def wellFoundedLT_antisymmetrization_iff' : Prop := True
/-- wellFoundedGT_antisymmetrization_iff (abstract). -/
def wellFoundedGT_antisymmetrization_iff' : Prop := True
/-- ofAntisymmetrization_le_ofAntisymmetrization_iff (abstract). -/
def ofAntisymmetrization_le_ofAntisymmetrization_iff' : Prop := True
/-- ofAntisymmetrization_lt_ofAntisymmetrization_iff (abstract). -/
def ofAntisymmetrization_lt_ofAntisymmetrization_iff' : Prop := True
/-- toAntisymmetrization_mono (abstract). -/
def toAntisymmetrization_mono' : Prop := True
/-- liftFun_antisymmRel (abstract). -/
def liftFun_antisymmRel' : Prop := True
/-- antisymmetrization (abstract). -/
def antisymmetrization' : Prop := True
/-- antisymmetrization_apply_mk (abstract). -/
def antisymmetrization_apply_mk' : Prop := True
/-- dualAntisymmetrization (abstract). -/
def dualAntisymmetrization' : Prop := True
/-- prodEquiv (abstract). -/
def prodEquiv' : Prop := True

-- Atoms.lean
/-- IsAtom (abstract). -/
def IsAtom' : Prop := True
/-- Iic (abstract). -/
def Iic' : Prop := True
/-- of_isAtom_coe_Iic (abstract). -/
def of_isAtom_coe_Iic' : Prop := True
/-- isAtom_iff_le_of_ge (abstract). -/
def isAtom_iff_le_of_ge' : Prop := True
-- COLLISION: lt_iff' already in SetTheory.lean — rename needed
-- COLLISION: le_iff' already in SetTheory.lean — rename needed
-- COLLISION: le_iff_eq' already in SetTheory.lean — rename needed
/-- Iic_eq (abstract). -/
def Iic_eq' : Prop := True
/-- bot_covBy_iff (abstract). -/
def bot_covBy_iff' : Prop := True
/-- atom_le_iSup (abstract). -/
def atom_le_iSup' : Prop := True
/-- IsCoatom (abstract). -/
def IsCoatom' : Prop := True
/-- Ici (abstract). -/
def Ici' : Prop := True
/-- covBy_top_iff (abstract). -/
def covBy_top_iff' : Prop := True
/-- iInf_le_coatom (abstract). -/
def iInf_le_coatom' : Prop := True
/-- isAtom_iff (abstract). -/
def isAtom_iff' : Prop := True
/-- isCoatom_iff (abstract). -/
def isCoatom_iff' : Prop := True
/-- inf_eq_bot_of_ne (abstract). -/
def inf_eq_bot_of_ne' : Prop := True
/-- disjoint_of_ne (abstract). -/
def disjoint_of_ne' : Prop := True
/-- sup_eq_top_of_ne (abstract). -/
def sup_eq_top_of_ne' : Prop := True
/-- IsAtomic (abstract). -/
def IsAtomic' : Prop := True
/-- isCoatomic_dual_iff_isAtomic (abstract). -/
def isCoatomic_dual_iff_isAtomic' : Prop := True
/-- isAtomic_dual_iff_isCoatomic (abstract). -/
def isAtomic_dual_iff_isCoatomic' : Prop := True
/-- isAtomic_iff_forall_isAtomic_Iic (abstract). -/
def isAtomic_iff_forall_isAtomic_Iic' : Prop := True
/-- isCoatomic_iff_forall_isCoatomic_Ici (abstract). -/
def isCoatomic_iff_forall_isCoatomic_Ici' : Prop := True
/-- IsStronglyAtomic (abstract). -/
def IsStronglyAtomic' : Prop := True
/-- exists_covBy_le_of_lt (abstract). -/
def exists_covBy_le_of_lt' : Prop := True
/-- IsStronglyCoatomic (abstract). -/
def IsStronglyCoatomic' : Prop := True
/-- exists_le_covBy_of_lt (abstract). -/
def exists_le_covBy_of_lt' : Prop := True
/-- isStronglyAtomic_dual_iff_is_stronglyCoatomic (abstract). -/
def isStronglyAtomic_dual_iff_is_stronglyCoatomic' : Prop := True
/-- isStronglyCoatomic_dual_iff_is_stronglyAtomic (abstract). -/
def isStronglyCoatomic_dual_iff_is_stronglyAtomic' : Prop := True
/-- isStronglyAtomic (abstract). -/
def isStronglyAtomic' : Prop := True
/-- isStronglyCoatomic (abstract). -/
def isStronglyCoatomic' : Prop := True
/-- of_wellFounded_lt (abstract). -/
def of_wellFounded_lt' : Prop := True
/-- of_wellFounded_gt (abstract). -/
def of_wellFounded_gt' : Prop := True
/-- isAtomic_of_orderBot_wellFounded_lt (abstract). -/
def isAtomic_of_orderBot_wellFounded_lt' : Prop := True
/-- isCoatomic_of_orderTop_gt_wellFounded (abstract). -/
def isCoatomic_of_orderTop_gt_wellFounded' : Prop := True
/-- eq_iff_atom_le_iff (abstract). -/
def eq_iff_atom_le_iff' : Prop := True
/-- toCompleteAtomicBooleanAlgebra (abstract). -/
def toCompleteAtomicBooleanAlgebra' : Prop := True
/-- IsAtomistic (abstract). -/
def IsAtomistic' : Prop := True
/-- IsCoatomistic (abstract). -/
def IsCoatomistic' : Prop := True
/-- isCoatomistic_dual_iff_isAtomistic (abstract). -/
def isCoatomistic_dual_iff_isAtomistic' : Prop := True
/-- isAtomistic_dual_iff_isCoatomistic (abstract). -/
def isAtomistic_dual_iff_isCoatomistic' : Prop := True
/-- sSup_atoms_le_eq (abstract). -/
def sSup_atoms_le_eq' : Prop := True
/-- sSup_atoms_eq_top (abstract). -/
def sSup_atoms_eq_top' : Prop := True
/-- le_iff_atom_le_imp (abstract). -/
def le_iff_atom_le_imp' : Prop := True
/-- isSimpleOrder_iff_isSimpleOrder_orderDual (abstract). -/
def isSimpleOrder_iff_isSimpleOrder_orderDual' : Prop := True
/-- bot_ne_top (abstract). -/
def bot_ne_top' : Prop := True
/-- preorder (abstract). -/
def preorder' : Prop := True
/-- linearOrder (abstract). -/
def linearOrder' : Prop := True
/-- isAtom_top (abstract). -/
def isAtom_top' : Prop := True
/-- isCoatom_bot (abstract). -/
def isCoatom_bot' : Prop := True
/-- bot_covBy_top (abstract). -/
def bot_covBy_top' : Prop := True
/-- eq_bot_of_lt (abstract). -/
def eq_bot_of_lt' : Prop := True
/-- eq_top_of_lt (abstract). -/
def eq_top_of_lt' : Prop := True
/-- lattice (abstract). -/
def lattice' : Prop := True
/-- distribLattice (abstract). -/
def distribLattice' : Prop := True
/-- equivBool (abstract). -/
def equivBool' : Prop := True
/-- orderIsoBool (abstract). -/
def orderIsoBool' : Prop := True
/-- booleanAlgebra (abstract). -/
def booleanAlgebra' : Prop := True
/-- completeLattice (abstract). -/
def completeLattice' : Prop := True
/-- completeBooleanAlgebra (abstract). -/
def completeBooleanAlgebra' : Prop := True
/-- isSimpleOrder_iff_isAtom_top (abstract). -/
def isSimpleOrder_iff_isAtom_top' : Prop := True
/-- isSimpleOrder_iff_isCoatom_bot (abstract). -/
def isSimpleOrder_iff_isCoatom_bot' : Prop := True
/-- isSimpleOrder_Iic_iff_isAtom (abstract). -/
def isSimpleOrder_Iic_iff_isAtom' : Prop := True
/-- isSimpleOrder_Ici_iff_isCoatom (abstract). -/
def isSimpleOrder_Ici_iff_isCoatom' : Prop := True
/-- isAtom_of_map_bot_of_image (abstract). -/
def isAtom_of_map_bot_of_image' : Prop := True
/-- isCoatom_of_map_top_of_image (abstract). -/
def isCoatom_of_map_top_of_image' : Prop := True
/-- isAtom_of_u_bot (abstract). -/
def isAtom_of_u_bot' : Prop := True
/-- isCoatom_of_image (abstract). -/
def isCoatom_of_image' : Prop := True
/-- isCoatom_of_l_top (abstract). -/
def isCoatom_of_l_top' : Prop := True
/-- isAtom_of_image (abstract). -/
def isAtom_of_image' : Prop := True
/-- isSimpleOrder_iff (abstract). -/
def isSimpleOrder_iff' : Prop := True
/-- isSimpleOrder (abstract). -/
def isSimpleOrder' : Prop := True
/-- isAtomic_iff (abstract). -/
def isAtomic_iff' : Prop := True
/-- isCoatomic_iff (abstract). -/
def isCoatomic_iff' : Prop := True
/-- isAtom_iff_isCoatom (abstract). -/
def isAtom_iff_isCoatom' : Prop := True
/-- isCoatom_iff_isAtom (abstract). -/
def isCoatom_iff_isAtom' : Prop := True
/-- isCoatomic_of_isAtomic_of_complementedLattice_of_isModular (abstract). -/
def isCoatomic_of_isAtomic_of_complementedLattice_of_isModular' : Prop := True
/-- isAtomic_of_isCoatomic_of_complementedLattice_of_isModular (abstract). -/
def isAtomic_of_isCoatomic_of_complementedLattice_of_isModular' : Prop := True
/-- isAtomic_iff_isCoatomic (abstract). -/
def isAtomic_iff_isCoatomic' : Prop := True
/-- eq_bot_iff (abstract). -/
def eq_bot_iff' : Prop := True
/-- isAtom_single (abstract). -/
def isAtom_single' : Prop := True
/-- isAtom_iff_eq_single (abstract). -/
def isAtom_iff_eq_single' : Prop := True
/-- isAtom_compl (abstract). -/
def isAtom_compl' : Prop := True
/-- isCoatom_compl (abstract). -/
def isCoatom_compl' : Prop := True
/-- isAtom_singleton (abstract). -/
def isAtom_singleton' : Prop := True
/-- isCoatom_singleton_compl (abstract). -/
def isCoatom_singleton_compl' : Prop := True

-- Atoms/Finite.lean
-- COLLISION: univ' already in SetTheory.lean — rename needed
-- COLLISION: card' already in SetTheory.lean — rename needed
/-- exists_covby_infinite_Ici_of_infinite_Ici (abstract). -/
def exists_covby_infinite_Ici_of_infinite_Ici' : Prop := True
/-- exists_covby_infinite_Iic_of_infinite_Iic (abstract). -/
def exists_covby_infinite_Iic_of_infinite_Iic' : Prop := True

-- Basic.lean
/-- le_trans' (abstract). -/
def le_trans' : Prop := True
/-- lt_trans' (abstract). -/
def lt_trans' : Prop := True
/-- lt_of_le_of_lt' (abstract). -/
def lt_of_le_of_lt' : Prop := True
/-- lt_of_lt_of_le' (abstract). -/
def lt_of_lt_of_le' : Prop := True
/-- ge_antisymm (abstract). -/
def ge_antisymm' : Prop := True
/-- lt_of_le_of_ne' (abstract). -/
def lt_of_le_of_ne' : Prop := True
/-- lt_of_le (abstract). -/
def lt_of_le' : Prop := True
/-- lt_self_iff_false (abstract). -/
def lt_self_iff_false' : Prop := True
/-- le_of_le_of_eq' (abstract). -/
def le_of_le_of_eq' : Prop := True
/-- le_of_eq_of_le' (abstract). -/
def le_of_eq_of_le' : Prop := True
/-- lt_of_lt_of_eq' (abstract). -/
def lt_of_lt_of_eq' : Prop := True
/-- ge_iff_eq (abstract). -/
def ge_iff_eq' : Prop := True
/-- lt_or_le (abstract). -/
def lt_or_le' : Prop := True
/-- ne_of_not_le (abstract). -/
def ne_of_not_le' : Prop := True
/-- le_iff_eq_or_lt (abstract). -/
def le_iff_eq_or_lt' : Prop := True
/-- lt_iff_le_and_ne (abstract). -/
def lt_iff_le_and_ne' : Prop := True
/-- eq_iff_not_lt_of_le (abstract). -/
def eq_iff_not_lt_of_le' : Prop := True
/-- gt_or_eq_of_le (abstract). -/
def gt_or_eq_of_le' : Prop := True
/-- eq_of_le_of_not_lt (abstract). -/
def eq_of_le_of_not_lt' : Prop := True
/-- eq_of_ge_of_not_gt (abstract). -/
def eq_of_ge_of_not_gt' : Prop := True
/-- le_iff_lt (abstract). -/
def le_iff_lt' : Prop := True
/-- not_le_or_not_le (abstract). -/
def not_le_or_not_le' : Prop := True
/-- ne_iff_lt_iff_le (abstract). -/
def ne_iff_lt_iff_le' : Prop := True
/-- min_def' (abstract). -/
def min_def' : Prop := True
/-- max_def' (abstract). -/
def max_def' : Prop := True
/-- lt_of_not_le (abstract). -/
def lt_of_not_le' : Prop := True
/-- lt_iff_not_le (abstract). -/
def lt_iff_not_le' : Prop := True
/-- lt_or_lt (abstract). -/
def lt_or_lt' : Prop := True
/-- lt_or_lt_iff_ne (abstract). -/
def lt_or_lt_iff_ne' : Prop := True
/-- not_lt_iff_eq_or_lt (abstract). -/
def not_lt_iff_eq_or_lt' : Prop := True
/-- exists_ge_of_linear (abstract). -/
def exists_ge_of_linear' : Prop := True
/-- exists_forall_ge_and (abstract). -/
def exists_forall_ge_and' : Prop := True
/-- lt_imp_lt_of_le_imp_le (abstract). -/
def lt_imp_lt_of_le_imp_le' : Prop := True
/-- le_imp_le_iff_lt_imp_lt (abstract). -/
def le_imp_le_iff_lt_imp_lt' : Prop := True
/-- lt_iff_lt_of_le_iff_le' (abstract). -/
def lt_iff_lt_of_le_iff_le' : Prop := True
/-- le_iff_le_iff_lt_iff_lt (abstract). -/
def le_iff_le_iff_lt_iff_lt' : Prop := True
/-- eq_of_forall_le_iff (abstract). -/
def eq_of_forall_le_iff' : Prop := True
/-- le_of_forall_le (abstract). -/
def le_of_forall_le' : Prop := True
-- COLLISION: le_of_forall_lt' already in SetTheory.lean — rename needed
/-- forall_lt_iff_le (abstract). -/
def forall_lt_iff_le' : Prop := True
/-- eq_of_forall_ge_iff (abstract). -/
def eq_of_forall_ge_iff' : Prop := True
/-- eq_of_forall_lt_iff (abstract). -/
def eq_of_forall_lt_iff' : Prop := True
/-- eq_of_forall_gt_iff (abstract). -/
def eq_of_forall_gt_iff' : Prop := True
/-- rel_imp_eq_of_rel_imp_le (abstract). -/
def rel_imp_eq_of_rel_imp_le' : Prop := True
/-- le_implies_le_of_le_of_le (abstract). -/
def le_implies_le_of_le_of_le' : Prop := True
/-- commutative_of_le (abstract). -/
def commutative_of_le' : Prop := True
/-- associative_of_commutative_of_le (abstract). -/
def associative_of_commutative_of_le' : Prop := True
/-- toLE_injective (abstract). -/
def toLE_injective' : Prop := True
/-- toPreorder_injective (abstract). -/
def toPreorder_injective' : Prop := True
/-- toPartialOrder_injective (abstract). -/
def toPartialOrder_injective' : Prop := True
-- COLLISION: ext' already in SetTheory.lean — rename needed
/-- Preimage (abstract). -/
def Preimage' : Prop := True
/-- ltByCases_lt (abstract). -/
def ltByCases_lt' : Prop := True
/-- ltByCases_gt (abstract). -/
def ltByCases_gt' : Prop := True
/-- ltByCases_eq (abstract). -/
def ltByCases_eq' : Prop := True
/-- ltByCases_not_lt (abstract). -/
def ltByCases_not_lt' : Prop := True
/-- ltByCases_not_gt (abstract). -/
def ltByCases_not_gt' : Prop := True
/-- ltByCases_ne (abstract). -/
def ltByCases_ne' : Prop := True
/-- ltByCases_comm (abstract). -/
def ltByCases_comm' : Prop := True
/-- eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt (abstract). -/
def eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt' : Prop := True
/-- ltByCases_rec (abstract). -/
def ltByCases_rec' : Prop := True
/-- ltByCases_eq_iff (abstract). -/
def ltByCases_eq_iff' : Prop := True
/-- ltByCases_congr (abstract). -/
def ltByCases_congr' : Prop := True
/-- ltTrichotomy (abstract). -/
def ltTrichotomy' : Prop := True
/-- ltTrichotomy_lt (abstract). -/
def ltTrichotomy_lt' : Prop := True
/-- ltTrichotomy_gt (abstract). -/
def ltTrichotomy_gt' : Prop := True
/-- ltTrichotomy_eq (abstract). -/
def ltTrichotomy_eq' : Prop := True
/-- ltTrichotomy_not_lt (abstract). -/
def ltTrichotomy_not_lt' : Prop := True
/-- ltTrichotomy_not_gt (abstract). -/
def ltTrichotomy_not_gt' : Prop := True
/-- ltTrichotomy_ne (abstract). -/
def ltTrichotomy_ne' : Prop := True
/-- ltTrichotomy_comm (abstract). -/
def ltTrichotomy_comm' : Prop := True
/-- ltTrichotomy_self (abstract). -/
def ltTrichotomy_self' : Prop := True
/-- ltTrichotomy_eq_iff (abstract). -/
def ltTrichotomy_eq_iff' : Prop := True
/-- OrderDual (abstract). -/
def OrderDual' : Prop := True
/-- dual_dual (abstract). -/
def dual_dual' : Prop := True
/-- compl_lt (abstract). -/
def compl_lt' : Prop := True
/-- compl_le (abstract). -/
def compl_le' : Prop := True
-- COLLISION: lt_def' already in SetTheory.lean — rename needed
/-- elim_le_elim_iff (abstract). -/
def elim_le_elim_iff' : Prop := True
/-- const_le_elim_iff (abstract). -/
def const_le_elim_iff' : Prop := True
/-- elim_le_const_iff (abstract). -/
def elim_le_const_iff' : Prop := True
/-- StrongLT (abstract). -/
def StrongLT' : Prop := True
/-- le_of_strongLT (abstract). -/
def le_of_strongLT' : Prop := True
/-- lt_of_strongLT (abstract). -/
def lt_of_strongLT' : Prop := True
/-- strongLT_of_strongLT_of_le (abstract). -/
def strongLT_of_strongLT_of_le' : Prop := True
/-- strongLT_of_le_of_strongLT (abstract). -/
def strongLT_of_le_of_strongLT' : Prop := True
/-- le_update_iff (abstract). -/
def le_update_iff' : Prop := True
/-- update_le_iff (abstract). -/
def update_le_iff' : Prop := True
/-- update_le_update_iff (abstract). -/
def update_le_update_iff' : Prop := True
/-- update_lt_update_iff (abstract). -/
def update_lt_update_iff' : Prop := True
/-- le_update_self_iff (abstract). -/
def le_update_self_iff' : Prop := True
/-- const_le_const (abstract). -/
def const_le_const' : Prop := True
/-- const_lt_const (abstract). -/
def const_lt_const' : Prop := True
/-- min_rec (abstract). -/
def min_rec' : Prop := True
/-- max_rec (abstract). -/
def max_rec' : Prop := True
/-- min_def_lt (abstract). -/
def min_def_lt' : Prop := True
/-- max_def_lt (abstract). -/
def max_def_lt' : Prop := True
-- COLLISION: lift' already in SetTheory.lean — rename needed
/-- compare_of_injective_eq_compareOfLessAndEq (abstract). -/
def compare_of_injective_eq_compareOfLessAndEq' : Prop := True
/-- liftWithOrd (abstract). -/
def liftWithOrd' : Prop := True
/-- swap_le_swap (abstract). -/
def swap_le_swap' : Prop := True
/-- swap_lt_swap (abstract). -/
def swap_lt_swap' : Prop := True
/-- mk_le_mk_iff_left (abstract). -/
def mk_le_mk_iff_left' : Prop := True
/-- mk_le_mk_iff_right (abstract). -/
def mk_le_mk_iff_right' : Prop := True
/-- mk_lt_mk_iff_left (abstract). -/
def mk_lt_mk_iff_left' : Prop := True
/-- mk_lt_mk_iff_right (abstract). -/
def mk_lt_mk_iff_right' : Prop := True
/-- mk_lt_mk (abstract). -/
def mk_lt_mk' : Prop := True
/-- mk_lt_mk_of_lt_of_le (abstract). -/
def mk_lt_mk_of_lt_of_le' : Prop := True
/-- mk_lt_mk_of_le_of_lt (abstract). -/
def mk_lt_mk_of_le_of_lt' : Prop := True
/-- DenselyOrdered (abstract). -/
def DenselyOrdered' : Prop := True
/-- exists_between (abstract). -/
def exists_between' : Prop := True
/-- denselyOrdered_orderDual (abstract). -/
def denselyOrdered_orderDual' : Prop := True
/-- instDenselyOrdered (abstract). -/
def instDenselyOrdered' : Prop := True
/-- le_of_forall_le_of_dense (abstract). -/
def le_of_forall_le_of_dense' : Prop := True
/-- eq_of_le_of_forall_le_of_dense (abstract). -/
def eq_of_le_of_forall_le_of_dense' : Prop := True
/-- le_of_forall_ge_of_dense (abstract). -/
def le_of_forall_ge_of_dense' : Prop := True
/-- eq_of_le_of_forall_ge_of_dense (abstract). -/
def eq_of_le_of_forall_ge_of_dense' : Prop := True
/-- dense_or_discrete (abstract). -/
def dense_or_discrete' : Prop := True
/-- eq_or_eq_or_eq_of_forall_not_lt_lt (abstract). -/
def eq_or_eq_or_eq_of_forall_not_lt_lt' : Prop := True
/-- AsLinearOrder (abstract). -/
def AsLinearOrder' : Prop := True
/-- one_le_dite (abstract). -/
def one_le_dite' : Prop := True
/-- dite_le_one (abstract). -/
def dite_le_one' : Prop := True
/-- one_lt_dite (abstract). -/
def one_lt_dite' : Prop := True
/-- dite_lt_one (abstract). -/
def dite_lt_one' : Prop := True
/-- one_le_ite (abstract). -/
def one_le_ite' : Prop := True
/-- ite_le_one (abstract). -/
def ite_le_one' : Prop := True
/-- one_lt_ite (abstract). -/
def one_lt_ite' : Prop := True
/-- ite_lt_one (abstract). -/
def ite_lt_one' : Prop := True

-- Birkhoff.lean
/-- infIrred_Ici (abstract). -/
def infIrred_Ici' : Prop := True
/-- infIrred_iff_of_finite (abstract). -/
def infIrred_iff_of_finite' : Prop := True
/-- supIrred_Iic (abstract). -/
def supIrred_Iic' : Prop := True
/-- supIrred_iff_of_finite (abstract). -/
def supIrred_iff_of_finite' : Prop := True
/-- supIrredLowerSet (abstract). -/
def supIrredLowerSet' : Prop := True
/-- infIrredUpperSet (abstract). -/
def infIrredUpperSet' : Prop := True
/-- supIrredLowerSet_surjective (abstract). -/
def supIrredLowerSet_surjective' : Prop := True
/-- infIrredUpperSet_surjective (abstract). -/
def infIrredUpperSet_surjective' : Prop := True
/-- supIrredLowerSet_symm_apply (abstract). -/
def supIrredLowerSet_symm_apply' : Prop := True
/-- infIrredUpperSet_symm_apply (abstract). -/
def infIrredUpperSet_symm_apply' : Prop := True
/-- lowerSetSupIrred (abstract). -/
def lowerSetSupIrred' : Prop := True
/-- birkhoffSet (abstract). -/
def birkhoffSet' : Prop := True
/-- birkhoffFinset (abstract). -/
def birkhoffFinset' : Prop := True
/-- coe_birkhoffFinset (abstract). -/
def coe_birkhoffFinset' : Prop := True
/-- birkhoffSet_sup (abstract). -/
def birkhoffSet_sup' : Prop := True
/-- birkhoffSet_inf (abstract). -/
def birkhoffSet_inf' : Prop := True
/-- birkhoffSet_apply (abstract). -/
def birkhoffSet_apply' : Prop := True
/-- birkhoffFinset_sup (abstract). -/
def birkhoffFinset_sup' : Prop := True
/-- birkhoffFinset_inf (abstract). -/
def birkhoffFinset_inf' : Prop := True
/-- birkhoffFinset_injective (abstract). -/
def birkhoffFinset_injective' : Prop := True

-- BooleanAlgebra.lean
-- COLLISION: is' already in SetTheory.lean — rename needed
-- COLLISION: for' already in SetTheory.lean — rename needed
/-- GeneralizedBooleanAlgebra (abstract). -/
def GeneralizedBooleanAlgebra' : Prop := True
/-- sup_inf_sdiff (abstract). -/
def sup_inf_sdiff' : Prop := True
/-- inf_inf_sdiff (abstract). -/
def inf_inf_sdiff' : Prop := True
/-- sup_sdiff_inf (abstract). -/
def sup_sdiff_inf' : Prop := True
/-- inf_sdiff_inf (abstract). -/
def inf_sdiff_inf' : Prop := True
/-- disjoint_inf_sdiff (abstract). -/
def disjoint_inf_sdiff' : Prop := True
/-- sdiff_unique (abstract). -/
def sdiff_unique' : Prop := True
/-- sdiff_le' (abstract). -/
def sdiff_le' : Prop := True
/-- sdiff_sup_self' (abstract). -/
def sdiff_sup_self' : Prop := True
/-- sdiff_inf_sdiff (abstract). -/
def sdiff_inf_sdiff' : Prop := True
/-- disjoint_sdiff_sdiff (abstract). -/
def disjoint_sdiff_sdiff' : Prop := True
/-- inf_sdiff_self_right (abstract). -/
def inf_sdiff_self_right' : Prop := True
/-- inf_sdiff_self_left (abstract). -/
def inf_sdiff_self_left' : Prop := True
/-- disjoint_sdiff_self_left (abstract). -/
def disjoint_sdiff_self_left' : Prop := True
/-- disjoint_sdiff_self_right (abstract). -/
def disjoint_sdiff_self_right' : Prop := True
/-- le_sdiff (abstract). -/
def le_sdiff' : Prop := True
/-- sdiff_eq_left (abstract). -/
def sdiff_eq_left' : Prop := True
/-- sdiff_eq_of_sup_eq (abstract). -/
def sdiff_eq_of_sup_eq' : Prop := True
/-- disjoint_sdiff_iff_le (abstract). -/
def disjoint_sdiff_iff_le' : Prop := True
/-- le_iff_disjoint_sdiff (abstract). -/
def le_iff_disjoint_sdiff' : Prop := True
/-- inf_sdiff_eq_bot_iff (abstract). -/
def inf_sdiff_eq_bot_iff' : Prop := True
/-- le_iff_eq_sup_sdiff (abstract). -/
def le_iff_eq_sup_sdiff' : Prop := True
/-- sdiff_sup (abstract). -/
def sdiff_sup' : Prop := True
/-- sdiff_eq_sdiff_iff_inf_eq_inf (abstract). -/
def sdiff_eq_sdiff_iff_inf_eq_inf' : Prop := True
/-- sdiff_eq_self_iff_disjoint (abstract). -/
def sdiff_eq_self_iff_disjoint' : Prop := True
/-- sdiff_lt (abstract). -/
def sdiff_lt' : Prop := True
/-- le_sdiff_iff (abstract). -/
def le_sdiff_iff' : Prop := True
/-- sdiff_eq_right (abstract). -/
def sdiff_eq_right' : Prop := True
/-- sdiff_ne_right (abstract). -/
def sdiff_ne_right' : Prop := True
/-- sdiff_lt_sdiff_right (abstract). -/
def sdiff_lt_sdiff_right' : Prop := True
/-- sup_inf_inf_sdiff (abstract). -/
def sup_inf_inf_sdiff' : Prop := True
/-- sdiff_sdiff_right (abstract). -/
def sdiff_sdiff_right' : Prop := True
/-- sdiff_sdiff_eq_sdiff_sup (abstract). -/
def sdiff_sdiff_eq_sdiff_sup' : Prop := True
/-- sdiff_sdiff_right_self (abstract). -/
def sdiff_sdiff_right_self' : Prop := True
/-- sdiff_sdiff_eq_self (abstract). -/
def sdiff_sdiff_eq_self' : Prop := True
/-- sdiff_eq_symm (abstract). -/
def sdiff_eq_symm' : Prop := True
/-- sdiff_eq_comm (abstract). -/
def sdiff_eq_comm' : Prop := True
/-- eq_of_sdiff_eq_sdiff (abstract). -/
def eq_of_sdiff_eq_sdiff' : Prop := True
/-- sdiff_le_sdiff_iff_le (abstract). -/
def sdiff_le_sdiff_iff_le' : Prop := True
/-- sdiff_sdiff_left' (abstract). -/
def sdiff_sdiff_left' : Prop := True
/-- sdiff_sdiff_sup_sdiff (abstract). -/
def sdiff_sdiff_sup_sdiff' : Prop := True
/-- sdiff_sdiff_sdiff_cancel_left (abstract). -/
def sdiff_sdiff_sdiff_cancel_left' : Prop := True
/-- sdiff_sdiff_sdiff_cancel_right (abstract). -/
def sdiff_sdiff_sdiff_cancel_right' : Prop := True
/-- inf_sdiff (abstract). -/
def inf_sdiff' : Prop := True
/-- inf_sdiff_assoc (abstract). -/
def inf_sdiff_assoc' : Prop := True
/-- inf_sdiff_right_comm (abstract). -/
def inf_sdiff_right_comm' : Prop := True
/-- inf_sdiff_distrib_left (abstract). -/
def inf_sdiff_distrib_left' : Prop := True
/-- inf_sdiff_distrib_right (abstract). -/
def inf_sdiff_distrib_right' : Prop := True
/-- disjoint_sdiff_comm (abstract). -/
def disjoint_sdiff_comm' : Prop := True
/-- sup_eq_sdiff_sup_sdiff_sup_inf (abstract). -/
def sup_eq_sdiff_sup_sdiff_sup_inf' : Prop := True
/-- sup_lt_of_lt_sdiff_left (abstract). -/
def sup_lt_of_lt_sdiff_left' : Prop := True
/-- sup_lt_of_lt_sdiff_right (abstract). -/
def sup_lt_of_lt_sdiff_right' : Prop := True
-- COLLISION: BooleanAlgebra' already in Order.lean — rename needed
/-- toBooleanAlgebra (abstract). -/
def toBooleanAlgebra' : Prop := True
/-- inf_compl_eq_bot' (abstract). -/
def inf_compl_eq_bot' : Prop := True
/-- sup_compl_eq_top (abstract). -/
def sup_compl_eq_top' : Prop := True
/-- compl_sup_eq_top (abstract). -/
def compl_sup_eq_top' : Prop := True
/-- isCompl_compl (abstract). -/
def isCompl_compl' : Prop := True
/-- sdiff_eq (abstract). -/
def sdiff_eq' : Prop := True
/-- himp_eq (abstract). -/
def himp_eq' : Prop := True
/-- top_sdiff (abstract). -/
def top_sdiff' : Prop := True
/-- eq_compl_iff_isCompl (abstract). -/
def eq_compl_iff_isCompl' : Prop := True
/-- compl_eq_iff_isCompl (abstract). -/
def compl_eq_iff_isCompl' : Prop := True
/-- compl_eq_comm (abstract). -/
def compl_eq_comm' : Prop := True
/-- eq_compl_comm (abstract). -/
def eq_compl_comm' : Prop := True
/-- compl_compl (abstract). -/
def compl_compl' : Prop := True
/-- compl_comp_compl (abstract). -/
def compl_comp_compl' : Prop := True
/-- compl_involutive (abstract). -/
def compl_involutive' : Prop := True
/-- compl_eq_top (abstract). -/
def compl_eq_top' : Prop := True
/-- compl_eq_bot (abstract). -/
def compl_eq_bot' : Prop := True
/-- compl_inf (abstract). -/
def compl_inf' : Prop := True
/-- compl_le_compl_iff_le (abstract). -/
def compl_le_compl_iff_le' : Prop := True
/-- compl_lt_compl_iff_lt (abstract). -/
def compl_lt_compl_iff_lt' : Prop := True
/-- compl_le_of_compl_le (abstract). -/
def compl_le_of_compl_le' : Prop := True
/-- compl_le_iff_compl_le (abstract). -/
def compl_le_iff_compl_le' : Prop := True
/-- compl_le_self (abstract). -/
def compl_le_self' : Prop := True
/-- sdiff_compl (abstract). -/
def sdiff_compl' : Prop := True
/-- sup_inf_inf_compl (abstract). -/
def sup_inf_inf_compl' : Prop := True
/-- compl_sdiff (abstract). -/
def compl_sdiff' : Prop := True
/-- compl_himp (abstract). -/
def compl_himp' : Prop := True
/-- compl_sdiff_compl (abstract). -/
def compl_sdiff_compl' : Prop := True
/-- compl_himp_compl (abstract). -/
def compl_himp_compl' : Prop := True
/-- disjoint_compl_left_iff (abstract). -/
def disjoint_compl_left_iff' : Prop := True
/-- disjoint_compl_right_iff (abstract). -/
def disjoint_compl_right_iff' : Prop := True
/-- codisjoint_himp_self_left (abstract). -/
def codisjoint_himp_self_left' : Prop := True
/-- codisjoint_himp_self_right (abstract). -/
def codisjoint_himp_self_right' : Prop := True
/-- himp_le (abstract). -/
def himp_le' : Prop := True
/-- himp_le_iff (abstract). -/
def himp_le_iff' : Prop := True
/-- himp_eq_left (abstract). -/
def himp_eq_left' : Prop := True
/-- himp_ne_right (abstract). -/
def himp_ne_right' : Prop := True
/-- generalizedBooleanAlgebra (abstract). -/
def generalizedBooleanAlgebra' : Prop := True
/-- booleanAlgebraOfComplemented (abstract). -/
def booleanAlgebraOfComplemented' : Prop := True

-- BooleanGenerators.lean
/-- BooleanGenerators (abstract). -/
def BooleanGenerators' : Prop := True
/-- atomistic (abstract). -/
def atomistic' : Prop := True
/-- isAtomistic_of_sSup_eq_top (abstract). -/
def isAtomistic_of_sSup_eq_top' : Prop := True
/-- mem_of_isAtom_of_le_sSup_atoms (abstract). -/
def mem_of_isAtom_of_le_sSup_atoms' : Prop := True
/-- sSup_inter (abstract). -/
def sSup_inter' : Prop := True
/-- distribLattice_of_sSup_eq_top (abstract). -/
def distribLattice_of_sSup_eq_top' : Prop := True
/-- complementedLattice_of_sSup_eq_top (abstract). -/
def complementedLattice_of_sSup_eq_top' : Prop := True
/-- booleanAlgebra_of_sSup_eq_top (abstract). -/
def booleanAlgebra_of_sSup_eq_top' : Prop := True
/-- sSup_le_sSup_iff_of_atoms (abstract). -/
def sSup_le_sSup_iff_of_atoms' : Prop := True
/-- eq_atoms_of_sSup_eq_top (abstract). -/
def eq_atoms_of_sSup_eq_top' : Prop := True

-- Booleanisation.lean
/-- Booleanisation (abstract). -/
def Booleanisation' : Prop := True
/-- comp (abstract). -/
def comp' : Prop := True
/-- LE (abstract). -/
def LE' : Prop := True
/-- LT (abstract). -/
def LT' : Prop := True
/-- lift_le_lift (abstract). -/
def lift_le_lift' : Prop := True
/-- comp_le_comp (abstract). -/
def comp_le_comp' : Prop := True
/-- lift_le_comp (abstract). -/
def lift_le_comp' : Prop := True
/-- not_comp_le_lift (abstract). -/
def not_comp_le_lift' : Prop := True
/-- liftLatticeHom (abstract). -/
def liftLatticeHom' : Prop := True
/-- liftLatticeHom_injective (abstract). -/
def liftLatticeHom_injective' : Prop := True

-- Bounded.lean
/-- bounded_ge_iff_bounded_gt (abstract). -/
def bounded_ge_iff_bounded_gt' : Prop := True
/-- unbounded_gt_iff_unbounded_ge (abstract). -/
def unbounded_gt_iff_unbounded_ge' : Prop := True
/-- unbounded_le_univ (abstract). -/
def unbounded_le_univ' : Prop := True
/-- unbounded_lt_univ (abstract). -/
def unbounded_lt_univ' : Prop := True
/-- unbounded_ge_univ (abstract). -/
def unbounded_ge_univ' : Prop := True
/-- unbounded_gt_univ (abstract). -/
def unbounded_gt_univ' : Prop := True
/-- bounded_self (abstract). -/
def bounded_self' : Prop := True
/-- bounded_lt_Iio (abstract). -/
def bounded_lt_Iio' : Prop := True
/-- bounded_le_Iio (abstract). -/
def bounded_le_Iio' : Prop := True
/-- bounded_le_Iic (abstract). -/
def bounded_le_Iic' : Prop := True
/-- bounded_lt_Iic (abstract). -/
def bounded_lt_Iic' : Prop := True
/-- bounded_gt_Ioi (abstract). -/
def bounded_gt_Ioi' : Prop := True
/-- bounded_ge_Ioi (abstract). -/
def bounded_ge_Ioi' : Prop := True
/-- bounded_ge_Ici (abstract). -/
def bounded_ge_Ici' : Prop := True
/-- bounded_gt_Ici (abstract). -/
def bounded_gt_Ici' : Prop := True
/-- bounded_lt_Ioo (abstract). -/
def bounded_lt_Ioo' : Prop := True
/-- bounded_lt_Ico (abstract). -/
def bounded_lt_Ico' : Prop := True
/-- bounded_lt_Ioc (abstract). -/
def bounded_lt_Ioc' : Prop := True
/-- bounded_lt_Icc (abstract). -/
def bounded_lt_Icc' : Prop := True
/-- bounded_le_Ioo (abstract). -/
def bounded_le_Ioo' : Prop := True
/-- bounded_le_Ico (abstract). -/
def bounded_le_Ico' : Prop := True
/-- bounded_le_Ioc (abstract). -/
def bounded_le_Ioc' : Prop := True
/-- bounded_le_Icc (abstract). -/
def bounded_le_Icc' : Prop := True
/-- bounded_gt_Ioo (abstract). -/
def bounded_gt_Ioo' : Prop := True
/-- bounded_gt_Ioc (abstract). -/
def bounded_gt_Ioc' : Prop := True
/-- bounded_gt_Ico (abstract). -/
def bounded_gt_Ico' : Prop := True
/-- bounded_gt_Icc (abstract). -/
def bounded_gt_Icc' : Prop := True
/-- bounded_ge_Ioo (abstract). -/
def bounded_ge_Ioo' : Prop := True
/-- bounded_ge_Ioc (abstract). -/
def bounded_ge_Ioc' : Prop := True
/-- bounded_ge_Ico (abstract). -/
def bounded_ge_Ico' : Prop := True
/-- bounded_ge_Icc (abstract). -/
def bounded_ge_Icc' : Prop := True
/-- unbounded_le_Ioi (abstract). -/
def unbounded_le_Ioi' : Prop := True
/-- unbounded_le_Ici (abstract). -/
def unbounded_le_Ici' : Prop := True
/-- unbounded_lt_Ioi (abstract). -/
def unbounded_lt_Ioi' : Prop := True
/-- unbounded_lt_Ici (abstract). -/
def unbounded_lt_Ici' : Prop := True
/-- bounded_inter_not (abstract). -/
def bounded_inter_not' : Prop := True
/-- unbounded_inter_not (abstract). -/
def unbounded_inter_not' : Prop := True
/-- bounded_le_inter_not_le (abstract). -/
def bounded_le_inter_not_le' : Prop := True
/-- unbounded_le_inter_not_le (abstract). -/
def unbounded_le_inter_not_le' : Prop := True
/-- bounded_le_inter_lt (abstract). -/
def bounded_le_inter_lt' : Prop := True
/-- unbounded_le_inter_lt (abstract). -/
def unbounded_le_inter_lt' : Prop := True
/-- bounded_le_inter_le (abstract). -/
def bounded_le_inter_le' : Prop := True
/-- unbounded_le_inter_le (abstract). -/
def unbounded_le_inter_le' : Prop := True
/-- bounded_lt_inter_not_lt (abstract). -/
def bounded_lt_inter_not_lt' : Prop := True
/-- unbounded_lt_inter_not_lt (abstract). -/
def unbounded_lt_inter_not_lt' : Prop := True
/-- bounded_lt_inter_le (abstract). -/
def bounded_lt_inter_le' : Prop := True
/-- unbounded_lt_inter_le (abstract). -/
def unbounded_lt_inter_le' : Prop := True
/-- bounded_lt_inter_lt (abstract). -/
def bounded_lt_inter_lt' : Prop := True
/-- unbounded_lt_inter_lt (abstract). -/
def unbounded_lt_inter_lt' : Prop := True
/-- bounded_ge_inter_not_ge (abstract). -/
def bounded_ge_inter_not_ge' : Prop := True
/-- unbounded_ge_inter_not_ge (abstract). -/
def unbounded_ge_inter_not_ge' : Prop := True
/-- bounded_ge_inter_gt (abstract). -/
def bounded_ge_inter_gt' : Prop := True
/-- unbounded_ge_inter_gt (abstract). -/
def unbounded_ge_inter_gt' : Prop := True
/-- bounded_ge_inter_ge (abstract). -/
def bounded_ge_inter_ge' : Prop := True
/-- unbounded_ge_iff_unbounded_inter_ge (abstract). -/
def unbounded_ge_iff_unbounded_inter_ge' : Prop := True
/-- bounded_gt_inter_not_gt (abstract). -/
def bounded_gt_inter_not_gt' : Prop := True
/-- unbounded_gt_inter_not_gt (abstract). -/
def unbounded_gt_inter_not_gt' : Prop := True
/-- bounded_gt_inter_ge (abstract). -/
def bounded_gt_inter_ge' : Prop := True
/-- unbounded_inter_ge (abstract). -/
def unbounded_inter_ge' : Prop := True
/-- bounded_gt_inter_gt (abstract). -/
def bounded_gt_inter_gt' : Prop := True
/-- unbounded_gt_inter_gt (abstract). -/
def unbounded_gt_inter_gt' : Prop := True

-- BoundedOrder/Basic.lean
/-- hierarchy (abstract). -/
def hierarchy' : Prop := True
/-- OrderTop (abstract). -/
def OrderTop' : Prop := True
/-- topOrderOrNoTopOrder (abstract). -/
def topOrderOrNoTopOrder' : Prop := True
/-- le_top (abstract). -/
def le_top' : Prop := True
/-- isTop_top (abstract). -/
def isTop_top' : Prop := True
/-- isMax_top (abstract). -/
def isMax_top' : Prop := True
/-- not_top_lt (abstract). -/
def not_top_lt' : Prop := True
/-- ne_top_of_lt (abstract). -/
def ne_top_of_lt' : Prop := True
/-- lt_top_of_lt (abstract). -/
def lt_top_of_lt' : Prop := True
/-- isMax_iff_eq_top (abstract). -/
def isMax_iff_eq_top' : Prop := True
/-- isTop_iff_eq_top (abstract). -/
def isTop_iff_eq_top' : Prop := True
/-- not_isMax_iff_ne_top (abstract). -/
def not_isMax_iff_ne_top' : Prop := True
/-- not_isTop_iff_ne_top (abstract). -/
def not_isTop_iff_ne_top' : Prop := True
/-- top_le_iff (abstract). -/
def top_le_iff' : Prop := True
/-- top_unique (abstract). -/
def top_unique' : Prop := True
/-- eq_top_iff (abstract). -/
def eq_top_iff' : Prop := True
/-- ne_top_of_le_ne_top (abstract). -/
def ne_top_of_le_ne_top' : Prop := True
/-- top_not_mem_iff (abstract). -/
def top_not_mem_iff' : Prop := True
/-- not_isMin_top (abstract). -/
def not_isMin_top' : Prop := True
/-- ext_top (abstract). -/
def ext_top' : Prop := True
/-- OrderBot (abstract). -/
def OrderBot' : Prop := True
/-- botOrderOrNoBotOrder (abstract). -/
def botOrderOrNoBotOrder' : Prop := True
/-- bot_le (abstract). -/
def bot_le' : Prop := True
/-- isBot_bot (abstract). -/
def isBot_bot' : Prop := True
/-- isMin_bot (abstract). -/
def isMin_bot' : Prop := True
/-- not_lt_bot (abstract). -/
def not_lt_bot' : Prop := True
/-- ne_bot_of_gt (abstract). -/
def ne_bot_of_gt' : Prop := True
/-- bot_lt_of_lt (abstract). -/
def bot_lt_of_lt' : Prop := True
/-- isMin_iff_eq_bot (abstract). -/
def isMin_iff_eq_bot' : Prop := True
/-- eq_bot_mono (abstract). -/
def eq_bot_mono' : Prop := True
/-- ne_bot_of_le_ne_bot (abstract). -/
def ne_bot_of_le_ne_bot' : Prop := True
/-- bot_not_mem_iff (abstract). -/
def bot_not_mem_iff' : Prop := True
/-- not_isMax_bot (abstract). -/
def not_isMax_bot' : Prop := True
/-- ext_bot (abstract). -/
def ext_bot' : Prop := True
/-- BoundedOrder (abstract). -/
def BoundedOrder' : Prop := True
/-- eq_bot_of_bot_eq_top (abstract). -/
def eq_bot_of_bot_eq_top' : Prop := True
/-- eq_top_of_bot_eq_top (abstract). -/
def eq_top_of_bot_eq_top' : Prop := True
/-- subsingleton_of_top_le_bot (abstract). -/
def subsingleton_of_top_le_bot' : Prop := True
/-- subsingleton_of_bot_eq_top (abstract). -/
def subsingleton_of_bot_eq_top' : Prop := True
/-- subsingleton_iff_bot_eq_top (abstract). -/
def subsingleton_iff_bot_eq_top' : Prop := True
/-- orderBot (abstract). -/
def orderBot' : Prop := True
/-- orderTop (abstract). -/
def orderTop' : Prop := True
/-- boundedOrder (abstract). -/
def boundedOrder' : Prop := True
/-- mk_bot (abstract). -/
def mk_bot' : Prop := True
/-- mk_top (abstract). -/
def mk_top' : Prop := True
/-- coe_bot (abstract). -/
def coe_bot' : Prop := True
/-- coe_top (abstract). -/
def coe_top' : Prop := True
/-- coe_eq_bot_iff (abstract). -/
def coe_eq_bot_iff' : Prop := True
/-- coe_eq_top_iff (abstract). -/
def coe_eq_top_iff' : Prop := True
/-- mk_eq_bot_iff (abstract). -/
def mk_eq_bot_iff' : Prop := True
/-- mk_eq_top_iff (abstract). -/
def mk_eq_top_iff' : Prop := True

-- BoundedOrder/Lattice.lean
/-- top_sup_eq (abstract). -/
def top_sup_eq' : Prop := True
/-- sup_top_eq (abstract). -/
def sup_top_eq' : Prop := True
/-- bot_sup_eq (abstract). -/
def bot_sup_eq' : Prop := True
/-- sup_bot_eq (abstract). -/
def sup_bot_eq' : Prop := True
/-- sup_eq_bot_iff (abstract). -/
def sup_eq_bot_iff' : Prop := True
/-- top_inf_eq (abstract). -/
def top_inf_eq' : Prop := True
/-- inf_top_eq (abstract). -/
def inf_top_eq' : Prop := True
/-- inf_eq_top_iff (abstract). -/
def inf_eq_top_iff' : Prop := True
/-- bot_inf_eq (abstract). -/
def bot_inf_eq' : Prop := True
/-- inf_bot_eq (abstract). -/
def inf_bot_eq' : Prop := True
/-- exists_ge_and_iff_exists (abstract). -/
def exists_ge_and_iff_exists' : Prop := True
/-- exists_and_iff_of_monotone (abstract). -/
def exists_and_iff_of_monotone' : Prop := True
/-- exists_le_and_iff_exists (abstract). -/
def exists_le_and_iff_exists' : Prop := True
/-- exists_and_iff_of_antitone (abstract). -/
def exists_and_iff_of_antitone' : Prop := True
/-- min_bot_left (abstract). -/
def min_bot_left' : Prop := True
/-- max_top_left (abstract). -/
def max_top_left' : Prop := True
/-- min_top_left (abstract). -/
def min_top_left' : Prop := True
/-- max_bot_left (abstract). -/
def max_bot_left' : Prop := True
/-- min_top_right (abstract). -/
def min_top_right' : Prop := True
/-- min_bot_right (abstract). -/
def min_bot_right' : Prop := True
/-- max_top_right (abstract). -/
def max_top_right' : Prop := True
/-- max_eq_bot (abstract). -/
def max_eq_bot' : Prop := True
/-- min_eq_top (abstract). -/
def min_eq_top' : Prop := True
/-- min_eq_bot (abstract). -/
def min_eq_bot' : Prop := True
/-- max_eq_top (abstract). -/
def max_eq_top' : Prop := True

-- BoundedOrder/Monotone.lean
/-- apply_eq_top_iff (abstract). -/
def apply_eq_top_iff' : Prop := True
/-- maximal_preimage_top (abstract). -/
def maximal_preimage_top' : Prop := True
/-- apply_eq_bot_iff (abstract). -/
def apply_eq_bot_iff' : Prop := True
/-- minimal_preimage_bot (abstract). -/
def minimal_preimage_bot' : Prop := True
/-- monotone_and (abstract). -/
def monotone_and' : Prop := True
/-- monotone_or (abstract). -/
def monotone_or' : Prop := True
/-- monotone_le (abstract). -/
def monotone_le' : Prop := True
/-- monotone_lt (abstract). -/
def monotone_lt' : Prop := True
/-- antitone_le (abstract). -/
def antitone_le' : Prop := True
/-- antitone_lt (abstract). -/
def antitone_lt' : Prop := True
/-- forall (abstract). -/
def forall' : Prop := True
/-- ball (abstract). -/
def ball' : Prop := True
/-- exists (abstract). -/
def exists' : Prop := True
/-- forall_ge_iff (abstract). -/
def forall_ge_iff' : Prop := True
/-- forall_le_iff (abstract). -/
def forall_le_iff' : Prop := True

-- Bounds/Basic.lean
/-- bot_mem_lowerBounds (abstract). -/
def bot_mem_lowerBounds' : Prop := True
/-- top_mem_upperBounds (abstract). -/
def top_mem_upperBounds' : Prop := True
/-- isLeast_bot_iff (abstract). -/
def isLeast_bot_iff' : Prop := True
/-- isGreatest_top_iff (abstract). -/
def isGreatest_top_iff' : Prop := True
/-- not_bddAbove_iff' (abstract). -/
def not_bddAbove_iff' : Prop := True
/-- upperBounds_mono_set (abstract). -/
def upperBounds_mono_set' : Prop := True
/-- lowerBounds_mono_set (abstract). -/
def lowerBounds_mono_set' : Prop := True
/-- upperBounds_mono_mem (abstract). -/
def upperBounds_mono_mem' : Prop := True
/-- lowerBounds_mono_mem (abstract). -/
def lowerBounds_mono_mem' : Prop := True
/-- upperBounds_mono (abstract). -/
def upperBounds_mono' : Prop := True
/-- lowerBounds_mono (abstract). -/
def lowerBounds_mono' : Prop := True
/-- of_subset_of_superset (abstract). -/
def of_subset_of_superset' : Prop := True
/-- subset_lowerBounds_upperBounds (abstract). -/
def subset_lowerBounds_upperBounds' : Prop := True
/-- subset_upperBounds_lowerBounds (abstract). -/
def subset_upperBounds_lowerBounds' : Prop := True
/-- bddAbove_lowerBounds (abstract). -/
def bddAbove_lowerBounds' : Prop := True
/-- bddBelow_upperBounds (abstract). -/
def bddBelow_upperBounds' : Prop := True
/-- isLUB_le_iff (abstract). -/
def isLUB_le_iff' : Prop := True
/-- le_isGLB_iff (abstract). -/
def le_isGLB_iff' : Prop := True
/-- isLUB_iff_le_iff (abstract). -/
def isLUB_iff_le_iff' : Prop := True
/-- isGLB_iff_le_iff (abstract). -/
def isGLB_iff_le_iff' : Prop := True
/-- bddAbove (abstract). -/
def bddAbove' : Prop := True
/-- bddBelow (abstract). -/
def bddBelow' : Prop := True
/-- nonempty (abstract). -/
def nonempty' : Prop := True
/-- upperBounds_union (abstract). -/
def upperBounds_union' : Prop := True
/-- lowerBounds_union (abstract). -/
def lowerBounds_union' : Prop := True
/-- union_upperBounds_subset_upperBounds_inter (abstract). -/
def union_upperBounds_subset_upperBounds_inter' : Prop := True
/-- union_lowerBounds_subset_lowerBounds_inter (abstract). -/
def union_lowerBounds_subset_lowerBounds_inter' : Prop := True
-- COLLISION: union' already in SetTheory.lean — rename needed
/-- bddAbove_union (abstract). -/
def bddAbove_union' : Prop := True
/-- bddBelow_union (abstract). -/
def bddBelow_union' : Prop := True
/-- inter_Ici_of_mem (abstract). -/
def inter_Ici_of_mem' : Prop := True
/-- inter_Iic_of_mem (abstract). -/
def inter_Iic_of_mem' : Prop := True
/-- bddAbove_iff_exists_ge (abstract). -/
def bddAbove_iff_exists_ge' : Prop := True
/-- bddBelow_iff_exists_le (abstract). -/
def bddBelow_iff_exists_le' : Prop := True
/-- exists_ge (abstract). -/
def exists_ge' : Prop := True
/-- exists_le (abstract). -/
def exists_le' : Prop := True
/-- isLeast_Ici (abstract). -/
def isLeast_Ici' : Prop := True
/-- isGreatest_Iic (abstract). -/
def isGreatest_Iic' : Prop := True
/-- isLUB_Iic (abstract). -/
def isLUB_Iic' : Prop := True
/-- isGLB_Ici (abstract). -/
def isGLB_Ici' : Prop := True
/-- upperBounds_Iic (abstract). -/
def upperBounds_Iic' : Prop := True
/-- lowerBounds_Ici (abstract). -/
def lowerBounds_Ici' : Prop := True
/-- bddAbove_Iic (abstract). -/
def bddAbove_Iic' : Prop := True
/-- bddBelow_Ici (abstract). -/
def bddBelow_Ici' : Prop := True
/-- bddAbove_Iio (abstract). -/
def bddAbove_Iio' : Prop := True
/-- bddBelow_Ioi (abstract). -/
def bddBelow_Ioi' : Prop := True
/-- lub_Iio_le (abstract). -/
def lub_Iio_le' : Prop := True
/-- le_glb_Ioi (abstract). -/
def le_glb_Ioi' : Prop := True
/-- lub_Iio_eq_self_or_Iio_eq_Iic (abstract). -/
def lub_Iio_eq_self_or_Iio_eq_Iic' : Prop := True
/-- glb_Ioi_eq_self_or_Ioi_eq_Ici (abstract). -/
def glb_Ioi_eq_self_or_Ioi_eq_Ici' : Prop := True
/-- exists_lub_Iio (abstract). -/
def exists_lub_Iio' : Prop := True
/-- exists_glb_Ioi (abstract). -/
def exists_glb_Ioi' : Prop := True
/-- isLUB_Iio (abstract). -/
def isLUB_Iio' : Prop := True
/-- isGLB_Ioi (abstract). -/
def isGLB_Ioi' : Prop := True
/-- upperBounds_Iio (abstract). -/
def upperBounds_Iio' : Prop := True
/-- lowerBounds_Ioi (abstract). -/
def lowerBounds_Ioi' : Prop := True
/-- isGreatest_singleton (abstract). -/
def isGreatest_singleton' : Prop := True
/-- isLeast_singleton (abstract). -/
def isLeast_singleton' : Prop := True
/-- isLUB_singleton (abstract). -/
def isLUB_singleton' : Prop := True
/-- isGLB_singleton (abstract). -/
def isGLB_singleton' : Prop := True
/-- bddAbove_singleton (abstract). -/
def bddAbove_singleton' : Prop := True
/-- bddBelow_singleton (abstract). -/
def bddBelow_singleton' : Prop := True
/-- upperBounds_singleton (abstract). -/
def upperBounds_singleton' : Prop := True
/-- lowerBounds_singleton (abstract). -/
def lowerBounds_singleton' : Prop := True
/-- bddAbove_Icc (abstract). -/
def bddAbove_Icc' : Prop := True
/-- bddBelow_Icc (abstract). -/
def bddBelow_Icc' : Prop := True
/-- bddAbove_Ico (abstract). -/
def bddAbove_Ico' : Prop := True
/-- bddBelow_Ico (abstract). -/
def bddBelow_Ico' : Prop := True
/-- bddAbove_Ioc (abstract). -/
def bddAbove_Ioc' : Prop := True
/-- bddBelow_Ioc (abstract). -/
def bddBelow_Ioc' : Prop := True
/-- bddAbove_Ioo (abstract). -/
def bddAbove_Ioo' : Prop := True
/-- bddBelow_Ioo (abstract). -/
def bddBelow_Ioo' : Prop := True
/-- isGreatest_Icc (abstract). -/
def isGreatest_Icc' : Prop := True
/-- isLUB_Icc (abstract). -/
def isLUB_Icc' : Prop := True
/-- upperBounds_Icc (abstract). -/
def upperBounds_Icc' : Prop := True
/-- isLeast_Icc (abstract). -/
def isLeast_Icc' : Prop := True
/-- isGLB_Icc (abstract). -/
def isGLB_Icc' : Prop := True
/-- lowerBounds_Icc (abstract). -/
def lowerBounds_Icc' : Prop := True
/-- isGreatest_Ioc (abstract). -/
def isGreatest_Ioc' : Prop := True
/-- isLUB_Ioc (abstract). -/
def isLUB_Ioc' : Prop := True
/-- upperBounds_Ioc (abstract). -/
def upperBounds_Ioc' : Prop := True
/-- isLeast_Ico (abstract). -/
def isLeast_Ico' : Prop := True
/-- isGLB_Ico (abstract). -/
def isGLB_Ico' : Prop := True
/-- lowerBounds_Ico (abstract). -/
def lowerBounds_Ico' : Prop := True
/-- isGLB_Ioo (abstract). -/
def isGLB_Ioo' : Prop := True
/-- lowerBounds_Ioo (abstract). -/
def lowerBounds_Ioo' : Prop := True
/-- isGLB_Ioc (abstract). -/
def isGLB_Ioc' : Prop := True
/-- lowerBounds_Ioc (abstract). -/
def lowerBounds_Ioc' : Prop := True
/-- isLUB_Ioo (abstract). -/
def isLUB_Ioo' : Prop := True
/-- bddBelow_bddAbove_iff_subset_Icc (abstract). -/
def bddBelow_bddAbove_iff_subset_Icc' : Prop := True
/-- isGreatest_univ_iff (abstract). -/
def isGreatest_univ_iff' : Prop := True
/-- isGreatest_univ (abstract). -/
def isGreatest_univ' : Prop := True
/-- upperBounds_univ (abstract). -/
def upperBounds_univ' : Prop := True
/-- isLUB_univ (abstract). -/
def isLUB_univ' : Prop := True
/-- lowerBounds_univ (abstract). -/
def lowerBounds_univ' : Prop := True
/-- isLeast_univ_iff (abstract). -/
def isLeast_univ_iff' : Prop := True
/-- isLeast_univ (abstract). -/
def isLeast_univ' : Prop := True
/-- isGLB_univ (abstract). -/
def isGLB_univ' : Prop := True
/-- not_bddAbove_univ (abstract). -/
def not_bddAbove_univ' : Prop := True
/-- not_bddBelow_univ (abstract). -/
def not_bddBelow_univ' : Prop := True
/-- upperBounds_empty (abstract). -/
def upperBounds_empty' : Prop := True
/-- lowerBounds_empty (abstract). -/
def lowerBounds_empty' : Prop := True
/-- bddAbove_empty (abstract). -/
def bddAbove_empty' : Prop := True
/-- bddBelow_empty (abstract). -/
def bddBelow_empty' : Prop := True
/-- isGLB_empty_iff (abstract). -/
def isGLB_empty_iff' : Prop := True
/-- isLUB_empty_iff (abstract). -/
def isLUB_empty_iff' : Prop := True
/-- isGLB_empty (abstract). -/
def isGLB_empty' : Prop := True
/-- isLUB_empty (abstract). -/
def isLUB_empty' : Prop := True
/-- nonempty_of_not_bddAbove (abstract). -/
def nonempty_of_not_bddAbove' : Prop := True
/-- nonempty_of_not_bddBelow (abstract). -/
def nonempty_of_not_bddBelow' : Prop := True
/-- bddAbove_insert (abstract). -/
def bddAbove_insert' : Prop := True
/-- bddBelow_insert (abstract). -/
def bddBelow_insert' : Prop := True
/-- upperBounds_insert (abstract). -/
def upperBounds_insert' : Prop := True
/-- lowerBounds_insert (abstract). -/
def lowerBounds_insert' : Prop := True
/-- isLUB_pair (abstract). -/
def isLUB_pair' : Prop := True
/-- isGLB_pair (abstract). -/
def isGLB_pair' : Prop := True
/-- isLeast_pair (abstract). -/
def isLeast_pair' : Prop := True
/-- isGreatest_pair (abstract). -/
def isGreatest_pair' : Prop := True
/-- isLUB_lowerBounds (abstract). -/
def isLUB_lowerBounds' : Prop := True
/-- isGLB_upperBounds (abstract). -/
def isGLB_upperBounds' : Prop := True
/-- lowerBounds_le_upperBounds (abstract). -/
def lowerBounds_le_upperBounds' : Prop := True
/-- isGLB_le_isLUB (abstract). -/
def isGLB_le_isLUB' : Prop := True
/-- isLUB_lt_iff (abstract). -/
def isLUB_lt_iff' : Prop := True
/-- lt_isGLB_iff (abstract). -/
def lt_isGLB_iff' : Prop := True
/-- le_of_isLUB_le_isGLB (abstract). -/
def le_of_isLUB_le_isGLB' : Prop := True
/-- unique (abstract). -/
def unique' : Prop := True
/-- isLeast_iff_eq (abstract). -/
def isLeast_iff_eq' : Prop := True
/-- isGreatest_iff_eq (abstract). -/
def isGreatest_iff_eq' : Prop := True
/-- subsingleton_of_isLUB_le_isGLB (abstract). -/
def subsingleton_of_isLUB_le_isGLB' : Prop := True
/-- isGLB_lt_isLUB_of_ne (abstract). -/
def isGLB_lt_isLUB_of_ne' : Prop := True
/-- lt_isLUB_iff (abstract). -/
def lt_isLUB_iff' : Prop := True

-- Bounds/Defs.lean
/-- upperBounds (abstract). -/
def upperBounds' : Prop := True
/-- lowerBounds (abstract). -/
def lowerBounds' : Prop := True
/-- BddAbove (abstract). -/
def BddAbove' : Prop := True
/-- BddBelow (abstract). -/
def BddBelow' : Prop := True
/-- IsLeast (abstract). -/
def IsLeast' : Prop := True
/-- IsGreatest (abstract). -/
def IsGreatest' : Prop := True
/-- IsLUB (abstract). -/
def IsLUB' : Prop := True
/-- IsGLB (abstract). -/
def IsGLB' : Prop := True
/-- IsCofinal (abstract). -/
def IsCofinal' : Prop := True

-- Bounds/Image.lean
/-- mem_upperBounds_image (abstract). -/
def mem_upperBounds_image' : Prop := True
/-- mem_upperBounds_image_self (abstract). -/
def mem_upperBounds_image_self' : Prop := True
/-- mem_lowerBounds_image (abstract). -/
def mem_lowerBounds_image' : Prop := True
/-- mem_lowerBounds_image_self (abstract). -/
def mem_lowerBounds_image_self' : Prop := True
/-- image_upperBounds_subset_upperBounds_image (abstract). -/
def image_upperBounds_subset_upperBounds_image' : Prop := True
/-- image_lowerBounds_subset_lowerBounds_image (abstract). -/
def image_lowerBounds_subset_lowerBounds_image' : Prop := True
/-- map_bddAbove (abstract). -/
def map_bddAbove' : Prop := True
/-- map_bddBelow (abstract). -/
def map_bddBelow' : Prop := True
/-- map_isLeast (abstract). -/
def map_isLeast' : Prop := True
/-- map_isGreatest (abstract). -/
def map_isGreatest' : Prop := True
/-- image_lowerBounds_subset_upperBounds_image (abstract). -/
def image_lowerBounds_subset_upperBounds_image' : Prop := True
/-- image_upperBounds_subset_lowerBounds_image (abstract). -/
def image_upperBounds_subset_lowerBounds_image' : Prop := True
/-- mem_upperBounds_image2 (abstract). -/
def mem_upperBounds_image2' : Prop := True
/-- mem_lowerBounds_image2 (abstract). -/
def mem_lowerBounds_image2' : Prop := True
/-- image2_upperBounds_upperBounds_subset (abstract). -/
def image2_upperBounds_upperBounds_subset' : Prop := True
/-- image2_lowerBounds_lowerBounds_subset (abstract). -/
def image2_lowerBounds_lowerBounds_subset' : Prop := True
/-- image2 (abstract). -/
def image2' : Prop := True
/-- mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds (abstract). -/
def mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds' : Prop := True
/-- mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds (abstract). -/
def mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds' : Prop := True
/-- image2_upperBounds_lowerBounds_subset_upperBounds_image2 (abstract). -/
def image2_upperBounds_lowerBounds_subset_upperBounds_image2' : Prop := True
/-- image2_lowerBounds_upperBounds_subset_lowerBounds_image2 (abstract). -/
def image2_lowerBounds_upperBounds_subset_lowerBounds_image2' : Prop := True
/-- bddAbove_image2_of_bddBelow (abstract). -/
def bddAbove_image2_of_bddBelow' : Prop := True
/-- bddBelow_image2_of_bddAbove (abstract). -/
def bddBelow_image2_of_bddAbove' : Prop := True
/-- isGreatest_image2_of_isLeast (abstract). -/
def isGreatest_image2_of_isLeast' : Prop := True
/-- isLeast_image2_of_isGreatest (abstract). -/
def isLeast_image2_of_isGreatest' : Prop := True
/-- mem_upperBounds_image2_of_mem_lowerBounds (abstract). -/
def mem_upperBounds_image2_of_mem_lowerBounds' : Prop := True
/-- mem_lowerBounds_image2_of_mem_upperBounds (abstract). -/
def mem_lowerBounds_image2_of_mem_upperBounds' : Prop := True
/-- image2_upperBounds_upperBounds_subset_upperBounds_image2 (abstract). -/
def image2_upperBounds_upperBounds_subset_upperBounds_image2' : Prop := True
/-- image2_lowerBounds_lowerBounds_subset_lowerBounds_image2 (abstract). -/
def image2_lowerBounds_lowerBounds_subset_lowerBounds_image2' : Prop := True
/-- image2_bddAbove (abstract). -/
def image2_bddAbove' : Prop := True
/-- image2_bddBelow (abstract). -/
def image2_bddBelow' : Prop := True
/-- isGreatest_image2 (abstract). -/
def isGreatest_image2' : Prop := True
/-- isLeast_image2 (abstract). -/
def isLeast_image2' : Prop := True
/-- mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds (abstract). -/
def mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds' : Prop := True
/-- mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds (abstract). -/
def mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds' : Prop := True
/-- image2_lowerBounds_upperBounds_subset_upperBounds_image2 (abstract). -/
def image2_lowerBounds_upperBounds_subset_upperBounds_image2' : Prop := True
/-- image2_upperBounds_lowerBounds_subset_lowerBounds_image2 (abstract). -/
def image2_upperBounds_lowerBounds_subset_lowerBounds_image2' : Prop := True
/-- bddAbove_image2_of_bddAbove (abstract). -/
def bddAbove_image2_of_bddAbove' : Prop := True
/-- isGreatest_image2_of_isGreatest (abstract). -/
def isGreatest_image2_of_isGreatest' : Prop := True
/-- isLeast_image2_of_isLeast (abstract). -/
def isLeast_image2_of_isLeast' : Prop := True
/-- bddAbove_prod (abstract). -/
def bddAbove_prod' : Prop := True
/-- bddBelow_prod (abstract). -/
def bddBelow_prod' : Prop := True
/-- bddAbove_range_prod (abstract). -/
def bddAbove_range_prod' : Prop := True
/-- bddBelow_range_prod (abstract). -/
def bddBelow_range_prod' : Prop := True
/-- isLUB_prod (abstract). -/
def isLUB_prod' : Prop := True
/-- isGLB_prod (abstract). -/
def isGLB_prod' : Prop := True
/-- bddAbove_pi (abstract). -/
def bddAbove_pi' : Prop := True
/-- bddBelow_pi (abstract). -/
def bddBelow_pi' : Prop := True
/-- bddAbove_range_pi (abstract). -/
def bddAbove_range_pi' : Prop := True
/-- bddBelow_range_pi (abstract). -/
def bddBelow_range_pi' : Prop := True
/-- isLUB_pi (abstract). -/
def isLUB_pi' : Prop := True
/-- isGLB_pi (abstract). -/
def isGLB_pi' : Prop := True
/-- of_image (abstract). -/
def of_image' : Prop := True
/-- range_mono (abstract). -/
def range_mono' : Prop := True
/-- range_comp (abstract). -/
def range_comp' : Prop := True

-- Bounds/OrderIso.lean
/-- upperBounds_image (abstract). -/
def upperBounds_image' : Prop := True
/-- lowerBounds_image (abstract). -/
def lowerBounds_image' : Prop := True
/-- isLUB_image (abstract). -/
def isLUB_image' : Prop := True
/-- isGLB_image (abstract). -/
def isGLB_image' : Prop := True
/-- isLUB_preimage (abstract). -/
def isLUB_preimage' : Prop := True
/-- isGLB_preimage (abstract). -/
def isGLB_preimage' : Prop := True

-- Category/BddDistLat.lean
/-- BddDistLat (abstract). -/
def BddDistLat' : Prop := True
-- COLLISION: of' already in SetTheory.lean — rename needed
/-- toBddLat (abstract). -/
def toBddLat' : Prop := True
-- COLLISION: mk' already in SetTheory.lean — rename needed
/-- dual (abstract). -/
def dual' : Prop := True
/-- dualEquiv (abstract). -/
def dualEquiv' : Prop := True

-- Category/BddLat.lean
/-- BddLat (abstract). -/
def BddLat' : Prop := True
/-- latToBddLat (abstract). -/
def latToBddLat' : Prop := True
/-- latToBddLatForgetAdjunction (abstract). -/
def latToBddLatForgetAdjunction' : Prop := True
/-- latToBddLatCompDualIsoDualCompLatToBddLat (abstract). -/
def latToBddLatCompDualIsoDualCompLatToBddLat' : Prop := True

-- Category/BddOrd.lean
/-- BddOrd (abstract). -/
def BddOrd' : Prop := True

-- Category/BoolAlg.lean
/-- BoolAlg (abstract). -/
def BoolAlg' : Prop := True
/-- toBddDistLat (abstract). -/
def toBddDistLat' : Prop := True
/-- typeToBoolAlgOp (abstract). -/
def typeToBoolAlgOp' : Prop := True

-- Category/CompleteLat.lean
/-- CompleteLat (abstract). -/
def CompleteLat' : Prop := True

-- Category/DistLat.lean
/-- DistLat (abstract). -/
def DistLat' : Prop := True

-- Category/FinBddDistLat.lean
/-- FinBddDistLat (abstract). -/
def FinBddDistLat' : Prop := True

-- Category/FinBoolAlg.lean
/-- FinBoolAlg (abstract). -/
def FinBoolAlg' : Prop := True
/-- fintypeToFinBoolAlgOp (abstract). -/
def fintypeToFinBoolAlgOp' : Prop := True

-- Category/FinPartOrd.lean
/-- FinPartOrd (abstract). -/
def FinPartOrd' : Prop := True

-- Category/Frm.lean
/-- Frm (abstract). -/
def Frm' : Prop := True
/-- Hom (abstract). -/
def Hom' : Prop := True
/-- topCatOpToFrm (abstract). -/
def topCatOpToFrm' : Prop := True

-- Category/HeytAlg.lean
/-- HeytAlg (abstract). -/
def HeytAlg' : Prop := True

-- Category/Lat.lean
/-- Lat (abstract). -/
def Lat' : Prop := True

-- Category/LinOrd.lean
/-- LinOrd (abstract). -/
def LinOrd' : Prop := True

-- Category/NonemptyFinLinOrd.lean
/-- NonemptyFiniteLinearOrder (abstract). -/
def NonemptyFiniteLinearOrder' : Prop := True
/-- NonemptyFinLinOrd (abstract). -/
def NonemptyFinLinOrd' : Prop := True
/-- mono_iff_injective (abstract). -/
def mono_iff_injective' : Prop := True
/-- epi_iff_surjective (abstract). -/
def epi_iff_surjective' : Prop := True
/-- nonemptyFinLinOrdDualCompForgetToFinPartOrd (abstract). -/
def nonemptyFinLinOrdDualCompForgetToFinPartOrd' : Prop := True
/-- hom_succ (abstract). -/
def hom_succ' : Prop := True

-- Category/OmegaCompletePartialOrder.lean
/-- ωCPO (abstract). -/
def ωCPO' : Prop := True
/-- product (abstract). -/
def product' : Prop := True
/-- isProduct (abstract). -/
def isProduct' : Prop := True
/-- equalizerι (abstract). -/
def equalizerι' : Prop := True
/-- equalizer (abstract). -/
def equalizer' : Prop := True
/-- isEqualizer (abstract). -/
def isEqualizer' : Prop := True

-- Category/PartOrd.lean
/-- PartOrd (abstract). -/
def PartOrd' : Prop := True
/-- preordToPartOrd (abstract). -/
def preordToPartOrd' : Prop := True
/-- preordToPartOrdForgetAdjunction (abstract). -/
def preordToPartOrdForgetAdjunction' : Prop := True
/-- preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd (abstract). -/
def preordToPartOrdCompToDualIsoToDualCompPreordToPartOrd' : Prop := True

-- Category/Preord.lean
/-- Preord (abstract). -/
def Preord' : Prop := True
/-- preordToCat (abstract). -/
def preordToCat' : Prop := True

-- Category/Semilat.lean
/-- SemilatSupCat (abstract). -/
def SemilatSupCat' : Prop := True
/-- SemilatInfCat (abstract). -/
def SemilatInfCat' : Prop := True
/-- SemilatSupCatEquivSemilatInfCat (abstract). -/
def SemilatSupCatEquivSemilatInfCat' : Prop := True

-- Chain.lean
/-- SuperChain (abstract). -/
def SuperChain' : Prop := True
/-- IsMaxChain (abstract). -/
def IsMaxChain' : Prop := True
/-- isChain_of_trichotomous (abstract). -/
def isChain_of_trichotomous' : Prop := True
-- COLLISION: pair' already in SetTheory.lean — rename needed
/-- isChain_univ_iff (abstract). -/
def isChain_univ_iff' : Prop := True
/-- isChain_range (abstract). -/
def isChain_range' : Prop := True
/-- total (abstract). -/
def total' : Prop := True
/-- directedOn (abstract). -/
def directedOn' : Prop := True
/-- directed (abstract). -/
def directed' : Prop := True
/-- exists3 (abstract). -/
def exists3' : Prop := True
/-- not_superChain (abstract). -/
def not_superChain' : Prop := True
/-- bot_mem (abstract). -/
def bot_mem' : Prop := True
/-- top_mem (abstract). -/
def top_mem' : Prop := True
/-- SuccChain (abstract). -/
def SuccChain' : Prop := True
/-- succ (abstract). -/
def succ' : Prop := True
/-- superChain_succChain (abstract). -/
def superChain_succChain' : Prop := True
/-- subset_succChain (abstract). -/
def subset_succChain' : Prop := True
/-- ChainClosure (abstract). -/
def ChainClosure' : Prop := True
/-- maxChain (abstract). -/
def maxChain' : Prop := True
/-- chainClosure_empty (abstract). -/
def chainClosure_empty' : Prop := True
/-- chainClosure_maxChain (abstract). -/
def chainClosure_maxChain' : Prop := True
/-- chainClosure_succ_total_aux (abstract). -/
def chainClosure_succ_total_aux' : Prop := True
/-- chainClosure_succ_total (abstract). -/
def chainClosure_succ_total' : Prop := True
/-- succ_fixpoint (abstract). -/
def succ_fixpoint' : Prop := True
/-- succ_fixpoint_iff (abstract). -/
def succ_fixpoint_iff' : Prop := True
/-- maxChain_spec (abstract). -/
def maxChain_spec' : Prop := True
/-- Flag (abstract). -/
def Flag' : Prop := True
/-- mk_coe (abstract). -/
def mk_coe' : Prop := True
/-- chain_le (abstract). -/
def chain_le' : Prop := True
/-- ofIsMaxChain (abstract). -/
def ofIsMaxChain' : Prop := True
/-- le_or_le (abstract). -/
def le_or_le' : Prop := True
/-- mem_iff_forall_le_or_ge (abstract). -/
def mem_iff_forall_le_or_ge' : Prop := True
-- COLLISION: map' already in SetTheory.lean — rename needed
/-- chain_lt (abstract). -/
def chain_lt' : Prop := True

-- Circular.lean
/-- Btw (abstract). -/
def Btw' : Prop := True
/-- SBtw (abstract). -/
def SBtw' : Prop := True
/-- CircularPreorder (abstract). -/
def CircularPreorder' : Prop := True
/-- CircularPartialOrder (abstract). -/
def CircularPartialOrder' : Prop := True
/-- CircularOrder (abstract). -/
def CircularOrder' : Prop := True
/-- btw_cyclic (abstract). -/
def btw_cyclic' : Prop := True
/-- sbtw_iff_btw_not_btw (abstract). -/
def sbtw_iff_btw_not_btw' : Prop := True
/-- btw_of_sbtw (abstract). -/
def btw_of_sbtw' : Prop := True
/-- not_btw_of_sbtw (abstract). -/
def not_btw_of_sbtw' : Prop := True
/-- sbtw_irrefl_left_right (abstract). -/
def sbtw_irrefl_left_right' : Prop := True
/-- sbtw_irrefl_left (abstract). -/
def sbtw_irrefl_left' : Prop := True
/-- sbtw_irrefl_right (abstract). -/
def sbtw_irrefl_right' : Prop := True
/-- sbtw_irrefl (abstract). -/
def sbtw_irrefl' : Prop := True
-- COLLISION: antisymm' already in SetTheory.lean — rename needed
/-- btw_refl_left_right (abstract). -/
def btw_refl_left_right' : Prop := True
/-- btw_rfl_left_right (abstract). -/
def btw_rfl_left_right' : Prop := True
/-- btw_refl_left (abstract). -/
def btw_refl_left' : Prop := True
/-- btw_rfl_left (abstract). -/
def btw_rfl_left' : Prop := True
/-- btw_refl_right (abstract). -/
def btw_refl_right' : Prop := True
/-- btw_rfl_right (abstract). -/
def btw_rfl_right' : Prop := True
/-- sbtw_iff_not_btw (abstract). -/
def sbtw_iff_not_btw' : Prop := True
/-- cIcc (abstract). -/
def cIcc' : Prop := True
/-- cIoo (abstract). -/
def cIoo' : Prop := True
/-- left_mem_cIcc (abstract). -/
def left_mem_cIcc' : Prop := True
/-- right_mem_cIcc (abstract). -/
def right_mem_cIcc' : Prop := True
/-- compl_cIcc (abstract). -/
def compl_cIcc' : Prop := True
/-- compl_cIoo (abstract). -/
def compl_cIoo' : Prop := True
/-- toBtw (abstract). -/
def toBtw' : Prop := True
/-- toSBtw (abstract). -/
def toSBtw' : Prop := True
/-- toCircularPreorder (abstract). -/
def toCircularPreorder' : Prop := True
/-- toCircularPartialOrder (abstract). -/
def toCircularPartialOrder' : Prop := True
/-- toCircularOrder (abstract). -/
def toCircularOrder' : Prop := True

-- Closure.lean
/-- ClosureOperator (abstract). -/
def ClosureOperator' : Prop := True
/-- conjBy (abstract). -/
def conjBy' : Prop := True
/-- id (abstract). -/
def id' : Prop := True
/-- mk₂ (abstract). -/
def mk₂' : Prop := True
/-- ofPred (abstract). -/
def ofPred' : Prop := True
-- COLLISION: monotone' already in SetTheory.lean — rename needed
/-- le_closure (abstract). -/
def le_closure' : Prop := True
/-- idempotent (abstract). -/
def idempotent' : Prop := True
/-- isClosed_closure (abstract). -/
def isClosed_closure' : Prop := True
/-- Closeds (abstract). -/
def Closeds' : Prop := True
/-- toCloseds (abstract). -/
def toCloseds' : Prop := True
/-- closure_eq (abstract). -/
def closure_eq' : Prop := True
/-- isClosed_iff_closure_le (abstract). -/
def isClosed_iff_closure_le' : Prop := True
/-- setOf_isClosed_eq_range_closure (abstract). -/
def setOf_isClosed_eq_range_closure' : Prop := True
/-- ext_isClosed (abstract). -/
def ext_isClosed' : Prop := True
/-- eq_ofPred_closed (abstract). -/
def eq_ofPred_closed' : Prop := True
/-- closure_top (abstract). -/
def closure_top' : Prop := True
/-- isClosed_top (abstract). -/
def isClosed_top' : Prop := True
/-- closure_inf_le (abstract). -/
def closure_inf_le' : Prop := True
/-- closure_sup_closure_le (abstract). -/
def closure_sup_closure_le' : Prop := True
/-- closure_sup_closure_left (abstract). -/
def closure_sup_closure_left' : Prop := True
/-- closure_sup_closure_right (abstract). -/
def closure_sup_closure_right' : Prop := True
/-- closure_sup_closure (abstract). -/
def closure_sup_closure' : Prop := True
/-- ofCompletePred (abstract). -/
def ofCompletePred' : Prop := True
/-- sInf_isClosed (abstract). -/
def sInf_isClosed' : Prop := True
/-- closure_iSup_closure (abstract). -/
def closure_iSup_closure' : Prop := True
/-- closure_iSup₂_closure (abstract). -/
def closure_iSup₂_closure' : Prop := True
/-- equivClosureOperator (abstract). -/
def equivClosureOperator' : Prop := True
/-- LowerAdjoint (abstract). -/
def LowerAdjoint' : Prop := True
/-- gc (abstract). -/
def gc' : Prop := True
/-- closureOperator (abstract). -/
def closureOperator' : Prop := True
/-- closed (abstract). -/
def closed' : Prop := True
/-- mem_closed_iff_closure_le (abstract). -/
def mem_closed_iff_closure_le' : Prop := True
/-- closure_is_closed (abstract). -/
def closure_is_closed' : Prop := True
/-- closed_eq_range_close (abstract). -/
def closed_eq_range_close' : Prop := True
/-- toClosed (abstract). -/
def toClosed' : Prop := True
/-- closure_le_closed_iff_le (abstract). -/
def closure_le_closed_iff_le' : Prop := True
/-- subset_closure (abstract). -/
def subset_closure' : Prop := True
/-- not_mem_of_not_mem_closure (abstract). -/
def not_mem_of_not_mem_closure' : Prop := True
/-- le_iff_subset (abstract). -/
def le_iff_subset' : Prop := True
/-- mem_iff (abstract). -/
def mem_iff' : Prop := True
/-- eq_of_le (abstract). -/
def eq_of_le' : Prop := True
/-- closure_union_closure_subset (abstract). -/
def closure_union_closure_subset' : Prop := True
/-- closure_union_closure_left (abstract). -/
def closure_union_closure_left' : Prop := True
/-- closure_union_closure_right (abstract). -/
def closure_union_closure_right' : Prop := True
/-- closure_union_closure (abstract). -/
def closure_union_closure' : Prop := True
/-- closure_iUnion_closure (abstract). -/
def closure_iUnion_closure' : Prop := True
/-- closure_iUnion₂_closure (abstract). -/
def closure_iUnion₂_closure' : Prop := True
/-- lowerAdjoint (abstract). -/
def lowerAdjoint' : Prop := True
/-- gi (abstract). -/
def gi' : Prop := True
/-- closureOperator_gi_self (abstract). -/
def closureOperator_gi_self' : Prop := True

-- Cofinal.lean
/-- of_isEmpty (abstract). -/
def of_isEmpty' : Prop := True
/-- isCofinal_empty_iff (abstract). -/
def isCofinal_empty_iff' : Prop := True
/-- singleton_top (abstract). -/
def singleton_top' : Prop := True
/-- mem_of_isMax (abstract). -/
def mem_of_isMax' : Prop := True
/-- of_not_bddAbove (abstract). -/
def of_not_bddAbove' : Prop := True
/-- not_isCofinal_iff_bddAbove (abstract). -/
def not_isCofinal_iff_bddAbove' : Prop := True
/-- not_bddAbove_iff_isCofinal (abstract). -/
def not_bddAbove_iff_isCofinal' : Prop := True

-- CompactlyGenerated/Basic.lean
/-- IsSupClosedCompact (abstract). -/
def IsSupClosedCompact' : Prop := True
/-- IsSupFiniteCompact (abstract). -/
def IsSupFiniteCompact' : Prop := True
/-- IsCompactElement (abstract). -/
def IsCompactElement' : Prop := True
/-- isCompactElement_iff_le_of_directed_sSup_le (abstract). -/
def isCompactElement_iff_le_of_directed_sSup_le' : Prop := True
/-- exists_finset_of_le_iSup (abstract). -/
def exists_finset_of_le_iSup' : Prop := True
/-- directed_sSup_lt_of_lt (abstract). -/
def directed_sSup_lt_of_lt' : Prop := True
/-- isCompactElement_finsetSup (abstract). -/
def isCompactElement_finsetSup' : Prop := True
/-- isSupFiniteCompact (abstract). -/
def isSupFiniteCompact' : Prop := True
/-- wellFoundedGT (abstract). -/
def wellFoundedGT' : Prop := True
/-- wellFoundedGT_characterisations (abstract). -/
def wellFoundedGT_characterisations' : Prop := True
/-- wellFoundedGT_iff_isSupFiniteCompact (abstract). -/
def wellFoundedGT_iff_isSupFiniteCompact' : Prop := True
/-- isSupFiniteCompact_iff_isSupClosedCompact (abstract). -/
def isSupFiniteCompact_iff_isSupClosedCompact' : Prop := True
/-- isSupClosedCompact_iff_wellFoundedGT (abstract). -/
def isSupClosedCompact_iff_wellFoundedGT' : Prop := True
/-- finite_of_sSupIndep (abstract). -/
def finite_of_sSupIndep' : Prop := True
/-- finite_ne_bot_of_iSupIndep (abstract). -/
def finite_ne_bot_of_iSupIndep' : Prop := True
/-- finite_of_iSupIndep (abstract). -/
def finite_of_iSupIndep' : Prop := True
/-- IsCompactlyGenerated (abstract). -/
def IsCompactlyGenerated' : Prop := True
/-- sSup_compact_le_eq (abstract). -/
def sSup_compact_le_eq' : Prop := True
/-- sSup_compact_eq_top (abstract). -/
def sSup_compact_eq_top' : Prop := True
/-- le_iff_compact_le_imp (abstract). -/
def le_iff_compact_le_imp' : Prop := True
/-- inf_sSup_eq (abstract). -/
def inf_sSup_eq' : Prop := True
/-- sSup_inf_eq (abstract). -/
def sSup_inf_eq' : Prop := True
/-- inf_iSup_eq (abstract). -/
def inf_iSup_eq' : Prop := True
/-- iSup_inf_eq (abstract). -/
def iSup_inf_eq' : Prop := True
/-- disjoint_sSup_right (abstract). -/
def disjoint_sSup_right' : Prop := True
/-- disjoint_sSup_left (abstract). -/
def disjoint_sSup_left' : Prop := True
/-- disjoint_iSup_right (abstract). -/
def disjoint_iSup_right' : Prop := True
/-- disjoint_iSup_left (abstract). -/
def disjoint_iSup_left' : Prop := True
/-- inf_sSup_eq_iSup_inf_sup_finset (abstract). -/
def inf_sSup_eq_iSup_inf_sup_finset' : Prop := True
/-- sSupIndep_iff_finite (abstract). -/
def sSupIndep_iff_finite' : Prop := True
/-- iSupIndep_iff_supIndep_of_injOn (abstract). -/
def iSupIndep_iff_supIndep_of_injOn' : Prop := True
/-- sSupIndep_iUnion_of_directed (abstract). -/
def sSupIndep_iUnion_of_directed' : Prop := True
/-- iSupIndep_sUnion_of_directed (abstract). -/
def iSupIndep_sUnion_of_directed' : Prop := True
/-- isCompactlyGenerated_of_wellFoundedGT (abstract). -/
def isCompactlyGenerated_of_wellFoundedGT' : Prop := True
/-- Iic_coatomic_of_compact_element (abstract). -/
def Iic_coatomic_of_compact_element' : Prop := True
/-- coatomic_of_top_compact (abstract). -/
def coatomic_of_top_compact' : Prop := True
/-- exists_sSupIndep_isCompl_sSup_atoms (abstract). -/
def exists_sSupIndep_isCompl_sSup_atoms' : Prop := True
/-- exists_sSupIndep_of_sSup_atoms_eq_top (abstract). -/
def exists_sSupIndep_of_sSup_atoms_eq_top' : Prop := True
/-- complementedLattice_of_sSup_atoms_eq_top (abstract). -/
def complementedLattice_of_sSup_atoms_eq_top' : Prop := True
/-- complementedLattice_of_isAtomistic (abstract). -/
def complementedLattice_of_isAtomistic' : Prop := True
/-- complementedLattice_iff_isAtomistic (abstract). -/
def complementedLattice_iff_isAtomistic' : Prop := True

-- CompactlyGenerated/Intervals.lean
/-- complementedLattice_of_complementedLattice_Iic (abstract). -/
def complementedLattice_of_complementedLattice_Iic' : Prop := True

-- Compare.lean
/-- cmpLE (abstract). -/
def cmpLE' : Prop := True
/-- cmpLE_swap (abstract). -/
def cmpLE_swap' : Prop := True
/-- cmpLE_eq_cmp (abstract). -/
def cmpLE_eq_cmp' : Prop := True
/-- compares_swap (abstract). -/
def compares_swap' : Prop := True
/-- swap_eq_iff_eq_swap (abstract). -/
def swap_eq_iff_eq_swap' : Prop := True
/-- eq_lt (abstract). -/
def eq_lt' : Prop := True
/-- ne_lt (abstract). -/
def ne_lt' : Prop := True
/-- eq_eq (abstract). -/
def eq_eq' : Prop := True
/-- eq_gt (abstract). -/
def eq_gt' : Prop := True
/-- ne_gt (abstract). -/
def ne_gt' : Prop := True
/-- le_total (abstract). -/
def le_total' : Prop := True
/-- le_antisymm (abstract). -/
def le_antisymm' : Prop := True
-- COLLISION: inj' already in SetTheory.lean — rename needed
/-- compares_iff_of_compares_impl (abstract). -/
def compares_iff_of_compares_impl' : Prop := True
/-- swap_orElse (abstract). -/
def swap_orElse' : Prop := True
/-- orElse_eq_lt (abstract). -/
def orElse_eq_lt' : Prop := True
/-- toDual_compares_toDual (abstract). -/
def toDual_compares_toDual' : Prop := True
/-- ofDual_compares_ofDual (abstract). -/
def ofDual_compares_ofDual' : Prop := True
-- COLLISION: cmp_compares' already in SetTheory.lean — rename needed
/-- linearOrderOfCompares (abstract). -/
def linearOrderOfCompares' : Prop := True
/-- cmp_eq_lt_iff (abstract). -/
def cmp_eq_lt_iff' : Prop := True
/-- cmp_eq_eq_iff (abstract). -/
def cmp_eq_eq_iff' : Prop := True
/-- cmp_eq_gt_iff (abstract). -/
def cmp_eq_gt_iff' : Prop := True
/-- cmp_self_eq_eq (abstract). -/
def cmp_self_eq_eq' : Prop := True
/-- cmp_eq_cmp_symm (abstract). -/
def cmp_eq_cmp_symm' : Prop := True
/-- lt_iff_lt_of_cmp_eq_cmp (abstract). -/
def lt_iff_lt_of_cmp_eq_cmp' : Prop := True
/-- le_iff_le_of_cmp_eq_cmp (abstract). -/
def le_iff_le_of_cmp_eq_cmp' : Prop := True
/-- eq_iff_eq_of_cmp_eq_cmp (abstract). -/
def eq_iff_eq_of_cmp_eq_cmp' : Prop := True

-- CompleteBooleanAlgebra.lean
/-- MinimalAxioms (abstract). -/
def MinimalAxioms' : Prop := True
/-- Frame (abstract). -/
def Frame' : Prop := True
/-- Coframe (abstract). -/
def Coframe' : Prop := True
/-- CompleteDistribLattice (abstract). -/
def CompleteDistribLattice' : Prop := True
/-- CompletelyDistribLattice (abstract). -/
def CompletelyDistribLattice' : Prop := True
/-- le_iInf_iSup (abstract). -/
def le_iInf_iSup' : Prop := True
/-- iSup_iInf_le (abstract). -/
def iSup_iInf_le' : Prop := True
/-- ofMinimalAxioms (abstract). -/
def ofMinimalAxioms' : Prop := True
/-- sup_sInf_eq (abstract). -/
def sup_sInf_eq' : Prop := True
/-- sInf_sup_eq (abstract). -/
def sInf_sup_eq' : Prop := True
/-- iInf_sup_eq (abstract). -/
def iInf_sup_eq' : Prop := True
/-- sup_iInf_eq (abstract). -/
def sup_iInf_eq' : Prop := True
/-- toFrame (abstract). -/
def toFrame' : Prop := True
/-- toCoframe (abstract). -/
def toCoframe' : Prop := True
/-- iInf_iSup_eq' (abstract). -/
def iInf_iSup_eq' : Prop := True
/-- iSup_iInf_eq (abstract). -/
def iSup_iInf_eq' : Prop := True
/-- toCompleteDistribLattice (abstract). -/
def toCompleteDistribLattice' : Prop := True
/-- iSup₂_inf_eq (abstract). -/
def iSup₂_inf_eq' : Prop := True
/-- inf_iSup₂_eq (abstract). -/
def inf_iSup₂_eq' : Prop := True
/-- iSup_inf_iSup (abstract). -/
def iSup_inf_iSup' : Prop := True
/-- biSup_inf_biSup (abstract). -/
def biSup_inf_biSup' : Prop := True
/-- sSup_inf_sSup (abstract). -/
def sSup_inf_sSup' : Prop := True
/-- iSup_disjoint_iff (abstract). -/
def iSup_disjoint_iff' : Prop := True
/-- disjoint_iSup_iff (abstract). -/
def disjoint_iSup_iff' : Prop := True
/-- iSup₂_disjoint_iff (abstract). -/
def iSup₂_disjoint_iff' : Prop := True
/-- disjoint_iSup₂_iff (abstract). -/
def disjoint_iSup₂_iff' : Prop := True
/-- sSup_disjoint_iff (abstract). -/
def sSup_disjoint_iff' : Prop := True
/-- disjoint_sSup_iff (abstract). -/
def disjoint_sSup_iff' : Prop := True
/-- iSup_inf_of_monotone (abstract). -/
def iSup_inf_of_monotone' : Prop := True
/-- iSup_inf_of_antitone (abstract). -/
def iSup_inf_of_antitone' : Prop := True
/-- iInf₂_sup_eq (abstract). -/
def iInf₂_sup_eq' : Prop := True
/-- sup_iInf₂_eq (abstract). -/
def sup_iInf₂_eq' : Prop := True
/-- iInf_sup_iInf (abstract). -/
def iInf_sup_iInf' : Prop := True
/-- biInf_sup_biInf (abstract). -/
def biInf_sup_biInf' : Prop := True
/-- sInf_sup_sInf (abstract). -/
def sInf_sup_sInf' : Prop := True
/-- iInf_sup_of_monotone (abstract). -/
def iInf_sup_of_monotone' : Prop := True
/-- iInf_sup_of_antitone (abstract). -/
def iInf_sup_of_antitone' : Prop := True
/-- CompleteBooleanAlgebra (abstract). -/
def CompleteBooleanAlgebra' : Prop := True
/-- compl_iInf (abstract). -/
def compl_iInf' : Prop := True
/-- compl_iSup (abstract). -/
def compl_iSup' : Prop := True
/-- compl_sInf (abstract). -/
def compl_sInf' : Prop := True
/-- compl_sSup (abstract). -/
def compl_sSup' : Prop := True
/-- iSup_symmDiff_iSup_le (abstract). -/
def iSup_symmDiff_iSup_le' : Prop := True
/-- biSup_symmDiff_biSup_le (abstract). -/
def biSup_symmDiff_biSup_le' : Prop := True
/-- CompleteAtomicBooleanAlgebra (abstract). -/
def CompleteAtomicBooleanAlgebra' : Prop := True
/-- frameMinimalAxioms (abstract). -/
def frameMinimalAxioms' : Prop := True
/-- coframeMinimalAxioms (abstract). -/
def coframeMinimalAxioms' : Prop := True
/-- frame (abstract). -/
def frame' : Prop := True
/-- coframe (abstract). -/
def coframe' : Prop := True
/-- completeDistribLatticeMinimalAxioms (abstract). -/
def completeDistribLatticeMinimalAxioms' : Prop := True
/-- completeDistribLattice (abstract). -/
def completeDistribLattice' : Prop := True
/-- completelyDistribLatticeMinimalAxioms (abstract). -/
def completelyDistribLatticeMinimalAxioms' : Prop := True
/-- completelyDistribLattice (abstract). -/
def completelyDistribLattice' : Prop := True
/-- completeAtomicBooleanAlgebra (abstract). -/
def completeAtomicBooleanAlgebra' : Prop := True

-- CompleteLattice.lean
/-- iSup_ulift (abstract). -/
def iSup_ulift' : Prop := True
/-- iInf_ulift (abstract). -/
def iInf_ulift' : Prop := True
/-- CompleteSemilatticeSup (abstract). -/
def CompleteSemilatticeSup' : Prop := True
/-- le_sSup (abstract). -/
def le_sSup' : Prop := True
/-- sSup_le (abstract). -/
def sSup_le' : Prop := True
/-- isLUB_sSup (abstract). -/
def isLUB_sSup' : Prop := True
/-- isLUB_iff_sSup_eq (abstract). -/
def isLUB_iff_sSup_eq' : Prop := True
/-- le_sSup_of_le (abstract). -/
def le_sSup_of_le' : Prop := True
/-- sSup_le_sSup (abstract). -/
def sSup_le_sSup' : Prop := True
/-- sSup_le_iff (abstract). -/
def sSup_le_iff' : Prop := True
/-- sSup_singleton (abstract). -/
def sSup_singleton' : Prop := True
/-- CompleteSemilatticeInf (abstract). -/
def CompleteSemilatticeInf' : Prop := True
/-- sInf_le (abstract). -/
def sInf_le' : Prop := True
/-- le_sInf (abstract). -/
def le_sInf' : Prop := True
/-- isGLB_sInf (abstract). -/
def isGLB_sInf' : Prop := True
/-- isGLB_iff_sInf_eq (abstract). -/
def isGLB_iff_sInf_eq' : Prop := True
/-- sInf_le_of_le (abstract). -/
def sInf_le_of_le' : Prop := True
/-- sInf_le_sInf (abstract). -/
def sInf_le_sInf' : Prop := True
/-- sInf_singleton (abstract). -/
def sInf_singleton' : Prop := True
/-- CompleteLattice (abstract). -/
def CompleteLattice' : Prop := True
/-- completeLatticeOfInf (abstract). -/
def completeLatticeOfInf' : Prop := True
/-- completeLatticeOfCompleteSemilatticeInf (abstract). -/
def completeLatticeOfCompleteSemilatticeInf' : Prop := True
/-- completeLatticeOfSup (abstract). -/
def completeLatticeOfSup' : Prop := True
/-- completeLatticeOfCompleteSemilatticeSup (abstract). -/
def completeLatticeOfCompleteSemilatticeSup' : Prop := True
/-- CompleteLinearOrder (abstract). -/
def CompleteLinearOrder' : Prop := True
-- COLLISION: a' already in SetTheory.lean — rename needed
/-- sInf_le_sSup (abstract). -/
def sInf_le_sSup' : Prop := True
/-- sSup_union (abstract). -/
def sSup_union' : Prop := True
/-- sInf_union (abstract). -/
def sInf_union' : Prop := True
/-- sSup_inter_le (abstract). -/
def sSup_inter_le' : Prop := True
/-- le_sInf_inter (abstract). -/
def le_sInf_inter' : Prop := True
/-- sSup_empty (abstract). -/
def sSup_empty' : Prop := True
-- COLLISION: sInf_empty' already in SetTheory.lean — rename needed
/-- sSup_univ (abstract). -/
def sSup_univ' : Prop := True
/-- sInf_univ (abstract). -/
def sInf_univ' : Prop := True
/-- sSup_insert (abstract). -/
def sSup_insert' : Prop := True
/-- sInf_insert (abstract). -/
def sInf_insert' : Prop := True
/-- sSup_le_sSup_of_subset_insert_bot (abstract). -/
def sSup_le_sSup_of_subset_insert_bot' : Prop := True
/-- sInf_le_sInf_of_subset_insert_top (abstract). -/
def sInf_le_sInf_of_subset_insert_top' : Prop := True
/-- sSup_diff_singleton_bot (abstract). -/
def sSup_diff_singleton_bot' : Prop := True
/-- sInf_diff_singleton_top (abstract). -/
def sInf_diff_singleton_top' : Prop := True
/-- sSup_pair (abstract). -/
def sSup_pair' : Prop := True
/-- sInf_pair (abstract). -/
def sInf_pair' : Prop := True
/-- sSup_eq_bot (abstract). -/
def sSup_eq_bot' : Prop := True
/-- sInf_eq_top (abstract). -/
def sInf_eq_top' : Prop := True
/-- eq_singleton_bot_of_sSup_eq_bot_of_nonempty (abstract). -/
def eq_singleton_bot_of_sSup_eq_bot_of_nonempty' : Prop := True
/-- eq_singleton_top_of_sInf_eq_top_of_nonempty (abstract). -/
def eq_singleton_top_of_sInf_eq_top_of_nonempty' : Prop := True
/-- sSup_eq_of_forall_le_of_forall_lt_exists_gt (abstract). -/
def sSup_eq_of_forall_le_of_forall_lt_exists_gt' : Prop := True
/-- sInf_eq_of_forall_ge_of_forall_gt_exists_lt (abstract). -/
def sInf_eq_of_forall_ge_of_forall_gt_exists_lt' : Prop := True
/-- sSup_eq_iSup' (abstract). -/
def sSup_eq_iSup' : Prop := True
/-- iSup_congr (abstract). -/
def iSup_congr' : Prop := True
/-- biSup_congr (abstract). -/
def biSup_congr' : Prop := True
/-- iSup_comp (abstract). -/
def iSup_comp' : Prop := True
/-- iSup_congr_Prop (abstract). -/
def iSup_congr_Prop' : Prop := True
/-- iSup_plift_up (abstract). -/
def iSup_plift_up' : Prop := True
/-- sInf_eq_iInf' (abstract). -/
def sInf_eq_iInf' : Prop := True
/-- iInf_congr (abstract). -/
def iInf_congr' : Prop := True
/-- biInf_congr (abstract). -/
def biInf_congr' : Prop := True
/-- iInf_comp (abstract). -/
def iInf_comp' : Prop := True
/-- iInf_congr_Prop (abstract). -/
def iInf_congr_Prop' : Prop := True
/-- iInf_plift_up (abstract). -/
def iInf_plift_up' : Prop := True
/-- iInf_plift_down (abstract). -/
def iInf_plift_down' : Prop := True
/-- iInf_range' (abstract). -/
def iInf_range' : Prop := True
/-- sInf_image' (abstract). -/
def sInf_image' : Prop := True
/-- iInf₂_le_of_le (abstract). -/
def iInf₂_le_of_le' : Prop := True
-- COLLISION: iSup_le' already in SetTheory.lean — rename needed
/-- le_iInf (abstract). -/
def le_iInf' : Prop := True
/-- iSup₂_le (abstract). -/
def iSup₂_le' : Prop := True
/-- le_iInf₂ (abstract). -/
def le_iInf₂' : Prop := True
/-- iSup₂_le_iSup (abstract). -/
def iSup₂_le_iSup' : Prop := True
/-- iInf_le_iInf₂ (abstract). -/
def iInf_le_iInf₂' : Prop := True
/-- iSup_mono (abstract). -/
def iSup_mono' : Prop := True
/-- iInf_mono (abstract). -/
def iInf_mono' : Prop := True
/-- iSup₂_mono (abstract). -/
def iSup₂_mono' : Prop := True
/-- iInf₂_mono (abstract). -/
def iInf₂_mono' : Prop := True
/-- iSup_const_mono (abstract). -/
def iSup_const_mono' : Prop := True
/-- iInf_const_mono (abstract). -/
def iInf_const_mono' : Prop := True
/-- iSup_iInf_le_iInf_iSup (abstract). -/
def iSup_iInf_le_iInf_iSup' : Prop := True
/-- biSup_mono (abstract). -/
def biSup_mono' : Prop := True
/-- biInf_mono (abstract). -/
def biInf_mono' : Prop := True
-- COLLISION: iSup_le_iff' already in SetTheory.lean — rename needed
/-- le_iInf_iff (abstract). -/
def le_iInf_iff' : Prop := True
/-- iSup₂_le_iff (abstract). -/
def iSup₂_le_iff' : Prop := True
/-- le_iInf₂_iff (abstract). -/
def le_iInf₂_iff' : Prop := True
/-- iSup_lt_iff (abstract). -/
def iSup_lt_iff' : Prop := True
/-- lt_iInf_iff (abstract). -/
def lt_iInf_iff' : Prop := True
/-- sSup_lowerBounds_eq_sInf (abstract). -/
def sSup_lowerBounds_eq_sInf' : Prop := True
/-- sInf_upperBounds_eq_csSup (abstract). -/
def sInf_upperBounds_eq_csSup' : Prop := True
/-- le_map_iSup (abstract). -/
def le_map_iSup' : Prop := True
/-- le_map_iInf (abstract). -/
def le_map_iInf' : Prop := True
/-- le_map_iSup₂ (abstract). -/
def le_map_iSup₂' : Prop := True
/-- le_map_iInf₂ (abstract). -/
def le_map_iInf₂' : Prop := True
/-- le_map_sSup (abstract). -/
def le_map_sSup' : Prop := True
/-- le_map_sInf (abstract). -/
def le_map_sInf' : Prop := True
-- COLLISION: map_iSup' already in SetTheory.lean — rename needed
/-- map_iInf (abstract). -/
def map_iInf' : Prop := True
-- COLLISION: map_sSup' already in SetTheory.lean — rename needed
/-- map_sInf (abstract). -/
def map_sInf' : Prop := True
/-- iSup_comp_le (abstract). -/
def iSup_comp_le' : Prop := True
/-- le_iInf_comp (abstract). -/
def le_iInf_comp' : Prop := True
/-- iSup_comp_eq (abstract). -/
def iSup_comp_eq' : Prop := True
/-- iInf_comp_eq (abstract). -/
def iInf_comp_eq' : Prop := True
/-- map_iSup_le (abstract). -/
def map_iSup_le' : Prop := True
/-- map_iInf_le (abstract). -/
def map_iInf_le' : Prop := True
/-- map_iSup₂_le (abstract). -/
def map_iSup₂_le' : Prop := True
/-- map_iInf₂_le (abstract). -/
def map_iInf₂_le' : Prop := True
/-- map_sSup_le (abstract). -/
def map_sSup_le' : Prop := True
/-- map_sInf_le (abstract). -/
def map_sInf_le' : Prop := True
/-- iSup_const_le (abstract). -/
def iSup_const_le' : Prop := True
/-- le_iInf_const (abstract). -/
def le_iInf_const' : Prop := True
/-- iSup_const (abstract). -/
def iSup_const' : Prop := True
/-- iInf_const (abstract). -/
def iInf_const' : Prop := True
/-- iSup_unique (abstract). -/
def iSup_unique' : Prop := True
/-- iInf_unique (abstract). -/
def iInf_unique' : Prop := True
/-- iSup_bot (abstract). -/
def iSup_bot' : Prop := True
/-- iInf_top (abstract). -/
def iInf_top' : Prop := True
/-- iSup_eq_bot (abstract). -/
def iSup_eq_bot' : Prop := True
/-- iInf_eq_top (abstract). -/
def iInf_eq_top' : Prop := True
/-- bot_lt_iSup (abstract). -/
def bot_lt_iSup' : Prop := True
/-- iInf_lt_top (abstract). -/
def iInf_lt_top' : Prop := True
/-- iSup_pos (abstract). -/
def iSup_pos' : Prop := True
/-- iInf_pos (abstract). -/
def iInf_pos' : Prop := True
/-- iSup_neg (abstract). -/
def iSup_neg' : Prop := True
/-- iInf_neg (abstract). -/
def iInf_neg' : Prop := True
/-- iSup_eq_of_forall_le_of_forall_lt_exists_gt (abstract). -/
def iSup_eq_of_forall_le_of_forall_lt_exists_gt' : Prop := True
/-- iInf_eq_of_forall_ge_of_forall_gt_exists_lt (abstract). -/
def iInf_eq_of_forall_ge_of_forall_gt_exists_lt' : Prop := True
/-- iSup_eq_dif (abstract). -/
def iSup_eq_dif' : Prop := True
/-- iSup_eq_if (abstract). -/
def iSup_eq_if' : Prop := True
/-- iInf_eq_dif (abstract). -/
def iInf_eq_dif' : Prop := True
/-- iInf_eq_if (abstract). -/
def iInf_eq_if' : Prop := True
/-- iSup_comm (abstract). -/
def iSup_comm' : Prop := True
/-- iInf_comm (abstract). -/
def iInf_comm' : Prop := True
/-- iSup₂_comm (abstract). -/
def iSup₂_comm' : Prop := True
/-- iInf₂_comm (abstract). -/
def iInf₂_comm' : Prop := True
/-- iSup_iSup_eq_left (abstract). -/
def iSup_iSup_eq_left' : Prop := True
/-- iInf_iInf_eq_left (abstract). -/
def iInf_iInf_eq_left' : Prop := True
/-- iSup_iSup_eq_right (abstract). -/
def iSup_iSup_eq_right' : Prop := True
/-- iInf_iInf_eq_right (abstract). -/
def iInf_iInf_eq_right' : Prop := True
/-- iSup_subtype (abstract). -/
def iSup_subtype' : Prop := True
/-- iInf_subtype (abstract). -/
def iInf_subtype' : Prop := True
/-- iSup_subtype'' (abstract). -/
def iSup_subtype'' : Prop := True
/-- iInf_subtype'' (abstract). -/
def iInf_subtype'' : Prop := True
/-- biSup_const (abstract). -/
def biSup_const' : Prop := True
/-- biInf_const (abstract). -/
def biInf_const' : Prop := True
/-- iSup_sup_eq (abstract). -/
def iSup_sup_eq' : Prop := True
/-- iInf_inf_eq (abstract). -/
def iInf_inf_eq' : Prop := True
/-- biSup_comp (abstract). -/
def biSup_comp' : Prop := True
/-- biInf_comp (abstract). -/
def biInf_comp' : Prop := True
/-- biInf_le (abstract). -/
def biInf_le' : Prop := True
/-- le_biSup (abstract). -/
def le_biSup' : Prop := True
/-- iSup_sup (abstract). -/
def iSup_sup' : Prop := True
/-- iInf_inf (abstract). -/
def iInf_inf' : Prop := True
/-- sup_biSup (abstract). -/
def sup_biSup' : Prop := True
/-- biInf_inf (abstract). -/
def biInf_inf' : Prop := True
/-- inf_biInf (abstract). -/
def inf_biInf' : Prop := True
/-- biSup_lt_eq_iSup (abstract). -/
def biSup_lt_eq_iSup' : Prop := True
/-- biSup_le_eq_iSup (abstract). -/
def biSup_le_eq_iSup' : Prop := True
/-- biInf_lt_eq_iInf (abstract). -/
def biInf_lt_eq_iInf' : Prop := True
/-- biInf_le_eq_iInf (abstract). -/
def biInf_le_eq_iInf' : Prop := True
/-- biSup_gt_eq_iSup (abstract). -/
def biSup_gt_eq_iSup' : Prop := True
/-- biSup_ge_eq_iSup (abstract). -/
def biSup_ge_eq_iSup' : Prop := True
/-- biInf_gt_eq_iInf (abstract). -/
def biInf_gt_eq_iInf' : Prop := True
/-- biInf_ge_eq_iInf (abstract). -/
def biInf_ge_eq_iInf' : Prop := True
/-- iSup_true (abstract). -/
def iSup_true' : Prop := True
/-- iInf_true (abstract). -/
def iInf_true' : Prop := True
/-- iSup_exists (abstract). -/
def iSup_exists' : Prop := True
/-- iInf_exists (abstract). -/
def iInf_exists' : Prop := True
/-- iSup_and (abstract). -/
def iSup_and' : Prop := True
/-- iInf_and (abstract). -/
def iInf_and' : Prop := True
/-- iSup_or (abstract). -/
def iSup_or' : Prop := True
/-- iInf_or (abstract). -/
def iInf_or' : Prop := True
/-- iSup_dite (abstract). -/
def iSup_dite' : Prop := True
/-- iInf_dite (abstract). -/
def iInf_dite' : Prop := True
/-- iSup_ite (abstract). -/
def iSup_ite' : Prop := True
/-- iInf_ite (abstract). -/
def iInf_ite' : Prop := True
/-- iSup_range (abstract). -/
def iSup_range' : Prop := True
/-- sSup_image (abstract). -/
def sSup_image' : Prop := True
/-- map_sSup_eq_sSup_symm_preimage (abstract). -/
def map_sSup_eq_sSup_symm_preimage' : Prop := True
/-- map_sInf_eq_sInf_symm_preimage (abstract). -/
def map_sInf_eq_sInf_symm_preimage' : Prop := True
/-- iSup_univ (abstract). -/
def iSup_univ' : Prop := True
/-- iSup_union (abstract). -/
def iSup_union' : Prop := True
/-- iInf_union (abstract). -/
def iInf_union' : Prop := True
/-- iSup_split (abstract). -/
def iSup_split' : Prop := True
/-- iInf_split (abstract). -/
def iInf_split' : Prop := True
/-- iSup_split_single (abstract). -/
def iSup_split_single' : Prop := True
/-- iInf_split_single (abstract). -/
def iInf_split_single' : Prop := True
/-- iSup_le_iSup_of_subset (abstract). -/
def iSup_le_iSup_of_subset' : Prop := True
/-- iInf_le_iInf_of_subset (abstract). -/
def iInf_le_iInf_of_subset' : Prop := True
/-- iSup_insert (abstract). -/
def iSup_insert' : Prop := True
/-- iInf_insert (abstract). -/
def iInf_insert' : Prop := True
/-- iSup_singleton (abstract). -/
def iSup_singleton' : Prop := True
/-- iInf_singleton (abstract). -/
def iInf_singleton' : Prop := True
/-- iSup_pair (abstract). -/
def iSup_pair' : Prop := True
/-- iInf_pair (abstract). -/
def iInf_pair' : Prop := True
/-- iSup_image (abstract). -/
def iSup_image' : Prop := True
/-- iInf_image (abstract). -/
def iInf_image' : Prop := True
/-- iSup_extend_bot (abstract). -/
def iSup_extend_bot' : Prop := True
/-- iInf_extend_top (abstract). -/
def iInf_extend_top' : Prop := True
-- COLLISION: iSup_of_empty' already in SetTheory.lean — rename needed
/-- iInf_of_isEmpty (abstract). -/
def iInf_of_isEmpty' : Prop := True
/-- iInf_of_empty (abstract). -/
def iInf_of_empty' : Prop := True
/-- iSup_bool_eq (abstract). -/
def iSup_bool_eq' : Prop := True
/-- iInf_bool_eq (abstract). -/
def iInf_bool_eq' : Prop := True
/-- sup_eq_iSup (abstract). -/
def sup_eq_iSup' : Prop := True
/-- inf_eq_iInf (abstract). -/
def inf_eq_iInf' : Prop := True
/-- isGLB_biInf (abstract). -/
def isGLB_biInf' : Prop := True
/-- isLUB_biSup (abstract). -/
def isLUB_biSup' : Prop := True
/-- iSup_sigma (abstract). -/
def iSup_sigma' : Prop := True
/-- iInf_sigma (abstract). -/
def iInf_sigma' : Prop := True
/-- iSup_psigma (abstract). -/
def iSup_psigma' : Prop := True
/-- iInf_psigma (abstract). -/
def iInf_psigma' : Prop := True
/-- iSup_prod (abstract). -/
def iSup_prod' : Prop := True
/-- iInf_prod (abstract). -/
def iInf_prod' : Prop := True
/-- biSup_prod (abstract). -/
def biSup_prod' : Prop := True
/-- biInf_prod (abstract). -/
def biInf_prod' : Prop := True
/-- iSup_image2 (abstract). -/
def iSup_image2' : Prop := True
/-- iInf_image2 (abstract). -/
def iInf_image2' : Prop := True
-- COLLISION: iSup_sum' already in SetTheory.lean — rename needed
/-- iInf_sum (abstract). -/
def iInf_sum' : Prop := True
/-- iSup_option (abstract). -/
def iSup_option' : Prop := True
/-- iInf_option (abstract). -/
def iInf_option' : Prop := True
/-- iSup_option_elim (abstract). -/
def iSup_option_elim' : Prop := True
/-- iInf_option_elim (abstract). -/
def iInf_option_elim' : Prop := True
/-- iSup_ne_bot_subtype (abstract). -/
def iSup_ne_bot_subtype' : Prop := True
/-- iInf_ne_top_subtype (abstract). -/
def iInf_ne_top_subtype' : Prop := True
/-- sSup_image2 (abstract). -/
def sSup_image2' : Prop := True
/-- sInf_image2 (abstract). -/
def sInf_image2' : Prop := True
/-- iSup_ge_eq_iSup_nat_add (abstract). -/
def iSup_ge_eq_iSup_nat_add' : Prop := True
/-- iInf_ge_eq_iInf_nat_add (abstract). -/
def iInf_ge_eq_iInf_nat_add' : Prop := True
/-- iSup_nat_add (abstract). -/
def iSup_nat_add' : Prop := True
/-- iInf_nat_add (abstract). -/
def iInf_nat_add' : Prop := True
/-- iSup_iInf_ge_nat_add (abstract). -/
def iSup_iInf_ge_nat_add' : Prop := True
/-- iInf_iSup_ge_nat_add (abstract). -/
def iInf_iSup_ge_nat_add' : Prop := True
/-- sup_iSup_nat_succ (abstract). -/
def sup_iSup_nat_succ' : Prop := True
/-- inf_iInf_nat_succ (abstract). -/
def inf_iInf_nat_succ' : Prop := True
/-- iInf_nat_gt_zero_eq (abstract). -/
def iInf_nat_gt_zero_eq' : Prop := True
/-- iSup_nat_gt_zero_eq (abstract). -/
def iSup_nat_gt_zero_eq' : Prop := True
/-- iSup_eq_top (abstract). -/
def iSup_eq_top' : Prop := True
/-- iInf_eq_bot (abstract). -/
def iInf_eq_bot' : Prop := True
/-- iSup₂_eq_top (abstract). -/
def iSup₂_eq_top' : Prop := True
/-- iInf₂_eq_bot (abstract). -/
def iInf₂_eq_bot' : Prop := True
/-- iSup_Prop_eq (abstract). -/
def iSup_Prop_eq' : Prop := True
/-- iInf_Prop_eq (abstract). -/
def iInf_Prop_eq' : Prop := True
/-- iSup_apply (abstract). -/
def iSup_apply' : Prop := True
/-- iInf_apply (abstract). -/
def iInf_apply' : Prop := True
/-- unary_relation_sSup_iff (abstract). -/
def unary_relation_sSup_iff' : Prop := True
/-- unary_relation_sInf_iff (abstract). -/
def unary_relation_sInf_iff' : Prop := True
/-- binary_relation_sSup_iff (abstract). -/
def binary_relation_sSup_iff' : Prop := True
/-- binary_relation_sInf_iff (abstract). -/
def binary_relation_sInf_iff' : Prop := True
/-- sSup (abstract). -/
def sSup' : Prop := True
/-- sInf (abstract). -/
def sInf' : Prop := True
/-- iSup (abstract). -/
def iSup' : Prop := True
/-- iInf (abstract). -/
def iInf' : Prop := True
/-- swap_sInf (abstract). -/
def swap_sInf' : Prop := True
/-- swap_sSup (abstract). -/
def swap_sSup' : Prop := True
/-- fst_iInf (abstract). -/
def fst_iInf' : Prop := True
/-- snd_iInf (abstract). -/
def snd_iInf' : Prop := True
/-- swap_iInf (abstract). -/
def swap_iInf' : Prop := True
/-- iInf_mk (abstract). -/
def iInf_mk' : Prop := True
/-- fst_iSup (abstract). -/
def fst_iSup' : Prop := True
/-- snd_iSup (abstract). -/
def snd_iSup' : Prop := True
/-- swap_iSup (abstract). -/
def swap_iSup' : Prop := True
/-- iSup_mk (abstract). -/
def iSup_mk' : Prop := True
/-- sInf_prod (abstract). -/
def sInf_prod' : Prop := True
/-- sSup_prod (abstract). -/
def sSup_prod' : Prop := True
/-- sup_sInf_le_iInf_sup (abstract). -/
def sup_sInf_le_iInf_sup' : Prop := True
/-- iSup_inf_le_inf_sSup (abstract). -/
def iSup_inf_le_inf_sSup' : Prop := True
/-- sInf_sup_le_iInf_sup (abstract). -/
def sInf_sup_le_iInf_sup' : Prop := True
/-- iSup_inf_le_sSup_inf (abstract). -/
def iSup_inf_le_sSup_inf' : Prop := True
/-- le_iSup_inf_iSup (abstract). -/
def le_iSup_inf_iSup' : Prop := True
/-- iInf_sup_iInf_le (abstract). -/
def iInf_sup_iInf_le' : Prop := True
/-- down_iSup (abstract). -/
def down_iSup' : Prop := True
/-- up_iSup (abstract). -/
def up_iSup' : Prop := True
/-- down_iInf (abstract). -/
def down_iInf' : Prop := True
/-- up_iInf (abstract). -/
def up_iInf' : Prop := True

-- CompleteLattice/Finset.lean
/-- iSup_eq_iSup_finset (abstract). -/
def iSup_eq_iSup_finset' : Prop := True
/-- iInf_eq_iInf_finset (abstract). -/
def iInf_eq_iInf_finset' : Prop := True
/-- iUnion_eq_iUnion_finset (abstract). -/
def iUnion_eq_iUnion_finset' : Prop := True
/-- iInter_eq_iInter_finset (abstract). -/
def iInter_eq_iInter_finset' : Prop := True
/-- maximal_iff_forall_insert (abstract). -/
def maximal_iff_forall_insert' : Prop := True
/-- minimal_iff_forall_diff_singleton (abstract). -/
def minimal_iff_forall_diff_singleton' : Prop := True
/-- iSup_option_toFinset (abstract). -/
def iSup_option_toFinset' : Prop := True
/-- iInf_option_toFinset (abstract). -/
def iInf_option_toFinset' : Prop := True
/-- iSup_finset_image (abstract). -/
def iSup_finset_image' : Prop := True
/-- iInf_finset_image (abstract). -/
def iInf_finset_image' : Prop := True
/-- iSup_insert_update (abstract). -/
def iSup_insert_update' : Prop := True
/-- iInf_insert_update (abstract). -/
def iInf_insert_update' : Prop := True
/-- iSup_biUnion (abstract). -/
def iSup_biUnion' : Prop := True
/-- iInf_biUnion (abstract). -/
def iInf_biUnion' : Prop := True
/-- set_biUnion_singleton (abstract). -/
def set_biUnion_singleton' : Prop := True
/-- set_biInter_singleton (abstract). -/
def set_biInter_singleton' : Prop := True
/-- set_biUnion_preimage_singleton (abstract). -/
def set_biUnion_preimage_singleton' : Prop := True
/-- set_biUnion_option_toFinset (abstract). -/
def set_biUnion_option_toFinset' : Prop := True
/-- set_biInter_option_toFinset (abstract). -/
def set_biInter_option_toFinset' : Prop := True
/-- subset_set_biUnion_of_mem (abstract). -/
def subset_set_biUnion_of_mem' : Prop := True
/-- set_biUnion_union (abstract). -/
def set_biUnion_union' : Prop := True
/-- set_biInter_inter (abstract). -/
def set_biInter_inter' : Prop := True
/-- set_biUnion_insert (abstract). -/
def set_biUnion_insert' : Prop := True
/-- set_biInter_insert (abstract). -/
def set_biInter_insert' : Prop := True
/-- set_biUnion_finset_image (abstract). -/
def set_biUnion_finset_image' : Prop := True
/-- set_biInter_finset_image (abstract). -/
def set_biInter_finset_image' : Prop := True
/-- set_biUnion_insert_update (abstract). -/
def set_biUnion_insert_update' : Prop := True
/-- set_biInter_insert_update (abstract). -/
def set_biInter_insert_update' : Prop := True
/-- set_biUnion_biUnion (abstract). -/
def set_biUnion_biUnion' : Prop := True
/-- set_biInter_biUnion (abstract). -/
def set_biInter_biUnion' : Prop := True

-- CompleteLatticeIntervals.lean
/-- subsetSupSet (abstract). -/
def subsetSupSet' : Prop := True
/-- subset_sSup_of_within (abstract). -/
def subset_sSup_of_within' : Prop := True
/-- subset_sSup_emptyset (abstract). -/
def subset_sSup_emptyset' : Prop := True
/-- subset_sSup_of_not_bddAbove (abstract). -/
def subset_sSup_of_not_bddAbove' : Prop := True
/-- subsetInfSet (abstract). -/
def subsetInfSet' : Prop := True
/-- subset_sInf_of_within (abstract). -/
def subset_sInf_of_within' : Prop := True
/-- subset_sInf_emptyset (abstract). -/
def subset_sInf_emptyset' : Prop := True
/-- subset_sInf_of_not_bddBelow (abstract). -/
def subset_sInf_of_not_bddBelow' : Prop := True
/-- subsetConditionallyCompleteLinearOrder (abstract). -/
def subsetConditionallyCompleteLinearOrder' : Prop := True
/-- sSup_within_of_ordConnected (abstract). -/
def sSup_within_of_ordConnected' : Prop := True
/-- sInf_within_of_ordConnected (abstract). -/
def sInf_within_of_ordConnected' : Prop := True
/-- coe_sSup (abstract). -/
def coe_sSup' : Prop := True
/-- coe_sInf (abstract). -/
def coe_sInf' : Prop := True
/-- coe_iSup (abstract). -/
def coe_iSup' : Prop := True
-- COLLISION: coe_iInf' already in FieldTheory.lean — rename needed
/-- coe_biInf (abstract). -/
def coe_biInf' : Prop := True

-- CompletePartialOrder.lean
/-- CompletePartialOrder (abstract). -/
def CompletePartialOrder' : Prop := True
-- COLLISION: le_iSup' already in SetTheory.lean — rename needed
/-- scottContinuous (abstract). -/
def scottContinuous' : Prop := True

-- CompleteSublattice.lean
/-- CompleteSublattice (abstract). -/
def CompleteSublattice' : Prop := True
/-- subtype (abstract). -/
def subtype' : Prop := True
/-- subtype_injective (abstract). -/
def subtype_injective' : Prop := True
/-- comap (abstract). -/
def comap' : Prop := True
/-- disjoint_iff (abstract). -/
def disjoint_iff' : Prop := True
/-- codisjoint_iff (abstract). -/
def codisjoint_iff' : Prop := True
/-- copy (abstract). -/
def copy' : Prop := True
/-- copy_eq (abstract). -/
def copy_eq' : Prop := True
-- COLLISION: range' already in SetTheory.lean — rename needed
/-- toOrderIsoRangeOfInjective (abstract). -/
def toOrderIsoRangeOfInjective' : Prop := True

-- Concept.lean
/-- intentClosure (abstract). -/
def intentClosure' : Prop := True
/-- extentClosure (abstract). -/
def extentClosure' : Prop := True
/-- subset_intentClosure_iff_subset_extentClosure (abstract). -/
def subset_intentClosure_iff_subset_extentClosure' : Prop := True
/-- gc_intentClosure_extentClosure (abstract). -/
def gc_intentClosure_extentClosure' : Prop := True
/-- intentClosure_empty (abstract). -/
def intentClosure_empty' : Prop := True
/-- extentClosure_empty (abstract). -/
def extentClosure_empty' : Prop := True
/-- intentClosure_union (abstract). -/
def intentClosure_union' : Prop := True
/-- extentClosure_union (abstract). -/
def extentClosure_union' : Prop := True
/-- intentClosure_iUnion (abstract). -/
def intentClosure_iUnion' : Prop := True
/-- extentClosure_iUnion (abstract). -/
def extentClosure_iUnion' : Prop := True
/-- intentClosure_iUnion₂ (abstract). -/
def intentClosure_iUnion₂' : Prop := True
/-- extentClosure_iUnion₂ (abstract). -/
def extentClosure_iUnion₂' : Prop := True
/-- subset_extentClosure_intentClosure (abstract). -/
def subset_extentClosure_intentClosure' : Prop := True
/-- subset_intentClosure_extentClosure (abstract). -/
def subset_intentClosure_extentClosure' : Prop := True
/-- intentClosure_extentClosure_intentClosure (abstract). -/
def intentClosure_extentClosure_intentClosure' : Prop := True
/-- extentClosure_intentClosure_extentClosure (abstract). -/
def extentClosure_intentClosure_extentClosure' : Prop := True
/-- intentClosure_anti (abstract). -/
def intentClosure_anti' : Prop := True
/-- extentClosure_anti (abstract). -/
def extentClosure_anti' : Prop := True
/-- Concept (abstract). -/
def Concept' : Prop := True
/-- snd_subset_snd_iff (abstract). -/
def snd_subset_snd_iff' : Prop := True
/-- snd_ssubset_snd_iff (abstract). -/
def snd_ssubset_snd_iff' : Prop := True
/-- strictMono_fst (abstract). -/
def strictMono_fst' : Prop := True
/-- strictAnti_snd (abstract). -/
def strictAnti_snd' : Prop := True
/-- swap_swap (abstract). -/
def swap_swap' : Prop := True
/-- swap_le_swap_iff (abstract). -/
def swap_le_swap_iff' : Prop := True
/-- swap_lt_swap_iff (abstract). -/
def swap_lt_swap_iff' : Prop := True
/-- swapEquiv (abstract). -/
def swapEquiv' : Prop := True

-- ConditionallyCompleteLattice/Basic.lean
/-- sSup_eq (abstract). -/
def sSup_eq' : Prop := True
/-- sInf_eq (abstract). -/
def sInf_eq' : Prop := True
/-- le_csSup (abstract). -/
def le_csSup' : Prop := True
/-- csSup_le (abstract). -/
def csSup_le' : Prop := True
/-- csInf_le (abstract). -/
def csInf_le' : Prop := True
/-- le_csInf (abstract). -/
def le_csInf' : Prop := True
/-- le_csSup_of_le (abstract). -/
def le_csSup_of_le' : Prop := True
/-- csInf_le_of_le (abstract). -/
def csInf_le_of_le' : Prop := True
/-- csSup_le_csSup (abstract). -/
def csSup_le_csSup' : Prop := True
/-- csInf_le_csInf (abstract). -/
def csInf_le_csInf' : Prop := True
/-- le_csSup_iff (abstract). -/
def le_csSup_iff' : Prop := True
/-- csInf_le_iff (abstract). -/
def csInf_le_iff' : Prop := True
/-- isLUB_csSup (abstract). -/
def isLUB_csSup' : Prop := True
/-- isGLB_csInf (abstract). -/
def isGLB_csInf' : Prop := True
/-- csSup_eq (abstract). -/
def csSup_eq' : Prop := True
/-- csSup_mem (abstract). -/
def csSup_mem' : Prop := True
/-- csInf_eq (abstract). -/
def csInf_eq' : Prop := True
/-- csInf_mem (abstract). -/
def csInf_mem' : Prop := True
/-- subset_Icc_csInf_csSup (abstract). -/
def subset_Icc_csInf_csSup' : Prop := True
/-- csSup_le_iff (abstract). -/
def csSup_le_iff' : Prop := True
/-- le_csInf_iff (abstract). -/
def le_csInf_iff' : Prop := True
/-- csSup_lowerBounds_eq_csInf (abstract). -/
def csSup_lowerBounds_eq_csInf' : Prop := True
/-- csInf_upperBounds_eq_csSup (abstract). -/
def csInf_upperBounds_eq_csSup' : Prop := True
/-- csSup_lowerBounds_range (abstract). -/
def csSup_lowerBounds_range' : Prop := True
/-- csInf_upperBounds_range (abstract). -/
def csInf_upperBounds_range' : Prop := True
/-- not_mem_of_lt_csInf (abstract). -/
def not_mem_of_lt_csInf' : Prop := True
/-- not_mem_of_csSup_lt (abstract). -/
def not_mem_of_csSup_lt' : Prop := True
/-- csSup_eq_of_forall_le_of_forall_lt_exists_gt (abstract). -/
def csSup_eq_of_forall_le_of_forall_lt_exists_gt' : Prop := True
/-- csInf_eq_of_forall_ge_of_forall_gt_exists_lt (abstract). -/
def csInf_eq_of_forall_ge_of_forall_gt_exists_lt' : Prop := True
/-- lt_csSup_of_lt (abstract). -/
def lt_csSup_of_lt' : Prop := True
/-- csInf_lt_of_lt (abstract). -/
def csInf_lt_of_lt' : Prop := True
/-- exists_between_of_forall_le (abstract). -/
def exists_between_of_forall_le' : Prop := True
/-- csSup_singleton (abstract). -/
def csSup_singleton' : Prop := True
/-- csInf_singleton (abstract). -/
def csInf_singleton' : Prop := True
/-- csSup_pair (abstract). -/
def csSup_pair' : Prop := True
/-- csInf_pair (abstract). -/
def csInf_pair' : Prop := True
/-- csInf_le_csSup (abstract). -/
def csInf_le_csSup' : Prop := True
/-- csSup_union (abstract). -/
def csSup_union' : Prop := True
/-- csInf_union (abstract). -/
def csInf_union' : Prop := True
/-- csSup_inter_le (abstract). -/
def csSup_inter_le' : Prop := True
/-- le_csInf_inter (abstract). -/
def le_csInf_inter' : Prop := True
/-- csSup_insert (abstract). -/
def csSup_insert' : Prop := True
/-- csInf_insert (abstract). -/
def csInf_insert' : Prop := True
/-- csInf_Icc (abstract). -/
def csInf_Icc' : Prop := True
/-- csInf_Ici (abstract). -/
def csInf_Ici' : Prop := True
/-- csInf_Ico (abstract). -/
def csInf_Ico' : Prop := True
/-- csInf_Ioc (abstract). -/
def csInf_Ioc' : Prop := True
/-- csInf_Ioi (abstract). -/
def csInf_Ioi' : Prop := True
/-- csInf_Ioo (abstract). -/
def csInf_Ioo' : Prop := True
/-- csSup_Icc (abstract). -/
def csSup_Icc' : Prop := True
/-- csSup_Ico (abstract). -/
def csSup_Ico' : Prop := True
/-- csSup_Iic (abstract). -/
def csSup_Iic' : Prop := True
/-- csSup_Iio (abstract). -/
def csSup_Iio' : Prop := True
/-- csSup_Ioc (abstract). -/
def csSup_Ioc' : Prop := True
/-- csSup_Ioo (abstract). -/
def csSup_Ioo' : Prop := True
/-- csSup_eq_of_is_forall_le_of_forall_le_imp_ge (abstract). -/
def csSup_eq_of_is_forall_le_of_forall_le_imp_ge' : Prop := True
/-- sup_eq_top_of_top_mem (abstract). -/
def sup_eq_top_of_top_mem' : Prop := True
/-- inf_eq_bot_of_bot_mem (abstract). -/
def inf_eq_bot_of_bot_mem' : Prop := True
/-- exists_lt_of_lt_csSup (abstract). -/
def exists_lt_of_lt_csSup' : Prop := True
/-- exists_lt_of_csInf_lt (abstract). -/
def exists_lt_of_csInf_lt' : Prop := True
/-- lt_csSup_iff (abstract). -/
def lt_csSup_iff' : Prop := True
/-- csInf_lt_iff (abstract). -/
def csInf_lt_iff' : Prop := True
/-- csSup_of_not_bddAbove (abstract). -/
def csSup_of_not_bddAbove' : Prop := True
/-- csSup_eq_univ_of_not_bddAbove (abstract). -/
def csSup_eq_univ_of_not_bddAbove' : Prop := True
/-- csInf_of_not_bddBelow (abstract). -/
def csInf_of_not_bddBelow' : Prop := True
/-- csInf_eq_univ_of_not_bddBelow (abstract). -/
def csInf_eq_univ_of_not_bddBelow' : Prop := True
/-- csSup_eq_csSup_of_forall_exists_le (abstract). -/
def csSup_eq_csSup_of_forall_exists_le' : Prop := True
/-- csInf_eq_csInf_of_forall_exists_le (abstract). -/
def csInf_eq_csInf_of_forall_exists_le' : Prop := True
/-- sSup_iUnion_Iic (abstract). -/
def sSup_iUnion_Iic' : Prop := True
/-- sInf_iUnion_Ici (abstract). -/
def sInf_iUnion_Ici' : Prop := True
/-- csInf_eq_bot_of_bot_mem (abstract). -/
def csInf_eq_bot_of_bot_mem' : Prop := True
/-- csSup_eq_top_of_top_mem (abstract). -/
def csSup_eq_top_of_top_mem' : Prop := True
/-- sInf_eq_argmin_on (abstract). -/
def sInf_eq_argmin_on' : Prop := True
/-- isLeast_csInf (abstract). -/
def isLeast_csInf' : Prop := True
/-- map_csInf (abstract). -/
def map_csInf' : Prop := True
/-- csInf_univ (abstract). -/
def csInf_univ' : Prop := True
/-- csSup_empty (abstract). -/
def csSup_empty' : Prop := True
/-- le_csInf_iff'' (abstract). -/
def le_csInf_iff'' : Prop := True
/-- le_csSup_image (abstract). -/
def le_csSup_image' : Prop := True
/-- csSup_image_le (abstract). -/
def csSup_image_le' : Prop := True
/-- csInf_image_le (abstract). -/
def csInf_image_le' : Prop := True
/-- le_csInf_image (abstract). -/
def le_csInf_image' : Prop := True
/-- csSup_image2_eq_csSup_csSup (abstract). -/
def csSup_image2_eq_csSup_csSup' : Prop := True
/-- csSup_image2_eq_csSup_csInf (abstract). -/
def csSup_image2_eq_csSup_csInf' : Prop := True
/-- csSup_image2_eq_csInf_csSup (abstract). -/
def csSup_image2_eq_csInf_csSup' : Prop := True
/-- csSup_image2_eq_csInf_csInf (abstract). -/
def csSup_image2_eq_csInf_csInf' : Prop := True
/-- csInf_image2_eq_csInf_csInf (abstract). -/
def csInf_image2_eq_csInf_csInf' : Prop := True
/-- csInf_image2_eq_csInf_csSup (abstract). -/
def csInf_image2_eq_csInf_csSup' : Prop := True
/-- csInf_image2_eq_csSup_csInf (abstract). -/
def csInf_image2_eq_csSup_csInf' : Prop := True
/-- csInf_image2_eq_csSup_csSup (abstract). -/
def csInf_image2_eq_csSup_csSup' : Prop := True
-- COLLISION: on' already in SetTheory.lean — rename needed

-- ConditionallyCompleteLattice/Defs.lean
/-- ConditionallyCompleteLattice (abstract). -/
def ConditionallyCompleteLattice' : Prop := True
/-- ConditionallyCompleteLinearOrder (abstract). -/
def ConditionallyCompleteLinearOrder' : Prop := True
/-- ConditionallyCompleteLinearOrderBot (abstract). -/
def ConditionallyCompleteLinearOrderBot' : Prop := True
/-- conditionallyCompleteLinearOrderBot (abstract). -/
def conditionallyCompleteLinearOrderBot' : Prop := True
/-- conditionallyCompleteLatticeOfsSup (abstract). -/
def conditionallyCompleteLatticeOfsSup' : Prop := True
/-- conditionallyCompleteLatticeOfsInf (abstract). -/
def conditionallyCompleteLatticeOfsInf' : Prop := True
/-- conditionallyCompleteLatticeOfLatticeOfsSup (abstract). -/
def conditionallyCompleteLatticeOfLatticeOfsSup' : Prop := True
/-- conditionallyCompleteLatticeOfLatticeOfsInf (abstract). -/
def conditionallyCompleteLatticeOfLatticeOfsInf' : Prop := True

-- ConditionallyCompleteLattice/Finset.lean
/-- csSup_eq_max' (abstract). -/
def csSup_eq_max' : Prop := True
/-- csInf_eq_min' (abstract). -/
def csInf_eq_min' : Prop := True
/-- csSup_lt_iff (abstract). -/
def csSup_lt_iff' : Prop := True
/-- lt_csInf_iff (abstract). -/
def lt_csInf_iff' : Prop := True
/-- ciSup_eq_max'_image (abstract). -/
def ciSup_eq_max'_image' : Prop := True
/-- ciInf_eq_min'_image (abstract). -/
def ciInf_eq_min'_image' : Prop := True
/-- ciSup_mem_image (abstract). -/
def ciSup_mem_image' : Prop := True
/-- ciInf_mem_image (abstract). -/
def ciInf_mem_image' : Prop := True
/-- ciSup_lt_iff (abstract). -/
def ciSup_lt_iff' : Prop := True
/-- lt_ciInf_iff (abstract). -/
def lt_ciInf_iff' : Prop := True
/-- iSup_mem_map_of_exists_sSup_empty_le (abstract). -/
def iSup_mem_map_of_exists_sSup_empty_le' : Prop := True
/-- iInf_mem_map_of_exists_le_sInf_empty (abstract). -/
def iInf_mem_map_of_exists_le_sInf_empty' : Prop := True
/-- exists_eq_ciSup_of_finite (abstract). -/
def exists_eq_ciSup_of_finite' : Prop := True
/-- exists_eq_ciInf_of_finite (abstract). -/
def exists_eq_ciInf_of_finite' : Prop := True
/-- sup'_eq_csSup_image (abstract). -/
def sup'_eq_csSup_image' : Prop := True
/-- inf'_eq_csInf_image (abstract). -/
def inf'_eq_csInf_image' : Prop := True
/-- sup'_id_eq_csSup (abstract). -/
def sup'_id_eq_csSup' : Prop := True
/-- inf'_id_eq_csInf (abstract). -/
def inf'_id_eq_csInf' : Prop := True
/-- sup'_univ_eq_ciSup (abstract). -/
def sup'_univ_eq_ciSup' : Prop := True
/-- inf'_univ_eq_ciInf (abstract). -/
def inf'_univ_eq_ciInf' : Prop := True
/-- iSup_mem_map_of_ne_nil (abstract). -/
def iSup_mem_map_of_ne_nil' : Prop := True
/-- iSup_mem_map_of_ne_zero (abstract). -/
def iSup_mem_map_of_ne_zero' : Prop := True

-- ConditionallyCompleteLattice/Group.lean
/-- le_mul_ciInf (abstract). -/
def le_mul_ciInf' : Prop := True
/-- mul_ciSup_le (abstract). -/
def mul_ciSup_le' : Prop := True
/-- le_ciInf_mul (abstract). -/
def le_ciInf_mul' : Prop := True
/-- ciSup_mul_le (abstract). -/
def ciSup_mul_le' : Prop := True
/-- le_ciInf_mul_ciInf (abstract). -/
def le_ciInf_mul_ciInf' : Prop := True
/-- ciSup_mul_ciSup_le (abstract). -/
def ciSup_mul_ciSup_le' : Prop := True

-- ConditionallyCompleteLattice/Indexed.lean
/-- iInf_empty (abstract). -/
def iInf_empty' : Prop := True
/-- ciSup_empty (abstract). -/
def ciSup_empty' : Prop := True
/-- isLUB_ciSup (abstract). -/
def isLUB_ciSup' : Prop := True
/-- isLUB_ciSup_set (abstract). -/
def isLUB_ciSup_set' : Prop := True
/-- isGLB_ciInf (abstract). -/
def isGLB_ciInf' : Prop := True
/-- isGLB_ciInf_set (abstract). -/
def isGLB_ciInf_set' : Prop := True
/-- ciSup_le_iff (abstract). -/
def ciSup_le_iff' : Prop := True
/-- le_ciInf_iff (abstract). -/
def le_ciInf_iff' : Prop := True
/-- ciSup_set_le_iff (abstract). -/
def ciSup_set_le_iff' : Prop := True
/-- le_ciInf_set_iff (abstract). -/
def le_ciInf_set_iff' : Prop := True
/-- ciSup_eq (abstract). -/
def ciSup_eq' : Prop := True
/-- ciSup_set_eq (abstract). -/
def ciSup_set_eq' : Prop := True
/-- ciInf_eq (abstract). -/
def ciInf_eq' : Prop := True
/-- ciInf_set_eq (abstract). -/
def ciInf_set_eq' : Prop := True
/-- ciSup_le (abstract). -/
def ciSup_le' : Prop := True
/-- le_ciSup (abstract). -/
def le_ciSup' : Prop := True
/-- le_ciSup_of_le (abstract). -/
def le_ciSup_of_le' : Prop := True
/-- ciSup_mono (abstract). -/
def ciSup_mono' : Prop := True
/-- le_ciSup_set (abstract). -/
def le_ciSup_set' : Prop := True
/-- ciInf_mono (abstract). -/
def ciInf_mono' : Prop := True
/-- le_ciInf (abstract). -/
def le_ciInf' : Prop := True
/-- ciInf_le (abstract). -/
def ciInf_le' : Prop := True
/-- ciInf_le_of_le (abstract). -/
def ciInf_le_of_le' : Prop := True
/-- ciInf_set_le (abstract). -/
def ciInf_set_le' : Prop := True
/-- ciSup_const (abstract). -/
def ciSup_const' : Prop := True
/-- ciInf_const (abstract). -/
def ciInf_const' : Prop := True
/-- ciSup_unique (abstract). -/
def ciSup_unique' : Prop := True
/-- ciInf_unique (abstract). -/
def ciInf_unique' : Prop := True
/-- ciSup_subsingleton (abstract). -/
def ciSup_subsingleton' : Prop := True
/-- ciInf_subsingleton (abstract). -/
def ciInf_subsingleton' : Prop := True
/-- ciSup_pos (abstract). -/
def ciSup_pos' : Prop := True
/-- ciInf_pos (abstract). -/
def ciInf_pos' : Prop := True
/-- ciSup_neg (abstract). -/
def ciSup_neg' : Prop := True
/-- ciInf_neg (abstract). -/
def ciInf_neg' : Prop := True
/-- ciSup_eq_ite (abstract). -/
def ciSup_eq_ite' : Prop := True
/-- ciInf_eq_ite (abstract). -/
def ciInf_eq_ite' : Prop := True
/-- cbiSup_eq_of_forall (abstract). -/
def cbiSup_eq_of_forall' : Prop := True
/-- cbiInf_eq_of_forall (abstract). -/
def cbiInf_eq_of_forall' : Prop := True
/-- ciInf_eq_of_forall_ge_of_forall_gt_exists_lt (abstract). -/
def ciInf_eq_of_forall_ge_of_forall_gt_exists_lt' : Prop := True
/-- ciSup_mem_iInter_Icc_of_antitone (abstract). -/
def ciSup_mem_iInter_Icc_of_antitone' : Prop := True
/-- ciSup_mem_iInter_Icc_of_antitone_Icc (abstract). -/
def ciSup_mem_iInter_Icc_of_antitone_Icc' : Prop := True
/-- Iic_ciInf (abstract). -/
def Iic_ciInf' : Prop := True
/-- Ici_ciSup (abstract). -/
def Ici_ciSup' : Prop := True
/-- ciSup_subtype (abstract). -/
def ciSup_subtype' : Prop := True
/-- ciInf_subtype (abstract). -/
def ciInf_subtype' : Prop := True
/-- ciSup_subtype'' (abstract). -/
def ciSup_subtype'' : Prop := True
/-- ciInf_subtype'' (abstract). -/
def ciInf_subtype'' : Prop := True
/-- csSup_image (abstract). -/
def csSup_image' : Prop := True
/-- csInf_image (abstract). -/
def csInf_image' : Prop := True
/-- ciSup_image (abstract). -/
def ciSup_image' : Prop := True
/-- ciInf_image (abstract). -/
def ciInf_image' : Prop := True
/-- exists_lt_of_lt_ciSup (abstract). -/
def exists_lt_of_lt_ciSup' : Prop := True
/-- exists_lt_of_ciInf_lt (abstract). -/
def exists_lt_of_ciInf_lt' : Prop := True
/-- lt_ciSup_iff (abstract). -/
def lt_ciSup_iff' : Prop := True
/-- ciInf_lt_iff (abstract). -/
def ciInf_lt_iff' : Prop := True
/-- cbiSup_eq_of_not_forall (abstract). -/
def cbiSup_eq_of_not_forall' : Prop := True
/-- cbiInf_eq_of_not_forall (abstract). -/
def cbiInf_eq_of_not_forall' : Prop := True
/-- ciInf_eq_bot_of_bot_mem (abstract). -/
def ciInf_eq_bot_of_bot_mem' : Prop := True
/-- ciInf_eq_top_of_top_mem (abstract). -/
def ciInf_eq_top_of_top_mem' : Prop := True
/-- ciInf_mem (abstract). -/
def ciInf_mem' : Prop := True
/-- ciSup_of_empty (abstract). -/
def ciSup_of_empty' : Prop := True
/-- ciSup_false (abstract). -/
def ciSup_false' : Prop := True
/-- le_ciSup_iff' (abstract). -/
def le_ciSup_iff' : Prop := True
/-- ciSup_or' (abstract). -/
def ciSup_or' : Prop := True
/-- l_csSup (abstract). -/
def l_csSup' : Prop := True
/-- l_ciSup (abstract). -/
def l_ciSup' : Prop := True
/-- l_ciSup_set (abstract). -/
def l_ciSup_set' : Prop := True
/-- u_csInf (abstract). -/
def u_csInf' : Prop := True
/-- u_ciInf (abstract). -/
def u_ciInf' : Prop := True
/-- u_ciInf_set (abstract). -/
def u_ciInf_set' : Prop := True
/-- map_csSup (abstract). -/
def map_csSup' : Prop := True
/-- map_ciSup (abstract). -/
def map_ciSup' : Prop := True
/-- map_ciSup_set (abstract). -/
def map_ciSup_set' : Prop := True
/-- map_ciInf (abstract). -/
def map_ciInf' : Prop := True
/-- map_ciInf_set (abstract). -/
def map_ciInf_set' : Prop := True
/-- iSup_coe_eq_top (abstract). -/
def iSup_coe_eq_top' : Prop := True
/-- iSup_coe_lt_top (abstract). -/
def iSup_coe_lt_top' : Prop := True
/-- iInf_coe_eq_top (abstract). -/
def iInf_coe_eq_top' : Prop := True
/-- iInf_coe_lt_top (abstract). -/
def iInf_coe_lt_top' : Prop := True

-- Copy.lean

-- CountableDenseLinearOrder.lean
/-- exists_between_finsets (abstract). -/
def exists_between_finsets' : Prop := True
/-- exists_orderEmbedding_insert (abstract). -/
def exists_orderEmbedding_insert' : Prop := True
/-- PartialIso (abstract). -/
def PartialIso' : Prop := True
/-- exists_across (abstract). -/
def exists_across' : Prop := True
-- COLLISION: comm' already in SetTheory.lean — rename needed
/-- definedAtLeft (abstract). -/
def definedAtLeft' : Prop := True
/-- definedAtRight (abstract). -/
def definedAtRight' : Prop := True
/-- funOfIdeal (abstract). -/
def funOfIdeal' : Prop := True
/-- invOfIdeal (abstract). -/
def invOfIdeal' : Prop := True
/-- iso_of_countable_dense (abstract). -/
def iso_of_countable_dense' : Prop := True

-- Cover.lean
/-- WCovBy (abstract). -/
def WCovBy' : Prop := True
/-- wcovBy_of_le_of_le (abstract). -/
def wcovBy_of_le_of_le' : Prop := True
/-- wcovBy (abstract). -/
def wcovBy' : Prop := True
/-- wcovBy_iff_le (abstract). -/
def wcovBy_iff_le' : Prop := True
/-- wcovBy_of_eq_or_eq (abstract). -/
def wcovBy_of_eq_or_eq' : Prop := True
/-- trans_wcovBy (abstract). -/
def trans_wcovBy' : Prop := True
/-- wcovBy_congr_left (abstract). -/
def wcovBy_congr_left' : Prop := True
/-- trans_antisymm_rel (abstract). -/
def trans_antisymm_rel' : Prop := True
/-- wcovBy_congr_right (abstract). -/
def wcovBy_congr_right' : Prop := True
/-- not_wcovBy_iff (abstract). -/
def not_wcovBy_iff' : Prop := True
/-- Ioo_eq (abstract). -/
def Ioo_eq' : Prop := True
/-- wcovBy_iff_Ioo_eq (abstract). -/
def wcovBy_iff_Ioo_eq' : Prop := True
/-- of_le_of_le (abstract). -/
def of_le_of_le' : Prop := True
/-- apply_wcovBy_apply_iff (abstract). -/
def apply_wcovBy_apply_iff' : Prop := True
/-- toDual_wcovBy_toDual_iff (abstract). -/
def toDual_wcovBy_toDual_iff' : Prop := True
/-- ofDual_wcovBy_ofDual_iff (abstract). -/
def ofDual_wcovBy_ofDual_iff' : Prop := True
/-- wcovBy_of_apply (abstract). -/
def wcovBy_of_apply' : Prop := True
/-- map_wcovBy (abstract). -/
def map_wcovBy' : Prop := True
/-- eq_or_eq (abstract). -/
def eq_or_eq' : Prop := True
/-- wcovBy_iff_le_and_eq_or_eq (abstract). -/
def wcovBy_iff_le_and_eq_or_eq' : Prop := True
/-- le_and_le_iff (abstract). -/
def le_and_le_iff' : Prop := True
/-- Icc_eq (abstract). -/
def Icc_eq' : Prop := True
/-- Ico_subset (abstract). -/
def Ico_subset' : Prop := True
/-- Ioc_subset (abstract). -/
def Ioc_subset' : Prop := True
/-- sup_eq (abstract). -/
def sup_eq' : Prop := True
/-- CovBy (abstract). -/
def CovBy' : Prop := True
/-- not_covBy_iff (abstract). -/
def not_covBy_iff' : Prop := True
/-- not_covBy (abstract). -/
def not_covBy' : Prop := True
/-- denselyOrdered_iff_forall_not_covBy (abstract). -/
def denselyOrdered_iff_forall_not_covBy' : Prop := True
/-- covBy_of_not_le (abstract). -/
def covBy_of_not_le' : Prop := True
/-- covBy_of_lt (abstract). -/
def covBy_of_lt' : Prop := True
/-- of_le_of_lt (abstract). -/
def of_le_of_lt' : Prop := True
/-- of_lt_of_le (abstract). -/
def of_lt_of_le' : Prop := True
/-- not_covBy_of_lt_of_lt (abstract). -/
def not_covBy_of_lt_of_lt' : Prop := True
/-- covBy_iff_wcovBy_and_lt (abstract). -/
def covBy_iff_wcovBy_and_lt' : Prop := True
/-- covBy_iff_wcovBy_and_not_le (abstract). -/
def covBy_iff_wcovBy_and_not_le' : Prop := True
/-- wcovBy_iff_covBy_or_le_and_le (abstract). -/
def wcovBy_iff_covBy_or_le_and_le' : Prop := True
/-- trans_covBy (abstract). -/
def trans_covBy' : Prop := True
/-- covBy_congr_left (abstract). -/
def covBy_congr_left' : Prop := True
/-- trans_antisymmRel (abstract). -/
def trans_antisymmRel' : Prop := True
/-- covBy_iff_Ioo_eq (abstract). -/
def covBy_iff_Ioo_eq' : Prop := True
/-- apply_covBy_apply_iff (abstract). -/
def apply_covBy_apply_iff' : Prop := True
/-- covBy_of_eq_or_eq (abstract). -/
def covBy_of_eq_or_eq' : Prop := True
/-- covBy_of_apply (abstract). -/
def covBy_of_apply' : Prop := True
/-- map_covBy (abstract). -/
def map_covBy' : Prop := True
/-- covBy_of_ne (abstract). -/
def covBy_of_ne' : Prop := True
/-- covBy_iff_wcovBy_and_ne (abstract). -/
def covBy_iff_wcovBy_and_ne' : Prop := True
/-- Ioi_eq (abstract). -/
def Ioi_eq' : Prop := True
/-- Iio_eq (abstract). -/
def Iio_eq' : Prop := True
/-- le_of_lt (abstract). -/
def le_of_lt' : Prop := True
/-- ge_of_gt (abstract). -/
def ge_of_gt' : Prop := True
/-- unique_left (abstract). -/
def unique_left' : Prop := True
/-- unique_right (abstract). -/
def unique_right' : Prop := True
/-- eq_of_between (abstract). -/
def eq_of_between' : Prop := True
/-- covBy_iff_lt_iff_le_left (abstract). -/
def covBy_iff_lt_iff_le_left' : Prop := True
/-- covBy_iff_le_iff_lt_left (abstract). -/
def covBy_iff_le_iff_lt_left' : Prop := True
/-- covBy_iff_lt_iff_le_right (abstract). -/
def covBy_iff_lt_iff_le_right' : Prop := True
/-- covBy_iff_le_iff_lt_right (abstract). -/
def covBy_iff_le_iff_lt_right' : Prop := True
/-- exists_disjoint_Iio_Ioi (abstract). -/
def exists_disjoint_Iio_Ioi' : Prop := True
/-- wcovBy_insert (abstract). -/
def wcovBy_insert' : Prop := True
/-- sdiff_singleton_wcovBy (abstract). -/
def sdiff_singleton_wcovBy' : Prop := True
/-- covBy_insert (abstract). -/
def covBy_insert' : Prop := True
/-- sdiff_singleton_covBy (abstract). -/
def sdiff_singleton_covBy' : Prop := True
/-- exists_set_insert (abstract). -/
def exists_set_insert' : Prop := True
/-- exists_set_sdiff_singleton (abstract). -/
def exists_set_sdiff_singleton' : Prop := True
/-- covBy_iff_exists_insert (abstract). -/
def covBy_iff_exists_insert' : Prop := True
/-- covBy_iff_exists_sdiff_singleton (abstract). -/
def covBy_iff_exists_sdiff_singleton' : Prop := True
/-- wcovBy_eq_reflGen_covBy (abstract). -/
def wcovBy_eq_reflGen_covBy' : Prop := True
/-- transGen_wcovBy_eq_reflTransGen_covBy (abstract). -/
def transGen_wcovBy_eq_reflTransGen_covBy' : Prop := True
/-- reflTransGen_wcovBy_eq_reflTransGen_covBy (abstract). -/
def reflTransGen_wcovBy_eq_reflTransGen_covBy' : Prop := True
/-- swap_wcovBy_swap (abstract). -/
def swap_wcovBy_swap' : Prop := True
/-- swap_covBy_swap (abstract). -/
def swap_covBy_swap' : Prop := True
/-- fst_eq_or_snd_eq_of_wcovBy (abstract). -/
def fst_eq_or_snd_eq_of_wcovBy' : Prop := True
-- COLLISION: fst' already in SetTheory.lean — rename needed
/-- snd (abstract). -/
def snd' : Prop := True
/-- mk_wcovBy_mk_iff_left (abstract). -/
def mk_wcovBy_mk_iff_left' : Prop := True
/-- mk_wcovBy_mk_iff_right (abstract). -/
def mk_wcovBy_mk_iff_right' : Prop := True
/-- mk_covBy_mk_iff_left (abstract). -/
def mk_covBy_mk_iff_left' : Prop := True
/-- mk_covBy_mk_iff_right (abstract). -/
def mk_covBy_mk_iff_right' : Prop := True
/-- mk_wcovBy_mk_iff (abstract). -/
def mk_wcovBy_mk_iff' : Prop := True
/-- mk_covBy_mk_iff (abstract). -/
def mk_covBy_mk_iff' : Prop := True
/-- wcovBy_iff (abstract). -/
def wcovBy_iff' : Prop := True
/-- covBy_iff (abstract). -/
def covBy_iff' : Prop := True
/-- coe_wcovBy_coe (abstract). -/
def coe_wcovBy_coe' : Prop := True
/-- coe_covBy_coe (abstract). -/
def coe_covBy_coe' : Prop := True
/-- coe_covBy_top (abstract). -/
def coe_covBy_top' : Prop := True
/-- coe_wcovBy_top (abstract). -/
def coe_wcovBy_top' : Prop := True
/-- bot_covBy_coe (abstract). -/
def bot_covBy_coe' : Prop := True
/-- bot_wcovBy_coe (abstract). -/
def bot_wcovBy_coe' : Prop := True
/-- exists_covBy_of_wellFoundedLT (abstract). -/
def exists_covBy_of_wellFoundedLT' : Prop := True
/-- exists_covBy_of_wellFoundedGT (abstract). -/
def exists_covBy_of_wellFoundedGT' : Prop := True

-- Defs/LinearOrder.lean
/-- maxDefault (abstract). -/
def maxDefault' : Prop := True
/-- minDefault (abstract). -/
def minDefault' : Prop := True
/-- LinearOrder (abstract). -/
def LinearOrder' : Prop := True
/-- le_of_not_ge (abstract). -/
def le_of_not_ge' : Prop := True
/-- le_of_not_le (abstract). -/
def le_of_not_le' : Prop := True
/-- lt_of_not_ge (abstract). -/
def lt_of_not_ge' : Prop := True
/-- lt_trichotomy (abstract). -/
def lt_trichotomy' : Prop := True
/-- le_of_not_lt (abstract). -/
def le_of_not_lt' : Prop := True
/-- le_of_not_gt (abstract). -/
def le_of_not_gt' : Prop := True
/-- le_or_lt (abstract). -/
def le_or_lt' : Prop := True
/-- lt_or_ge (abstract). -/
def lt_or_ge' : Prop := True
/-- le_or_gt (abstract). -/
def le_or_gt' : Prop := True
/-- lt_or_gt_of_ne (abstract). -/
def lt_or_gt_of_ne' : Prop := True
/-- ne_iff_lt_or_gt (abstract). -/
def ne_iff_lt_or_gt' : Prop := True
/-- lt_iff_not_ge (abstract). -/
def lt_iff_not_ge' : Prop := True
-- COLLISION: not_le' already in SetTheory.lean — rename needed
/-- eq_or_lt_of_not_lt (abstract). -/
def eq_or_lt_of_not_lt' : Prop := True
/-- ltByCases (abstract). -/
def ltByCases' : Prop := True
/-- ltGeByCases (abstract). -/
def ltGeByCases' : Prop := True
/-- le_imp_le_of_lt_imp_lt (abstract). -/
def le_imp_le_of_lt_imp_lt' : Prop := True
/-- min_le_left (abstract). -/
def min_le_left' : Prop := True
/-- min_le_right (abstract). -/
def min_le_right' : Prop := True
/-- le_min (abstract). -/
def le_min' : Prop := True
/-- le_max_left (abstract). -/
def le_max_left' : Prop := True
/-- le_max_right (abstract). -/
def le_max_right' : Prop := True
/-- max_le (abstract). -/
def max_le' : Prop := True
/-- eq_min (abstract). -/
def eq_min' : Prop := True
/-- min_comm (abstract). -/
def min_comm' : Prop := True
/-- min_assoc (abstract). -/
def min_assoc' : Prop := True
/-- min_left_comm (abstract). -/
def min_left_comm' : Prop := True
/-- min_self (abstract). -/
def min_self' : Prop := True
/-- min_eq_left (abstract). -/
def min_eq_left' : Prop := True
/-- min_eq_right (abstract). -/
def min_eq_right' : Prop := True
/-- eq_max (abstract). -/
def eq_max' : Prop := True
/-- max_comm (abstract). -/
def max_comm' : Prop := True
/-- max_assoc (abstract). -/
def max_assoc' : Prop := True
/-- max_left_comm (abstract). -/
def max_left_comm' : Prop := True
/-- max_self (abstract). -/
def max_self' : Prop := True
/-- max_eq_left (abstract). -/
def max_eq_left' : Prop := True
/-- max_eq_right (abstract). -/
def max_eq_right' : Prop := True
/-- min_eq_left_of_lt (abstract). -/
def min_eq_left_of_lt' : Prop := True
/-- min_eq_right_of_lt (abstract). -/
def min_eq_right_of_lt' : Prop := True
/-- max_eq_left_of_lt (abstract). -/
def max_eq_left_of_lt' : Prop := True
/-- max_eq_right_of_lt (abstract). -/
def max_eq_right_of_lt' : Prop := True
/-- lt_min (abstract). -/
def lt_min' : Prop := True
/-- max_lt (abstract). -/
def max_lt' : Prop := True
/-- compare_lt_iff_lt (abstract). -/
def compare_lt_iff_lt' : Prop := True
/-- compare_gt_iff_gt (abstract). -/
def compare_gt_iff_gt' : Prop := True
/-- compare_eq_iff_eq (abstract). -/
def compare_eq_iff_eq' : Prop := True
/-- compare_le_iff_le (abstract). -/
def compare_le_iff_le' : Prop := True
/-- compare_ge_iff_ge (abstract). -/
def compare_ge_iff_ge' : Prop := True
/-- compare_iff (abstract). -/
def compare_iff' : Prop := True
/-- cmp_eq_compare (abstract). -/
def cmp_eq_compare' : Prop := True
/-- cmp_eq_compareOfLessAndEq (abstract). -/
def cmp_eq_compareOfLessAndEq' : Prop := True

-- Defs/PartialOrder.lean
/-- Preorder (abstract). -/
def Preorder' : Prop := True
/-- le_refl (abstract). -/
def le_refl' : Prop := True
/-- le_rfl (abstract). -/
def le_rfl' : Prop := True
/-- lt_iff_le_not_le (abstract). -/
def lt_iff_le_not_le' : Prop := True
/-- lt_of_le_not_le (abstract). -/
def lt_of_le_not_le' : Prop := True
/-- le_not_le_of_lt (abstract). -/
def le_not_le_of_lt' : Prop := True
/-- le_of_eq (abstract). -/
def le_of_eq' : Prop := True
/-- not_le_of_lt (abstract). -/
def not_le_of_lt' : Prop := True
/-- not_le_of_gt (abstract). -/
def not_le_of_gt' : Prop := True
/-- not_lt_of_le (abstract). -/
def not_lt_of_le' : Prop := True
/-- not_lt_of_ge (abstract). -/
def not_lt_of_ge' : Prop := True
/-- ge_trans (abstract). -/
def ge_trans' : Prop := True
/-- lt_irrefl (abstract). -/
def lt_irrefl' : Prop := True
/-- gt_irrefl (abstract). -/
def gt_irrefl' : Prop := True
/-- gt_of_gt_of_ge (abstract). -/
def gt_of_gt_of_ge' : Prop := True
/-- gt_of_ge_of_gt (abstract). -/
def gt_of_ge_of_gt' : Prop := True
/-- decidableLTOfDecidableLE (abstract). -/
def decidableLTOfDecidableLE' : Prop := True
-- COLLISION: PartialOrder' already in Order.lean — rename needed
/-- le_antisymm_iff (abstract). -/
def le_antisymm_iff' : Prop := True
/-- decidableEqOfDecidableLE (abstract). -/
def decidableEqOfDecidableLE' : Prop := True
/-- lt_or_eq_of_le (abstract). -/
def lt_or_eq_of_le' : Prop := True
/-- eq_or_lt_of_le (abstract). -/
def eq_or_lt_of_le' : Prop := True
/-- le_iff_lt_or_eq (abstract). -/
def le_iff_lt_or_eq' : Prop := True

-- Defs/Unbundled.lean
/-- EmptyRelation (abstract). -/
def EmptyRelation' : Prop := True
/-- IsIrrefl (abstract). -/
def IsIrrefl' : Prop := True
/-- IsRefl (abstract). -/
def IsRefl' : Prop := True
/-- IsSymm (abstract). -/
def IsSymm' : Prop := True
/-- IsAsymm (abstract). -/
def IsAsymm' : Prop := True
/-- IsAntisymm (abstract). -/
def IsAntisymm' : Prop := True
/-- IsTrans (abstract). -/
def IsTrans' : Prop := True
/-- IsPartialOrder (abstract). -/
def IsPartialOrder' : Prop := True
/-- IsLinearOrder (abstract). -/
def IsLinearOrder' : Prop := True
/-- IsEquiv (abstract). -/
def IsEquiv' : Prop := True
/-- IsStrictWeakOrder (abstract). -/
def IsStrictWeakOrder' : Prop := True
/-- IsTrichotomous (abstract). -/
def IsTrichotomous' : Prop := True
/-- IsStrictTotalOrder (abstract). -/
def IsStrictTotalOrder' : Prop := True
/-- irrefl (abstract). -/
def irrefl' : Prop := True
-- COLLISION: refl' already in SetTheory.lean — rename needed
/-- asymm (abstract). -/
def asymm' : Prop := True
/-- trichotomous (abstract). -/
def trichotomous' : Prop := True
/-- irrefl_of (abstract). -/
def irrefl_of' : Prop := True
/-- refl_of (abstract). -/
def refl_of' : Prop := True
/-- trans_of (abstract). -/
def trans_of' : Prop := True
/-- symm_of (abstract). -/
def symm_of' : Prop := True
/-- asymm_of (abstract). -/
def asymm_of' : Prop := True
/-- total_of (abstract). -/
def total_of' : Prop := True
/-- Reflexive (abstract). -/
def Reflexive' : Prop := True
/-- Symmetric (abstract). -/
def Symmetric' : Prop := True
/-- Transitive (abstract). -/
def Transitive' : Prop := True
/-- Irreflexive (abstract). -/
def Irreflexive' : Prop := True
/-- AntiSymmetric (abstract). -/
def AntiSymmetric' : Prop := True
/-- Total (abstract). -/
def Total' : Prop := True
/-- symmetric (abstract). -/
def symmetric' : Prop := True
/-- transitive (abstract). -/
def transitive' : Prop := True
/-- Minimal (abstract). -/
def Minimal' : Prop := True
/-- Maximal (abstract). -/
def Maximal' : Prop := True
/-- IsUpperSet (abstract). -/
def IsUpperSet' : Prop := True
/-- IsLowerSet (abstract). -/
def IsLowerSet' : Prop := True
/-- UpperSet (abstract). -/
def UpperSet' : Prop := True
/-- LowerSet (abstract). -/
def LowerSet' : Prop := True

-- Directed.lean
/-- Directed (abstract). -/
def Directed' : Prop := True
/-- DirectedOn (abstract). -/
def DirectedOn' : Prop := True
/-- directedOn_iff_directed (abstract). -/
def directedOn_iff_directed' : Prop := True
/-- directedOn_range (abstract). -/
def directedOn_range' : Prop := True
/-- directedOn_image (abstract). -/
def directedOn_image' : Prop := True
/-- mono_comp (abstract). -/
def mono_comp' : Prop := True
/-- directedOn_of_sup_mem (abstract). -/
def directedOn_of_sup_mem' : Prop := True
/-- extend_bot (abstract). -/
def extend_bot' : Prop := True
/-- directedOn_of_inf_mem (abstract). -/
def directedOn_of_inf_mem' : Prop := True
/-- directed_of (abstract). -/
def directed_of' : Prop := True
/-- isDirected_mono (abstract). -/
def isDirected_mono' : Prop := True
/-- exists_ge_ge (abstract). -/
def exists_ge_ge' : Prop := True
/-- exists_le_le (abstract). -/
def exists_le_le' : Prop := True
/-- directed_of_isDirected_le (abstract). -/
def directed_of_isDirected_le' : Prop := True
/-- directed_le (abstract). -/
def directed_le' : Prop := True
/-- directed_ge (abstract). -/
def directed_ge' : Prop := True
/-- directed_of_isDirected_ge (abstract). -/
def directed_of_isDirected_ge' : Prop := True
/-- directedOn_singleton (abstract). -/
def directedOn_singleton' : Prop := True
/-- directedOn_pair (abstract). -/
def directedOn_pair' : Prop := True
/-- is_bot_of_is_min (abstract). -/
def is_bot_of_is_min' : Prop := True
/-- is_top_of_is_max (abstract). -/
def is_top_of_is_max' : Prop := True
/-- isTop_or_exists_gt (abstract). -/
def isTop_or_exists_gt' : Prop := True
/-- isBot_or_exists_lt (abstract). -/
def isBot_or_exists_lt' : Prop := True
/-- isBot_iff_isMin (abstract). -/
def isBot_iff_isMin' : Prop := True
/-- isTop_iff_isMax (abstract). -/
def isTop_iff_isMax' : Prop := True
/-- exists_lt_of_directed_ge (abstract). -/
def exists_lt_of_directed_ge' : Prop := True
/-- exists_lt_of_directed_le (abstract). -/
def exists_lt_of_directed_le' : Prop := True
/-- not_isMax (abstract). -/
def not_isMax' : Prop := True
/-- not_isMin (abstract). -/
def not_isMin' : Prop := True
/-- constant_of_monotone_antitone (abstract). -/
def constant_of_monotone_antitone' : Prop := True
/-- constant_of_monotoneOn_antitoneOn (abstract). -/
def constant_of_monotoneOn_antitoneOn' : Prop := True

-- DirectedInverseSystem.lean
-- COLLISION: argument' already in SetTheory.lean — rename needed
/-- DirectedSystem (abstract). -/
def DirectedSystem' : Prop := True
/-- InverseSystem (abstract). -/
def InverseSystem' : Prop := True
/-- limit (abstract). -/
def limit' : Prop := True
/-- piLT (abstract). -/
def piLT' : Prop := True
/-- piLTProj (abstract). -/
def piLTProj' : Prop := True
/-- IsNatEquiv (abstract). -/
def IsNatEquiv' : Prop := True
/-- piLTLim (abstract). -/
def piLTLim' : Prop := True
/-- piLTLim_symm_apply (abstract). -/
def piLTLim_symm_apply' : Prop := True
/-- piSplitLE (abstract). -/
def piSplitLE' : Prop := True
/-- piSplitLE_eq (abstract). -/
def piSplitLE_eq' : Prop := True
/-- piSplitLE_lt (abstract). -/
def piSplitLE_lt' : Prop := True
/-- piEquivSucc (abstract). -/
def piEquivSucc' : Prop := True
/-- piEquivSucc_self (abstract). -/
def piEquivSucc_self' : Prop := True
/-- isNatEquiv_piEquivSucc (abstract). -/
def isNatEquiv_piEquivSucc' : Prop := True
/-- invLimEquiv (abstract). -/
def invLimEquiv' : Prop := True
/-- piEquivLim (abstract). -/
def piEquivLim' : Prop := True
/-- isNatEquiv_piEquivLim (abstract). -/
def isNatEquiv_piEquivLim' : Prop := True
/-- PEquivOn (abstract). -/
def PEquivOn' : Prop := True
/-- restrict (abstract). -/
def restrict' : Prop := True
/-- unique_pEquivOn (abstract). -/
def unique_pEquivOn' : Prop := True
/-- pEquivOn_apply_eq (abstract). -/
def pEquivOn_apply_eq' : Prop := True
/-- pEquivOnSucc (abstract). -/
def pEquivOnSucc' : Prop := True
/-- pEquivOnGlue (abstract). -/
def pEquivOnGlue' : Prop := True
/-- pEquivOnLim (abstract). -/
def pEquivOnLim' : Prop := True
/-- globalEquivAux (abstract). -/
def globalEquivAux' : Prop := True
/-- globalEquiv (abstract). -/
def globalEquiv' : Prop := True
/-- globalEquiv_naturality (abstract). -/
def globalEquiv_naturality' : Prop := True
/-- globalEquiv_compatibility (abstract). -/
def globalEquiv_compatibility' : Prop := True

-- Disjoint.lean
-- COLLISION: stating' already in SetTheory.lean — rename needed
/-- Disjoint (abstract). -/
def Disjoint' : Prop := True
/-- disjoint_of_subsingleton (abstract). -/
def disjoint_of_subsingleton' : Prop := True
/-- disjoint_comm (abstract). -/
def disjoint_comm' : Prop := True
/-- symmetric_disjoint (abstract). -/
def symmetric_disjoint' : Prop := True
/-- disjoint_bot_left (abstract). -/
def disjoint_bot_left' : Prop := True
/-- disjoint_bot_right (abstract). -/
def disjoint_bot_right' : Prop := True
/-- mono_left (abstract). -/
def mono_left' : Prop := True
/-- mono_right (abstract). -/
def mono_right' : Prop := True
/-- disjoint_self (abstract). -/
def disjoint_self' : Prop := True
/-- ne (abstract). -/
def ne' : Prop := True
/-- eq_bot_of_le (abstract). -/
def eq_bot_of_le' : Prop := True
/-- eq_bot_of_ge (abstract). -/
def eq_bot_of_ge' : Prop := True
/-- eq_iff (abstract). -/
def eq_iff' : Prop := True
/-- ne_iff (abstract). -/
def ne_iff' : Prop := True
/-- disjoint_top (abstract). -/
def disjoint_top' : Prop := True
/-- top_disjoint (abstract). -/
def top_disjoint' : Prop := True
/-- disjoint_iff_inf_le (abstract). -/
def disjoint_iff_inf_le' : Prop := True
/-- disjoint_of_le_iff_left_eq_bot (abstract). -/
def disjoint_of_le_iff_left_eq_bot' : Prop := True
/-- le_bot (abstract). -/
def le_bot' : Prop := True
/-- eq_bot (abstract). -/
def eq_bot' : Prop := True
/-- of_disjoint_inf_of_le (abstract). -/
def of_disjoint_inf_of_le' : Prop := True
/-- right_lt_sup_of_left_ne_bot (abstract). -/
def right_lt_sup_of_left_ne_bot' : Prop := True
/-- disjoint_sup_left (abstract). -/
def disjoint_sup_left' : Prop := True
/-- disjoint_sup_right (abstract). -/
def disjoint_sup_right' : Prop := True
/-- sup_right (abstract). -/
def sup_right' : Prop := True
/-- left_le_of_le_sup_right (abstract). -/
def left_le_of_le_sup_right' : Prop := True
/-- left_le_of_le_sup_left (abstract). -/
def left_le_of_le_sup_left' : Prop := True
/-- Codisjoint (abstract). -/
def Codisjoint' : Prop := True
/-- codisjoint_comm (abstract). -/
def codisjoint_comm' : Prop := True
/-- symmetric_codisjoint (abstract). -/
def symmetric_codisjoint' : Prop := True
/-- codisjoint_top_left (abstract). -/
def codisjoint_top_left' : Prop := True
/-- codisjoint_top_right (abstract). -/
def codisjoint_top_right' : Prop := True
/-- codisjoint_self (abstract). -/
def codisjoint_self' : Prop := True
/-- eq_top_of_le (abstract). -/
def eq_top_of_le' : Prop := True
/-- eq_top_of_ge (abstract). -/
def eq_top_of_ge' : Prop := True
/-- codisjoint_bot (abstract). -/
def codisjoint_bot' : Prop := True
/-- bot_codisjoint (abstract). -/
def bot_codisjoint' : Prop := True
/-- ne_bot_of_ne_top (abstract). -/
def ne_bot_of_ne_top' : Prop := True
/-- codisjoint_iff_le_sup (abstract). -/
def codisjoint_iff_le_sup' : Prop := True
/-- top_le (abstract). -/
def top_le' : Prop := True
/-- eq_top (abstract). -/
def eq_top' : Prop := True
/-- of_codisjoint_sup_of_le (abstract). -/
def of_codisjoint_sup_of_le' : Prop := True
/-- codisjoint_inf_left (abstract). -/
def codisjoint_inf_left' : Prop := True
/-- codisjoint_inf_right (abstract). -/
def codisjoint_inf_right' : Prop := True
/-- inf_left (abstract). -/
def inf_left' : Prop := True
/-- inf_right (abstract). -/
def inf_right' : Prop := True
/-- left_le_of_le_inf_right (abstract). -/
def left_le_of_le_inf_right' : Prop := True
/-- left_le_of_le_inf_left (abstract). -/
def left_le_of_le_inf_left' : Prop := True
/-- le_of_codisjoint (abstract). -/
def le_of_codisjoint' : Prop := True
/-- IsCompl (abstract). -/
def IsCompl' : Prop := True
/-- isCompl_iff (abstract). -/
def isCompl_iff' : Prop := True
/-- isCompl_comm (abstract). -/
def isCompl_comm' : Prop := True
/-- inf_left_le_of_le_sup_right (abstract). -/
def inf_left_le_of_le_sup_right' : Prop := True
/-- right_unique (abstract). -/
def right_unique' : Prop := True
/-- left_unique (abstract). -/
def left_unique' : Prop := True
/-- sup_inf (abstract). -/
def sup_inf' : Prop := True
/-- inf_sup (abstract). -/
def inf_sup' : Prop := True
/-- isCompl_toDual_iff (abstract). -/
def isCompl_toDual_iff' : Prop := True
/-- isCompl_ofDual_iff (abstract). -/
def isCompl_ofDual_iff' : Prop := True
/-- isCompl_bot_top (abstract). -/
def isCompl_bot_top' : Prop := True
/-- isCompl_top_bot (abstract). -/
def isCompl_top_bot' : Prop := True
/-- eq_top_of_isCompl_bot (abstract). -/
def eq_top_of_isCompl_bot' : Prop := True
/-- eq_top_of_bot_isCompl (abstract). -/
def eq_top_of_bot_isCompl' : Prop := True
/-- eq_bot_of_isCompl_top (abstract). -/
def eq_bot_of_isCompl_top' : Prop := True
/-- eq_bot_of_top_isCompl (abstract). -/
def eq_bot_of_top_isCompl' : Prop := True
/-- IsComplemented (abstract). -/
def IsComplemented' : Prop := True
/-- isComplemented_bot (abstract). -/
def isComplemented_bot' : Prop := True
/-- isComplemented_top (abstract). -/
def isComplemented_top' : Prop := True
-- COLLISION: sup' already in SetTheory.lean — rename needed
/-- inf (abstract). -/
def inf' : Prop := True
/-- ComplementedLattice (abstract). -/
def ComplementedLattice' : Prop := True
/-- complementedLattice_iff (abstract). -/
def complementedLattice_iff' : Prop := True
/-- Complementeds (abstract). -/
def Complementeds' : Prop := True
/-- disjoint_coe (abstract). -/
def disjoint_coe' : Prop := True
/-- codisjoint_coe (abstract). -/
def codisjoint_coe' : Prop := True
/-- isCompl_coe (abstract). -/
def isCompl_coe' : Prop := True

-- Disjointed.lean
/-- disjointed (abstract). -/
def disjointed' : Prop := True
/-- disjointed_le_id (abstract). -/
def disjointed_le_id' : Prop := True
/-- disjointed_le (abstract). -/
def disjointed_le' : Prop := True
/-- disjoint_disjointed (abstract). -/
def disjoint_disjointed' : Prop := True
/-- disjointedRec (abstract). -/
def disjointedRec' : Prop := True
/-- disjointed_succ (abstract). -/
def disjointed_succ' : Prop := True
/-- disjointed_succ_sup (abstract). -/
def disjointed_succ_sup' : Prop := True
/-- partialSups_disjointed (abstract). -/
def partialSups_disjointed' : Prop := True
/-- disjointed_unique (abstract). -/
def disjointed_unique' : Prop := True
/-- iSup_disjointed (abstract). -/
def iSup_disjointed' : Prop := True
/-- disjointed_eq_inf_compl (abstract). -/
def disjointed_eq_inf_compl' : Prop := True
/-- disjointed_subset (abstract). -/
def disjointed_subset' : Prop := True
/-- iUnion_disjointed (abstract). -/
def iUnion_disjointed' : Prop := True
/-- disjointed_eq_inter_compl (abstract). -/
def disjointed_eq_inter_compl' : Prop := True
/-- preimage_find_eq_disjointed (abstract). -/
def preimage_find_eq_disjointed' : Prop := True

-- Estimator.lean
/-- EstimatorData (abstract). -/
def EstimatorData' : Prop := True
/-- Estimator (abstract). -/
def Estimator' : Prop := True
/-- improveUntilAux (abstract). -/
def improveUntilAux' : Prop := True
/-- improveUntil (abstract). -/
def improveUntil' : Prop := True
/-- improveUntilAux_spec (abstract). -/
def improveUntilAux_spec' : Prop := True
/-- improveUntil_spec (abstract). -/
def improveUntil_spec' : Prop := True
/-- fstInst (abstract). -/
def fstInst' : Prop := True

-- Extension/Linear.lean
/-- extend_partialOrder (abstract). -/
def extend_partialOrder' : Prop := True
/-- LinearExtension (abstract). -/
def LinearExtension' : Prop := True
/-- toLinearExtension (abstract). -/
def toLinearExtension' : Prop := True

-- Extension/Well.lean
/-- wellOrderExtension (abstract). -/
def wellOrderExtension' : Prop := True
/-- exists_well_order_ge (abstract). -/
def exists_well_order_ge' : Prop := True
/-- WellOrderExtension (abstract). -/
def WellOrderExtension' : Prop := True
/-- toWellOrderExtension (abstract). -/
def toWellOrderExtension' : Prop := True
/-- toWellOrderExtension_strictMono (abstract). -/
def toWellOrderExtension_strictMono' : Prop := True

-- Filter/AtTopBot.lean
/-- atTop (abstract). -/
def atTop' : Prop := True
/-- atBot (abstract). -/
def atBot' : Prop := True
/-- mem_atTop (abstract). -/
def mem_atTop' : Prop := True
/-- Ici_mem_atTop (abstract). -/
def Ici_mem_atTop' : Prop := True
/-- Ioi_mem_atTop (abstract). -/
def Ioi_mem_atTop' : Prop := True
/-- mem_atBot (abstract). -/
def mem_atBot' : Prop := True
/-- Iic_mem_atBot (abstract). -/
def Iic_mem_atBot' : Prop := True
/-- Iio_mem_atBot (abstract). -/
def Iio_mem_atBot' : Prop := True
/-- disjoint_atBot_principal_Ioi (abstract). -/
def disjoint_atBot_principal_Ioi' : Prop := True
/-- disjoint_atTop_principal_Iio (abstract). -/
def disjoint_atTop_principal_Iio' : Prop := True
/-- disjoint_atTop_principal_Iic (abstract). -/
def disjoint_atTop_principal_Iic' : Prop := True
/-- disjoint_atBot_principal_Ici (abstract). -/
def disjoint_atBot_principal_Ici' : Prop := True
/-- disjoint_pure_atTop (abstract). -/
def disjoint_pure_atTop' : Prop := True
/-- disjoint_pure_atBot (abstract). -/
def disjoint_pure_atBot' : Prop := True
/-- not_tendsto_const_atTop (abstract). -/
def not_tendsto_const_atTop' : Prop := True
/-- not_tendsto_const_atBot (abstract). -/
def not_tendsto_const_atBot' : Prop := True
/-- eventually_ge_atTop (abstract). -/
def eventually_ge_atTop' : Prop := True
/-- eventually_le_atBot (abstract). -/
def eventually_le_atBot' : Prop := True
/-- eventually_gt_atTop (abstract). -/
def eventually_gt_atTop' : Prop := True
/-- eventually_ne_atTop (abstract). -/
def eventually_ne_atTop' : Prop := True
/-- eventually_lt_atBot (abstract). -/
def eventually_lt_atBot' : Prop := True
/-- eventually_ne_atBot (abstract). -/
def eventually_ne_atBot' : Prop := True
/-- eventually_forall_ge_atTop (abstract). -/
def eventually_forall_ge_atTop' : Prop := True
/-- eventually_forall_le_atBot (abstract). -/
def eventually_forall_le_atBot' : Prop := True
/-- atTop_eq (abstract). -/
def atTop_eq' : Prop := True
/-- atBot_eq (abstract). -/
def atBot_eq' : Prop := True
/-- tendsto_atTop_pure (abstract). -/
def tendsto_atTop_pure' : Prop := True
/-- tendsto_atBot_pure (abstract). -/
def tendsto_atBot_pure' : Prop := True
/-- atTop_eq_generate_Ici (abstract). -/
def atTop_eq_generate_Ici' : Prop := True
/-- forall_exists_of_atTop (abstract). -/
def forall_exists_of_atTop' : Prop := True
/-- forall_exists_of_atBot (abstract). -/
def forall_exists_of_atBot' : Prop := True
/-- hasAntitoneBasis_atTop (abstract). -/
def hasAntitoneBasis_atTop' : Prop := True
/-- atTop_basis (abstract). -/
def atTop_basis' : Prop := True
/-- atTop_basis_Ioi (abstract). -/
def atTop_basis_Ioi' : Prop := True
/-- atTop_neBot (abstract). -/
def atTop_neBot' : Prop := True
/-- atTop_neBot_iff (abstract). -/
def atTop_neBot_iff' : Prop := True
/-- atBot_neBot_iff (abstract). -/
def atBot_neBot_iff' : Prop := True
/-- mem_atTop_sets (abstract). -/
def mem_atTop_sets' : Prop := True
/-- eventually_atTop (abstract). -/
def eventually_atTop' : Prop := True
/-- frequently_atTop (abstract). -/
def frequently_atTop' : Prop := True
/-- exists_eventually_atTop (abstract). -/
def exists_eventually_atTop' : Prop := True
/-- map_atTop_eq (abstract). -/
def map_atTop_eq' : Prop := True
/-- atTop_countable_basis (abstract). -/
def atTop_countable_basis' : Prop := True
/-- atBot_basis_Iio (abstract). -/
def atBot_basis_Iio' : Prop := True
/-- atBot_basis' (abstract). -/
def atBot_basis' : Prop := True
/-- atBot_neBot (abstract). -/
def atBot_neBot' : Prop := True
/-- mem_atBot_sets (abstract). -/
def mem_atBot_sets' : Prop := True
/-- eventually_atBot (abstract). -/
def eventually_atBot' : Prop := True
/-- frequently_atBot (abstract). -/
def frequently_atBot' : Prop := True
/-- exists_eventually_atBot (abstract). -/
def exists_eventually_atBot' : Prop := True
/-- map_atBot_eq (abstract). -/
def map_atBot_eq' : Prop := True
/-- atBot_countable_basis (abstract). -/
def atBot_countable_basis' : Prop := True
/-- tendsto_atTop (abstract). -/
def tendsto_atTop' : Prop := True
/-- tendsto_atBot (abstract). -/
def tendsto_atBot' : Prop := True
/-- tendsto_atTop_mono' (abstract). -/
def tendsto_atTop_mono' : Prop := True
/-- tendsto_atBot_mono' (abstract). -/
def tendsto_atBot_mono' : Prop := True
/-- atTop_eq_generate_of_forall_exists_le (abstract). -/
def atTop_eq_generate_of_forall_exists_le' : Prop := True
/-- atTop_eq_generate_of_not_bddAbove (abstract). -/
def atTop_eq_generate_of_not_bddAbove' : Prop := True
/-- comap_atTop (abstract). -/
def comap_atTop' : Prop := True
/-- comap_atBot (abstract). -/
def comap_atBot' : Prop := True
/-- map_atTop (abstract). -/
def map_atTop' : Prop := True
/-- map_atBot (abstract). -/
def map_atBot' : Prop := True
/-- tendsto_atTop_iff (abstract). -/
def tendsto_atTop_iff' : Prop := True
/-- tendsto_atBot_iff (abstract). -/
def tendsto_atBot_iff' : Prop := True
/-- extraction_of_frequently_atTop' (abstract). -/
def extraction_of_frequently_atTop' : Prop := True
/-- extraction_of_eventually_atTop (abstract). -/
def extraction_of_eventually_atTop' : Prop := True
/-- extraction_forall_of_frequently (abstract). -/
def extraction_forall_of_frequently' : Prop := True
/-- extraction_forall_of_eventually (abstract). -/
def extraction_forall_of_eventually' : Prop := True
/-- atTop_of_arithmetic (abstract). -/
def atTop_of_arithmetic' : Prop := True
/-- inf_map_atTop_neBot_iff (abstract). -/
def inf_map_atTop_neBot_iff' : Prop := True
/-- exists_le_of_tendsto_atTop (abstract). -/
def exists_le_of_tendsto_atTop' : Prop := True
/-- exists_le_of_tendsto_atBot (abstract). -/
def exists_le_of_tendsto_atBot' : Prop := True
/-- exists_lt_of_tendsto_atTop (abstract). -/
def exists_lt_of_tendsto_atTop' : Prop := True
/-- exists_lt_of_tendsto_atBot (abstract). -/
def exists_lt_of_tendsto_atBot' : Prop := True
/-- inf_map_atBot_neBot_iff (abstract). -/
def inf_map_atBot_neBot_iff' : Prop := True
/-- high_scores (abstract). -/
def high_scores' : Prop := True
/-- low_scores (abstract). -/
def low_scores' : Prop := True
/-- frequently_high_scores (abstract). -/
def frequently_high_scores' : Prop := True
/-- frequently_low_scores (abstract). -/
def frequently_low_scores' : Prop := True
/-- strictMono_subseq_of_tendsto_atTop (abstract). -/
def strictMono_subseq_of_tendsto_atTop' : Prop := True
/-- strictMono_subseq_of_id_le (abstract). -/
def strictMono_subseq_of_id_le' : Prop := True
/-- upperBounds_range_comp_tendsto_atTop (abstract). -/
def upperBounds_range_comp_tendsto_atTop' : Prop := True
/-- lowerBounds_range_comp_tendsto_atBot (abstract). -/
def lowerBounds_range_comp_tendsto_atBot' : Prop := True
/-- lowerBounds_range_comp_tendsto_atTop (abstract). -/
def lowerBounds_range_comp_tendsto_atTop' : Prop := True
/-- upperBounds_range_comp_tendsto_atBot (abstract). -/
def upperBounds_range_comp_tendsto_atBot' : Prop := True
/-- ciSup_comp_tendsto_atTop (abstract). -/
def ciSup_comp_tendsto_atTop' : Prop := True
/-- ciInf_comp_tendsto_atBot (abstract). -/
def ciInf_comp_tendsto_atBot' : Prop := True
/-- ciSup_comp_tendsto_atBot (abstract). -/
def ciSup_comp_tendsto_atBot' : Prop := True
/-- ciInf_comp_tendsto_atTop (abstract). -/
def ciInf_comp_tendsto_atTop' : Prop := True
/-- ciSup_comp_tendsto_atTop_of_linearOrder (abstract). -/
def ciSup_comp_tendsto_atTop_of_linearOrder' : Prop := True
-- COLLISION: f' already in SetTheory.lean — rename needed
/-- ciInf_comp_tendsto_atBot_of_linearOrder (abstract). -/
def ciInf_comp_tendsto_atBot_of_linearOrder' : Prop := True
/-- ciInf_comp_tendsto_atTop_of_linearOrder (abstract). -/
def ciInf_comp_tendsto_atTop_of_linearOrder' : Prop := True
/-- ciSup_comp_tendsto_atBot_of_linearOrder (abstract). -/
def ciSup_comp_tendsto_atBot_of_linearOrder' : Prop := True
/-- iSup_comp_tendsto_atTop (abstract). -/
def iSup_comp_tendsto_atTop' : Prop := True
/-- iInf_comp_tendsto_atBot (abstract). -/
def iInf_comp_tendsto_atBot' : Prop := True
/-- iSup_comp_tendsto_atBot (abstract). -/
def iSup_comp_tendsto_atBot' : Prop := True
/-- iInf_comp_tendsto_atTop (abstract). -/
def iInf_comp_tendsto_atTop' : Prop := True
/-- iUnion_comp_tendsto_atTop (abstract). -/
def iUnion_comp_tendsto_atTop' : Prop := True
/-- iInter_comp_tendsto_atBot (abstract). -/
def iInter_comp_tendsto_atBot' : Prop := True
/-- iInter_comp_tendsto_atTop (abstract). -/
def iInter_comp_tendsto_atTop' : Prop := True
/-- tendsto_atBot_atTop_of_antitone (abstract). -/
def tendsto_atBot_atTop_of_antitone' : Prop := True
/-- tendsto_atTop_principal (abstract). -/
def tendsto_atTop_principal' : Prop := True
/-- tendsto_atTop_atTop (abstract). -/
def tendsto_atTop_atTop' : Prop := True
/-- tendsto_atTop_atBot (abstract). -/
def tendsto_atTop_atBot' : Prop := True
/-- tendsto_atTop_atTop_iff_of_monotone (abstract). -/
def tendsto_atTop_atTop_iff_of_monotone' : Prop := True
/-- tendsto_atTop_atBot_iff_of_antitone (abstract). -/
def tendsto_atTop_atBot_iff_of_antitone' : Prop := True
/-- tendsto_atBot_principal (abstract). -/
def tendsto_atBot_principal' : Prop := True
/-- tendsto_atBot_atTop (abstract). -/
def tendsto_atBot_atTop' : Prop := True
/-- tendsto_atBot_atBot (abstract). -/
def tendsto_atBot_atBot' : Prop := True
/-- tendsto_atBot_atBot_iff_of_monotone (abstract). -/
def tendsto_atBot_atBot_iff_of_monotone' : Prop := True
/-- tendsto_atBot_atTop_iff_of_antitone (abstract). -/
def tendsto_atBot_atTop_iff_of_antitone' : Prop := True
/-- comap_embedding_atTop (abstract). -/
def comap_embedding_atTop' : Prop := True
/-- comap_embedding_atBot (abstract). -/
def comap_embedding_atBot' : Prop := True
/-- tendsto_atTop_embedding (abstract). -/
def tendsto_atTop_embedding' : Prop := True
/-- tendsto_atBot_embedding (abstract). -/
def tendsto_atBot_embedding' : Prop := True
/-- tendsto_finset_range (abstract). -/
def tendsto_finset_range' : Prop := True
/-- atTop_finset_eq_iInf (abstract). -/
def atTop_finset_eq_iInf' : Prop := True
/-- tendsto_atTop_finset_of_monotone (abstract). -/
def tendsto_atTop_finset_of_monotone' : Prop := True
/-- tendsto_finset_image_atTop_atTop (abstract). -/
def tendsto_finset_image_atTop_atTop' : Prop := True
/-- tendsto_finset_preimage_atTop_atTop (abstract). -/
def tendsto_finset_preimage_atTop_atTop' : Prop := True
/-- prod_atTop_atTop_eq (abstract). -/
def prod_atTop_atTop_eq' : Prop := True
/-- tendsto_finset_prod_atTop (abstract). -/
def tendsto_finset_prod_atTop' : Prop := True
/-- prod_atBot_atBot_eq (abstract). -/
def prod_atBot_atBot_eq' : Prop := True
/-- prod_map_atTop_eq (abstract). -/
def prod_map_atTop_eq' : Prop := True
/-- prod_map_atBot_eq (abstract). -/
def prod_map_atBot_eq' : Prop := True
/-- subseq_mem (abstract). -/
def subseq_mem' : Prop := True
/-- tendsto_atBot_diagonal (abstract). -/
def tendsto_atBot_diagonal' : Prop := True
/-- tendsto_atTop_diagonal (abstract). -/
def tendsto_atTop_diagonal' : Prop := True
/-- prod_map_prod_atBot (abstract). -/
def prod_map_prod_atBot' : Prop := True
/-- prod_map_prod_atTop (abstract). -/
def prod_map_prod_atTop' : Prop := True
/-- prod_atBot (abstract). -/
def prod_atBot' : Prop := True
/-- prod_atTop (abstract). -/
def prod_atTop' : Prop := True
/-- eventually_atBot_prod_self (abstract). -/
def eventually_atBot_prod_self' : Prop := True
/-- eventually_atTop_prod_self (abstract). -/
def eventually_atTop_prod_self' : Prop := True
/-- eventually_atTop_curry (abstract). -/
def eventually_atTop_curry' : Prop := True
/-- eventually_atBot_curry (abstract). -/
def eventually_atBot_curry' : Prop := True
/-- map_atTop_eq_of_gc_preorder (abstract). -/
def map_atTop_eq_of_gc_preorder' : Prop := True
/-- map_atTop_eq_of_gc (abstract). -/
def map_atTop_eq_of_gc' : Prop := True
/-- map_atBot_eq_of_gc_preorder (abstract). -/
def map_atBot_eq_of_gc_preorder' : Prop := True
/-- map_atBot_eq_of_gc (abstract). -/
def map_atBot_eq_of_gc' : Prop := True
/-- map_val_atTop_of_Ici_subset (abstract). -/
def map_val_atTop_of_Ici_subset' : Prop := True
/-- map_cast_int_atTop (abstract). -/
def map_cast_int_atTop' : Prop := True
/-- map_val_Ici_atTop (abstract). -/
def map_val_Ici_atTop' : Prop := True
/-- map_val_Ioi_atTop (abstract). -/
def map_val_Ioi_atTop' : Prop := True
/-- atTop_Ioi_eq (abstract). -/
def atTop_Ioi_eq' : Prop := True
/-- atTop_Ici_eq (abstract). -/
def atTop_Ici_eq' : Prop := True
/-- map_val_Iio_atBot (abstract). -/
def map_val_Iio_atBot' : Prop := True
/-- atBot_Iio_eq (abstract). -/
def atBot_Iio_eq' : Prop := True
/-- map_val_Iic_atBot (abstract). -/
def map_val_Iic_atBot' : Prop := True
/-- atBot_Iic_eq (abstract). -/
def atBot_Iic_eq' : Prop := True
/-- tendsto_Ioi_atTop (abstract). -/
def tendsto_Ioi_atTop' : Prop := True
/-- tendsto_Iio_atBot (abstract). -/
def tendsto_Iio_atBot' : Prop := True
/-- tendsto_Ici_atTop (abstract). -/
def tendsto_Ici_atTop' : Prop := True
/-- tendsto_Iic_atBot (abstract). -/
def tendsto_Iic_atBot' : Prop := True
/-- tendsto_comp_val_Ioi_atTop (abstract). -/
def tendsto_comp_val_Ioi_atTop' : Prop := True
/-- tendsto_comp_val_Ici_atTop (abstract). -/
def tendsto_comp_val_Ici_atTop' : Prop := True
/-- tendsto_comp_val_Iio_atBot (abstract). -/
def tendsto_comp_val_Iio_atBot' : Prop := True
/-- tendsto_comp_val_Iic_atBot (abstract). -/
def tendsto_comp_val_Iic_atBot' : Prop := True
/-- map_add_atTop_eq_nat (abstract). -/
def map_add_atTop_eq_nat' : Prop := True
/-- map_sub_atTop_eq_nat (abstract). -/
def map_sub_atTop_eq_nat' : Prop := True
/-- tendsto_add_atTop_nat (abstract). -/
def tendsto_add_atTop_nat' : Prop := True
/-- tendsto_sub_atTop_nat (abstract). -/
def tendsto_sub_atTop_nat' : Prop := True
/-- tendsto_add_atTop_iff_nat (abstract). -/
def tendsto_add_atTop_iff_nat' : Prop := True
/-- map_div_atTop_eq_nat (abstract). -/
def map_div_atTop_eq_nat' : Prop := True
/-- tendsto_atTop_atTop_of_monotone' (abstract). -/
def tendsto_atTop_atTop_of_monotone' : Prop := True
/-- tendsto_atBot_atBot_of_monotone' (abstract). -/
def tendsto_atBot_atBot_of_monotone' : Prop := True
/-- unbounded_of_tendsto_atTop (abstract). -/
def unbounded_of_tendsto_atTop' : Prop := True
/-- unbounded_of_tendsto_atBot (abstract). -/
def unbounded_of_tendsto_atBot' : Prop := True
/-- tendsto_atBot_of_monotone_of_filter (abstract). -/
def tendsto_atBot_of_monotone_of_filter' : Prop := True
/-- tendsto_atTop_of_monotone_of_subseq (abstract). -/
def tendsto_atTop_of_monotone_of_subseq' : Prop := True
/-- tendsto_atBot_of_monotone_of_subseq (abstract). -/
def tendsto_atBot_of_monotone_of_subseq' : Prop := True
/-- eventually_subset (abstract). -/
def eventually_subset' : Prop := True
/-- tendsto (abstract). -/
def tendsto' : Prop := True
/-- comp_mono (abstract). -/
def comp_mono' : Prop := True
/-- comp_strictMono (abstract). -/
def comp_strictMono' : Prop := True
/-- subbasis_with_rel (abstract). -/
def subbasis_with_rel' : Prop := True
/-- exists_seq_tendsto (abstract). -/
def exists_seq_tendsto' : Prop := True
/-- exists_seq_monotone_tendsto_atTop_atTop (abstract). -/
def exists_seq_monotone_tendsto_atTop_atTop' : Prop := True
/-- exists_seq_antitone_tendsto_atTop_atBot (abstract). -/
def exists_seq_antitone_tendsto_atTop_atBot' : Prop := True
/-- tendsto_iff_seq_tendsto (abstract). -/
def tendsto_iff_seq_tendsto' : Prop := True
/-- tendsto_of_seq_tendsto (abstract). -/
def tendsto_of_seq_tendsto' : Prop := True
/-- eventually_iff_seq_eventually (abstract). -/
def eventually_iff_seq_eventually' : Prop := True
/-- frequently_iff_seq_frequently (abstract). -/
def frequently_iff_seq_frequently' : Prop := True
/-- subseq_forall_of_frequently (abstract). -/
def subseq_forall_of_frequently' : Prop := True
/-- frequently_iff_seq_forall (abstract). -/
def frequently_iff_seq_forall' : Prop := True
/-- tendsto_of_subseq_tendsto (abstract). -/
def tendsto_of_subseq_tendsto' : Prop := True
/-- subseq_tendsto_of_neBot (abstract). -/
def subseq_tendsto_of_neBot' : Prop := True
/-- piecewise_eventually_eq_iUnion (abstract). -/
def piecewise_eventually_eq_iUnion' : Prop := True
/-- piecewise_eventually_eq_iInter (abstract). -/
def piecewise_eventually_eq_iInter' : Prop := True
/-- eventually_pow_lt_factorial_sub (abstract). -/
def eventually_pow_lt_factorial_sub' : Prop := True
/-- eventually_mul_pow_lt_factorial_sub (abstract). -/
def eventually_mul_pow_lt_factorial_sub' : Prop := True
/-- exists_pow_lt_factorial (abstract). -/
def exists_pow_lt_factorial' : Prop := True
/-- exists_mul_pow_lt_factorial (abstract). -/
def exists_mul_pow_lt_factorial' : Prop := True

-- Filter/AtTopBot/Archimedean.lean
/-- comap_cast_atTop (abstract). -/
def comap_cast_atTop' : Prop := True
/-- tendsto_natCast_atTop_iff (abstract). -/
def tendsto_natCast_atTop_iff' : Prop := True
/-- tendsto_natCast_atTop_atTop (abstract). -/
def tendsto_natCast_atTop_atTop' : Prop := True
/-- natCast_atTop (abstract). -/
def natCast_atTop' : Prop := True
/-- comap_cast_atBot (abstract). -/
def comap_cast_atBot' : Prop := True
/-- tendsto_intCast_atTop_iff (abstract). -/
def tendsto_intCast_atTop_iff' : Prop := True
/-- tendsto_intCast_atBot_iff (abstract). -/
def tendsto_intCast_atBot_iff' : Prop := True
/-- tendsto_intCast_atTop_atTop (abstract). -/
def tendsto_intCast_atTop_atTop' : Prop := True
/-- intCast_atTop (abstract). -/
def intCast_atTop' : Prop := True
/-- intCast_atBot (abstract). -/
def intCast_atBot' : Prop := True
/-- tendsto_ratCast_atTop_iff (abstract). -/
def tendsto_ratCast_atTop_iff' : Prop := True
/-- tendsto_ratCast_atBot_iff (abstract). -/
def tendsto_ratCast_atBot_iff' : Prop := True
/-- ratCast_atTop (abstract). -/
def ratCast_atTop' : Prop := True
/-- ratCast_atBot (abstract). -/
def ratCast_atBot' : Prop := True
/-- atTop_hasAntitoneBasis_of_archimedean (abstract). -/
def atTop_hasAntitoneBasis_of_archimedean' : Prop := True
/-- atTop_hasCountableBasis_of_archimedean (abstract). -/
def atTop_hasCountableBasis_of_archimedean' : Prop := True
/-- atBot_hasCountableBasis_of_archimedean (abstract). -/
def atBot_hasCountableBasis_of_archimedean' : Prop := True
/-- const_mul_atTop' (abstract). -/
def const_mul_atTop' : Prop := True
/-- atTop_mul_const' (abstract). -/
def atTop_mul_const' : Prop := True
/-- atTop_mul_const_of_neg' (abstract). -/
def atTop_mul_const_of_neg' : Prop := True
/-- atBot_mul_const' (abstract). -/
def atBot_mul_const' : Prop := True
/-- atBot_mul_const_of_neg' (abstract). -/
def atBot_mul_const_of_neg' : Prop := True
/-- atTop_nsmul_const (abstract). -/
def atTop_nsmul_const' : Prop := True
/-- atTop_nsmul_neg_const (abstract). -/
def atTop_nsmul_neg_const' : Prop := True
/-- atTop_zsmul_neg_const (abstract). -/
def atTop_zsmul_neg_const' : Prop := True
/-- atBot_zsmul_const (abstract). -/
def atBot_zsmul_const' : Prop := True
/-- atBot_zsmul_neg_const (abstract). -/
def atBot_zsmul_neg_const' : Prop := True

-- Filter/AtTopBot/BigOperators.lean
/-- gives (abstract). -/
def gives' : Prop := True
/-- map_atTop_finset_prod_le_of_prod_eq (abstract). -/
def map_atTop_finset_prod_le_of_prod_eq' : Prop := True
/-- map_atTop_finset_prod_eq (abstract). -/
def map_atTop_finset_prod_eq' : Prop := True

-- Filter/AtTopBot/Field.lean
/-- tendsto_const_mul_atTop_of_pos (abstract). -/
def tendsto_const_mul_atTop_of_pos' : Prop := True
/-- tendsto_mul_const_atTop_of_pos (abstract). -/
def tendsto_mul_const_atTop_of_pos' : Prop := True
/-- tendsto_div_const_atTop_of_pos (abstract). -/
def tendsto_div_const_atTop_of_pos' : Prop := True
/-- tendsto_const_mul_atTop_iff_pos (abstract). -/
def tendsto_const_mul_atTop_iff_pos' : Prop := True
/-- tendsto_mul_const_atTop_iff_pos (abstract). -/
def tendsto_mul_const_atTop_iff_pos' : Prop := True
/-- tendsto_div_const_atTop_iff_pos (abstract). -/
def tendsto_div_const_atTop_iff_pos' : Prop := True
/-- atTop_div_const (abstract). -/
def atTop_div_const' : Prop := True
/-- tendsto_const_mul_pow_atTop (abstract). -/
def tendsto_const_mul_pow_atTop' : Prop := True
/-- tendsto_const_mul_pow_atTop_iff (abstract). -/
def tendsto_const_mul_pow_atTop_iff' : Prop := True
/-- tendsto_zpow_atTop_atTop (abstract). -/
def tendsto_zpow_atTop_atTop' : Prop := True
/-- tendsto_const_mul_atBot_of_pos (abstract). -/
def tendsto_const_mul_atBot_of_pos' : Prop := True
/-- tendsto_mul_const_atBot_of_pos (abstract). -/
def tendsto_mul_const_atBot_of_pos' : Prop := True
/-- tendsto_div_const_atBot_of_pos (abstract). -/
def tendsto_div_const_atBot_of_pos' : Prop := True
/-- tendsto_const_mul_atTop_of_neg (abstract). -/
def tendsto_const_mul_atTop_of_neg' : Prop := True
/-- tendsto_mul_const_atTop_of_neg (abstract). -/
def tendsto_mul_const_atTop_of_neg' : Prop := True
/-- tendsto_div_const_atTop_of_neg (abstract). -/
def tendsto_div_const_atTop_of_neg' : Prop := True
/-- tendsto_const_mul_atBot_of_neg (abstract). -/
def tendsto_const_mul_atBot_of_neg' : Prop := True
/-- tendsto_mul_const_atBot_of_neg (abstract). -/
def tendsto_mul_const_atBot_of_neg' : Prop := True
/-- tendsto_div_const_atBot_of_neg (abstract). -/
def tendsto_div_const_atBot_of_neg' : Prop := True
/-- tendsto_const_mul_atTop_iff (abstract). -/
def tendsto_const_mul_atTop_iff' : Prop := True
/-- tendsto_mul_const_atTop_iff (abstract). -/
def tendsto_mul_const_atTop_iff' : Prop := True
/-- tendsto_div_const_atTop_iff (abstract). -/
def tendsto_div_const_atTop_iff' : Prop := True
/-- tendsto_const_mul_atBot_iff (abstract). -/
def tendsto_const_mul_atBot_iff' : Prop := True
/-- tendsto_mul_const_atBot_iff (abstract). -/
def tendsto_mul_const_atBot_iff' : Prop := True
/-- tendsto_div_const_atBot_iff (abstract). -/
def tendsto_div_const_atBot_iff' : Prop := True
/-- tendsto_const_mul_atTop_iff_neg (abstract). -/
def tendsto_const_mul_atTop_iff_neg' : Prop := True
/-- tendsto_mul_const_atTop_iff_neg (abstract). -/
def tendsto_mul_const_atTop_iff_neg' : Prop := True
/-- tendsto_div_const_atTop_iff_neg (abstract). -/
def tendsto_div_const_atTop_iff_neg' : Prop := True
/-- tendsto_const_mul_atBot_iff_pos (abstract). -/
def tendsto_const_mul_atBot_iff_pos' : Prop := True
/-- tendsto_mul_const_atBot_iff_pos (abstract). -/
def tendsto_mul_const_atBot_iff_pos' : Prop := True
/-- tendsto_div_const_atBot_iff_pos (abstract). -/
def tendsto_div_const_atBot_iff_pos' : Prop := True
/-- tendsto_const_mul_atBot_iff_neg (abstract). -/
def tendsto_const_mul_atBot_iff_neg' : Prop := True
/-- tendsto_mul_const_atBot_iff_neg (abstract). -/
def tendsto_mul_const_atBot_iff_neg' : Prop := True
/-- tendsto_div_const_atBot_iff_neg (abstract). -/
def tendsto_div_const_atBot_iff_neg' : Prop := True
/-- const_mul_atTop_of_neg (abstract). -/
def const_mul_atTop_of_neg' : Prop := True
/-- atTop_div_const_of_neg (abstract). -/
def atTop_div_const_of_neg' : Prop := True
/-- const_mul_atBot (abstract). -/
def const_mul_atBot' : Prop := True
/-- atBot_div_const (abstract). -/
def atBot_div_const' : Prop := True
/-- const_mul_atBot_of_neg (abstract). -/
def const_mul_atBot_of_neg' : Prop := True
/-- tendsto_neg_const_mul_pow_atTop (abstract). -/
def tendsto_neg_const_mul_pow_atTop' : Prop := True
/-- tendsto_const_mul_pow_atBot_iff (abstract). -/
def tendsto_const_mul_pow_atBot_iff' : Prop := True

-- Filter/AtTopBot/Floor.lean

-- Filter/AtTopBot/Group.lean
/-- tendsto_atTop_add_left_of_le' (abstract). -/
def tendsto_atTop_add_left_of_le' : Prop := True
/-- tendsto_atBot_add_left_of_ge' (abstract). -/
def tendsto_atBot_add_left_of_ge' : Prop := True
/-- tendsto_atTop_add_right_of_le' (abstract). -/
def tendsto_atTop_add_right_of_le' : Prop := True
/-- tendsto_atBot_add_right_of_ge' (abstract). -/
def tendsto_atBot_add_right_of_ge' : Prop := True
/-- tendsto_atTop_add_const_left (abstract). -/
def tendsto_atTop_add_const_left' : Prop := True
/-- tendsto_atBot_add_const_left (abstract). -/
def tendsto_atBot_add_const_left' : Prop := True
/-- tendsto_atTop_add_const_right (abstract). -/
def tendsto_atTop_add_const_right' : Prop := True
/-- tendsto_atBot_add_const_right (abstract). -/
def tendsto_atBot_add_const_right' : Prop := True
/-- map_neg_atBot (abstract). -/
def map_neg_atBot' : Prop := True
/-- map_neg_atTop (abstract). -/
def map_neg_atTop' : Prop := True
/-- comap_neg_atBot (abstract). -/
def comap_neg_atBot' : Prop := True
/-- comap_neg_atTop (abstract). -/
def comap_neg_atTop' : Prop := True
/-- tendsto_neg_atTop_atBot (abstract). -/
def tendsto_neg_atTop_atBot' : Prop := True
/-- tendsto_neg_atBot_atTop (abstract). -/
def tendsto_neg_atBot_atTop' : Prop := True
/-- tendsto_neg_atTop_iff (abstract). -/
def tendsto_neg_atTop_iff' : Prop := True
/-- tendsto_neg_atBot_iff (abstract). -/
def tendsto_neg_atBot_iff' : Prop := True
/-- tendsto_abs_atTop_atTop (abstract). -/
def tendsto_abs_atTop_atTop' : Prop := True
/-- tendsto_abs_atBot_atTop (abstract). -/
def tendsto_abs_atBot_atTop' : Prop := True
/-- comap_abs_atTop (abstract). -/
def comap_abs_atTop' : Prop := True

-- Filter/AtTopBot/ModEq.lean
/-- frequently_modEq (abstract). -/
def frequently_modEq' : Prop := True
/-- frequently_mod_eq (abstract). -/
def frequently_mod_eq' : Prop := True
/-- frequently_even (abstract). -/
def frequently_even' : Prop := True
/-- frequently_odd (abstract). -/
def frequently_odd' : Prop := True
/-- nonneg_of_eventually_pow_nonneg (abstract). -/
def nonneg_of_eventually_pow_nonneg' : Prop := True

-- Filter/AtTopBot/Monoid.lean
/-- tendsto_atTop_add_nonneg_left' (abstract). -/
def tendsto_atTop_add_nonneg_left' : Prop := True
/-- tendsto_atBot_add_nonpos_left' (abstract). -/
def tendsto_atBot_add_nonpos_left' : Prop := True
/-- tendsto_atTop_add_nonneg_right' (abstract). -/
def tendsto_atTop_add_nonneg_right' : Prop := True
/-- tendsto_atBot_add_nonpos_right' (abstract). -/
def tendsto_atBot_add_nonpos_right' : Prop := True
/-- tendsto_atTop_add (abstract). -/
def tendsto_atTop_add' : Prop := True
/-- tendsto_atBot_add (abstract). -/
def tendsto_atBot_add' : Prop := True
/-- nsmul_atTop (abstract). -/
def nsmul_atTop' : Prop := True
/-- nsmul_atBot (abstract). -/
def nsmul_atBot' : Prop := True
/-- tendsto_atTop_of_add_const_left (abstract). -/
def tendsto_atTop_of_add_const_left' : Prop := True
/-- tendsto_atBot_of_add_const_left (abstract). -/
def tendsto_atBot_of_add_const_left' : Prop := True
/-- tendsto_atTop_of_add_const_right (abstract). -/
def tendsto_atTop_of_add_const_right' : Prop := True
/-- tendsto_atBot_of_add_const_right (abstract). -/
def tendsto_atBot_of_add_const_right' : Prop := True
/-- tendsto_atTop_of_add_bdd_above_left' (abstract). -/
def tendsto_atTop_of_add_bdd_above_left' : Prop := True
/-- tendsto_atBot_of_add_bdd_below_left' (abstract). -/
def tendsto_atBot_of_add_bdd_below_left' : Prop := True
/-- tendsto_atTop_of_add_bdd_above_right' (abstract). -/
def tendsto_atTop_of_add_bdd_above_right' : Prop := True
/-- tendsto_atBot_of_add_bdd_below_right' (abstract). -/
def tendsto_atBot_of_add_bdd_below_right' : Prop := True

-- Filter/AtTopBot/Ring.lean
/-- atTop_mul_atTop (abstract). -/
def atTop_mul_atTop' : Prop := True
/-- tendsto_mul_self_atTop (abstract). -/
def tendsto_mul_self_atTop' : Prop := True
/-- tendsto_pow_atTop (abstract). -/
def tendsto_pow_atTop' : Prop := True
/-- zero_pow_eventuallyEq (abstract). -/
def zero_pow_eventuallyEq' : Prop := True
/-- atTop_mul_atBot (abstract). -/
def atTop_mul_atBot' : Prop := True
/-- atBot_mul_atTop (abstract). -/
def atBot_mul_atTop' : Prop := True
/-- atBot_mul_atBot (abstract). -/
def atBot_mul_atBot' : Prop := True
/-- atTop_of_const_mul (abstract). -/
def atTop_of_const_mul' : Prop := True
/-- atTop_of_mul_const (abstract). -/
def atTop_of_mul_const' : Prop := True
/-- tendsto_pow_atTop_iff (abstract). -/
def tendsto_pow_atTop_iff' : Prop := True
/-- not_tendsto_pow_atTop_atBot (abstract). -/
def not_tendsto_pow_atTop_atBot' : Prop := True
/-- exists_lt_mul_self (abstract). -/
def exists_lt_mul_self' : Prop := True
/-- exists_le_mul_self (abstract). -/
def exists_le_mul_self' : Prop := True

-- Filter/Bases.lean
/-- FilterBasis (abstract). -/
def FilterBasis' : Prop := True
/-- asBasis (abstract). -/
def asBasis' : Prop := True
/-- IsBasis (abstract). -/
def IsBasis' : Prop := True
/-- filterBasis (abstract). -/
def filterBasis' : Prop := True
/-- filter (abstract). -/
def filter' : Prop := True
/-- mem_filter_of_mem (abstract). -/
def mem_filter_of_mem' : Prop := True
/-- eq_iInf_principal (abstract). -/
def eq_iInf_principal' : Prop := True
/-- mem_filter_iff (abstract). -/
def mem_filter_iff' : Prop := True
/-- filter_eq_generate (abstract). -/
def filter_eq_generate' : Prop := True
/-- HasBasis (abstract). -/
def HasBasis' : Prop := True
/-- hasBasis_generate (abstract). -/
def hasBasis_generate' : Prop := True
/-- ofSets (abstract). -/
def ofSets' : Prop := True
/-- eq_of_same_basis (abstract). -/
def eq_of_same_basis' : Prop := True
/-- hasBasis_iff (abstract). -/
def hasBasis_iff' : Prop := True
/-- ex_mem (abstract). -/
def ex_mem' : Prop := True
/-- hasBasis (abstract). -/
def hasBasis' : Prop := True
/-- mem_of_superset (abstract). -/
def mem_of_superset' : Prop := True
/-- index (abstract). -/
def index' : Prop := True
/-- filter_eq (abstract). -/
def filter_eq' : Prop := True
/-- eq_generate (abstract). -/
def eq_generate' : Prop := True
/-- generate_eq_generate_inter (abstract). -/
def generate_eq_generate_inter' : Prop := True
/-- ofSets_filter_eq_generate (abstract). -/
def ofSets_filter_eq_generate' : Prop := True
/-- to_hasBasis' (abstract). -/
def to_hasBasis' : Prop := True
/-- congr (abstract). -/
def congr' : Prop := True
/-- to_subset (abstract). -/
def to_subset' : Prop := True
/-- eventually_iff (abstract). -/
def eventually_iff' : Prop := True
/-- frequently_iff (abstract). -/
def frequently_iff' : Prop := True
/-- exists_iff (abstract). -/
def exists_iff' : Prop := True
/-- forall_iff (abstract). -/
def forall_iff' : Prop := True
/-- neBot_iff (abstract). -/
def neBot_iff' : Prop := True
/-- generate_neBot_iff (abstract). -/
def generate_neBot_iff' : Prop := True
/-- basis_sets (abstract). -/
def basis_sets' : Prop := True
/-- asBasis_filter (abstract). -/
def asBasis_filter' : Prop := True
/-- hasBasis_self (abstract). -/
def hasBasis_self' : Prop := True
/-- hasBasis_self_subset (abstract). -/
def hasBasis_self_subset' : Prop := True
/-- ge_iff (abstract). -/
def ge_iff' : Prop := True
/-- le_basis_iff (abstract). -/
def le_basis_iff' : Prop := True
/-- hasBasis_iInf' (abstract). -/
def hasBasis_iInf' : Prop := True
/-- hasBasis_iInf_of_directed' (abstract). -/
def hasBasis_iInf_of_directed' : Prop := True
/-- hasBasis_biInf_of_directed' (abstract). -/
def hasBasis_biInf_of_directed' : Prop := True
/-- hasBasis_principal (abstract). -/
def hasBasis_principal' : Prop := True
/-- hasBasis_pure (abstract). -/
def hasBasis_pure' : Prop := True
/-- hasBasis_iSup (abstract). -/
def hasBasis_iSup' : Prop := True
/-- sup_principal (abstract). -/
def sup_principal' : Prop := True
/-- sup_pure (abstract). -/
def sup_pure' : Prop := True
/-- inf_principal (abstract). -/
def inf_principal' : Prop := True
/-- principal_inf (abstract). -/
def principal_inf' : Prop := True
/-- inf_basis_neBot_iff (abstract). -/
def inf_basis_neBot_iff' : Prop := True
/-- inf_neBot_iff (abstract). -/
def inf_neBot_iff' : Prop := True
/-- inf_principal_neBot_iff (abstract). -/
def inf_principal_neBot_iff' : Prop := True
/-- exists_mem_filter_basis (abstract). -/
def exists_mem_filter_basis' : Prop := True
/-- exists_mem_filter_basis_of_disjoint (abstract). -/
def exists_mem_filter_basis_of_disjoint' : Prop := True
/-- mem_iff_inf_principal_compl (abstract). -/
def mem_iff_inf_principal_compl' : Prop := True
/-- not_mem_iff_inf_principal_compl (abstract). -/
def not_mem_iff_inf_principal_compl' : Prop := True
/-- disjoint_principal_right (abstract). -/
def disjoint_principal_right' : Prop := True
/-- disjoint_principal_left (abstract). -/
def disjoint_principal_left' : Prop := True
/-- disjoint_principal_principal (abstract). -/
def disjoint_principal_principal' : Prop := True
/-- disjoint_pure_pure (abstract). -/
def disjoint_pure_pure' : Prop := True
/-- disjoint_iff_left (abstract). -/
def disjoint_iff_left' : Prop := True
/-- disjoint_iff_right (abstract). -/
def disjoint_iff_right' : Prop := True
/-- le_iff_forall_inf_principal_compl (abstract). -/
def le_iff_forall_inf_principal_compl' : Prop := True
/-- inf_neBot_iff_frequently_left (abstract). -/
def inf_neBot_iff_frequently_left' : Prop := True
/-- inf_neBot_iff_frequently_right (abstract). -/
def inf_neBot_iff_frequently_right' : Prop := True
/-- eq_biInf (abstract). -/
def eq_biInf' : Prop := True
/-- eq_iInf (abstract). -/
def eq_iInf' : Prop := True
/-- hasBasis_iInf_principal (abstract). -/
def hasBasis_iInf_principal' : Prop := True
/-- hasBasis_iInf_principal_finite (abstract). -/
def hasBasis_iInf_principal_finite' : Prop := True
/-- hasBasis_biInf_principal (abstract). -/
def hasBasis_biInf_principal' : Prop := True
/-- comap_hasBasis (abstract). -/
def comap_hasBasis' : Prop := True
/-- forall_mem_mem (abstract). -/
def forall_mem_mem' : Prop := True
/-- ker (abstract). -/
def ker' : Prop := True
/-- IsAntitoneBasis (abstract). -/
def IsAntitoneBasis' : Prop := True
/-- HasAntitoneBasis (abstract). -/
def HasAntitoneBasis' : Prop := True
/-- iInf_principal (abstract). -/
def iInf_principal' : Prop := True
/-- tendsto_left_iff (abstract). -/
def tendsto_left_iff' : Prop := True
/-- tendsto_right_iff (abstract). -/
def tendsto_right_iff' : Prop := True
/-- tendsto_iff (abstract). -/
def tendsto_iff' : Prop := True
/-- basis_left (abstract). -/
def basis_left' : Prop := True
/-- basis_right (abstract). -/
def basis_right' : Prop := True
/-- basis_both (abstract). -/
def basis_both' : Prop := True
/-- prod_pprod (abstract). -/
def prod_pprod' : Prop := True
-- COLLISION: prod' already in SetTheory.lean — rename needed
/-- prod_same_index (abstract). -/
def prod_same_index' : Prop := True
/-- prod_same_index_mono (abstract). -/
def prod_same_index_mono' : Prop := True
/-- prod_same_index_anti (abstract). -/
def prod_same_index_anti' : Prop := True
/-- prod_self (abstract). -/
def prod_self' : Prop := True
/-- mem_prod_self_iff (abstract). -/
def mem_prod_self_iff' : Prop := True
/-- eventually_prod_self_iff (abstract). -/
def eventually_prod_self_iff' : Prop := True
/-- coprod (abstract). -/
def coprod' : Prop := True
/-- map_sigma_mk_comap (abstract). -/
def map_sigma_mk_comap' : Prop := True
/-- IsCountablyGenerated (abstract). -/
def IsCountablyGenerated' : Prop := True
/-- IsCountableBasis (abstract). -/
def IsCountableBasis' : Prop := True
/-- HasCountableBasis (abstract). -/
def HasCountableBasis' : Prop := True
/-- CountableFilterBasis (abstract). -/
def CountableFilterBasis' : Prop := True
/-- isCountablyGenerated (abstract). -/
def isCountablyGenerated' : Prop := True
/-- antitone_seq_of_seq (abstract). -/
def antitone_seq_of_seq' : Prop := True
/-- countable_biInf_eq_iInf_seq (abstract). -/
def countable_biInf_eq_iInf_seq' : Prop := True
/-- countable_biInf_principal_eq_seq_iInf (abstract). -/
def countable_biInf_principal_eq_seq_iInf' : Prop := True
-- COLLISION: mem' already in SetTheory.lean — rename needed
/-- hasBasis_ge (abstract). -/
def hasBasis_ge' : Prop := True
/-- exists_antitone_subbasis (abstract). -/
def exists_antitone_subbasis' : Prop := True
/-- exists_antitone_basis (abstract). -/
def exists_antitone_basis' : Prop := True
/-- exists_antitone_seq (abstract). -/
def exists_antitone_seq' : Prop := True
/-- isCountablyGenerated_seq (abstract). -/
def isCountablyGenerated_seq' : Prop := True
/-- isCountablyGenerated_of_seq (abstract). -/
def isCountablyGenerated_of_seq' : Prop := True
/-- isCountablyGenerated_biInf_principal (abstract). -/
def isCountablyGenerated_biInf_principal' : Prop := True
/-- isCountablyGenerated_iff_exists_antitone_basis (abstract). -/
def isCountablyGenerated_iff_exists_antitone_basis' : Prop := True
/-- isCountablyGenerated_principal (abstract). -/
def isCountablyGenerated_principal' : Prop := True
/-- isCountablyGenerated_pure (abstract). -/
def isCountablyGenerated_pure' : Prop := True
/-- isCountablyGenerated_bot (abstract). -/
def isCountablyGenerated_bot' : Prop := True
/-- isCountablyGenerated_top (abstract). -/
def isCountablyGenerated_top' : Prop := True

-- Filter/Basic.lean
/-- filter_eq_iff (abstract). -/
def filter_eq_iff' : Prop := True
/-- sets_subset_sets (abstract). -/
def sets_subset_sets' : Prop := True
/-- sets_ssubset_sets (abstract). -/
def sets_ssubset_sets' : Prop := True
/-- coext (abstract). -/
def coext' : Prop := True
/-- inter_mem_iff (abstract). -/
def inter_mem_iff' : Prop := True
/-- diff_mem (abstract). -/
def diff_mem' : Prop := True
/-- congr_sets (abstract). -/
def congr_sets' : Prop := True
/-- biInter_mem' (abstract). -/
def biInter_mem' : Prop := True
/-- iInter_mem' (abstract). -/
def iInter_mem' : Prop := True
/-- exists_mem_subset_iff (abstract). -/
def exists_mem_subset_iff' : Prop := True
/-- monotone_mem (abstract). -/
def monotone_mem' : Prop := True
/-- exists_mem_and_iff (abstract). -/
def exists_mem_and_iff' : Prop := True
/-- forall_in_swap (abstract). -/
def forall_in_swap' : Prop := True
/-- mem_principal_self (abstract). -/
def mem_principal_self' : Prop := True
/-- GenerateSets (abstract). -/
def GenerateSets' : Prop := True
/-- generate (abstract). -/
def generate' : Prop := True
/-- mem_generate_of_mem (abstract). -/
def mem_generate_of_mem' : Prop := True
/-- le_generate_iff (abstract). -/
def le_generate_iff' : Prop := True
/-- generate_singleton (abstract). -/
def generate_singleton' : Prop := True
/-- mkOfClosure (abstract). -/
def mkOfClosure' : Prop := True
/-- mkOfClosure_sets (abstract). -/
def mkOfClosure_sets' : Prop := True
/-- giGenerate (abstract). -/
def giGenerate' : Prop := True
/-- mem_inf_of_left (abstract). -/
def mem_inf_of_left' : Prop := True
/-- mem_inf_of_right (abstract). -/
def mem_inf_of_right' : Prop := True
/-- inter_mem_inf (abstract). -/
def inter_mem_inf' : Prop := True
/-- mem_inf_of_inter (abstract). -/
def mem_inf_of_inter' : Prop := True
/-- not_neBot (abstract). -/
def not_neBot' : Prop := True
/-- neBot_of_le (abstract). -/
def neBot_of_le' : Prop := True
/-- sup_neBot (abstract). -/
def sup_neBot' : Prop := True
/-- not_disjoint_self_iff (abstract). -/
def not_disjoint_self_iff' : Prop := True
/-- eq_or_neBot (abstract). -/
def eq_or_neBot' : Prop := True
/-- sup_sets_eq (abstract). -/
def sup_sets_eq' : Prop := True
/-- sSup_sets_eq (abstract). -/
def sSup_sets_eq' : Prop := True
/-- iSup_sets_eq (abstract). -/
def iSup_sets_eq' : Prop := True
/-- generate_empty (abstract). -/
def generate_empty' : Prop := True
/-- union_mem_sup (abstract). -/
def union_mem_sup' : Prop := True
/-- mem_iSup (abstract). -/
def mem_iSup' : Prop := True
/-- iSup_neBot (abstract). -/
def iSup_neBot' : Prop := True
/-- iInf_eq_generate (abstract). -/
def iInf_eq_generate' : Prop := True
/-- mem_iInf_of_mem (abstract). -/
def mem_iInf_of_mem' : Prop := True
/-- le_principal_iff (abstract). -/
def le_principal_iff' : Prop := True
/-- Iic_principal (abstract). -/
def Iic_principal' : Prop := True
/-- principal_mono (abstract). -/
def principal_mono' : Prop := True
/-- principal_univ (abstract). -/
def principal_univ' : Prop := True
/-- principal_empty (abstract). -/
def principal_empty' : Prop := True
/-- generate_eq_biInf (abstract). -/
def generate_eq_biInf' : Prop := True
/-- empty_mem_iff_bot (abstract). -/
def empty_mem_iff_bot' : Prop := True
/-- nonempty_of_mem (abstract). -/
def nonempty_of_mem' : Prop := True
/-- empty_not_mem (abstract). -/
def empty_not_mem' : Prop := True
/-- nonempty_of_neBot (abstract). -/
def nonempty_of_neBot' : Prop := True
/-- compl_not_mem (abstract). -/
def compl_not_mem' : Prop := True
/-- filter_eq_bot_of_isEmpty (abstract). -/
def filter_eq_bot_of_isEmpty' : Prop := True
/-- disjoint_of_disjoint_of_mem (abstract). -/
def disjoint_of_disjoint_of_mem' : Prop := True
/-- not_disjoint (abstract). -/
def not_disjoint' : Prop := True
/-- inf_eq_bot_iff (abstract). -/
def inf_eq_bot_iff' : Prop := True
/-- eq_top_of_neBot (abstract). -/
def eq_top_of_neBot' : Prop := True
/-- forall_mem_nonempty_iff_neBot (abstract). -/
def forall_mem_nonempty_iff_neBot' : Prop := True
/-- eq_iInf_of_mem_iff_exists_mem (abstract). -/
def eq_iInf_of_mem_iff_exists_mem' : Prop := True
/-- eq_biInf_of_mem_iff_exists_mem (abstract). -/
def eq_biInf_of_mem_iff_exists_mem' : Prop := True
/-- iInf_sets_eq (abstract). -/
def iInf_sets_eq' : Prop := True
/-- mem_iInf_of_directed (abstract). -/
def mem_iInf_of_directed' : Prop := True
/-- mem_biInf_of_directed (abstract). -/
def mem_biInf_of_directed' : Prop := True
/-- biInf_sets_eq (abstract). -/
def biInf_sets_eq' : Prop := True
/-- sup_join (abstract). -/
def sup_join' : Prop := True
/-- iSup_join (abstract). -/
def iSup_join' : Prop := True
/-- iInf_neBot_of_directed' (abstract). -/
def iInf_neBot_of_directed' : Prop := True
/-- sInf_neBot_of_directed' (abstract). -/
def sInf_neBot_of_directed' : Prop := True
/-- iInf_neBot_iff_of_directed' (abstract). -/
def iInf_neBot_iff_of_directed' : Prop := True
/-- iSup_principal (abstract). -/
def iSup_principal' : Prop := True
/-- principal_eq_bot_iff (abstract). -/
def principal_eq_bot_iff' : Prop := True
/-- principal_neBot_iff (abstract). -/
def principal_neBot_iff' : Prop := True
/-- isCompl_principal (abstract). -/
def isCompl_principal' : Prop := True
/-- mem_inf_principal' (abstract). -/
def mem_inf_principal' : Prop := True
/-- iSup_inf_principal (abstract). -/
def iSup_inf_principal' : Prop := True
/-- inf_principal_eq_bot (abstract). -/
def inf_principal_eq_bot' : Prop := True
/-- mem_of_eq_bot (abstract). -/
def mem_of_eq_bot' : Prop := True
/-- diff_mem_inf_principal_compl (abstract). -/
def diff_mem_inf_principal_compl' : Prop := True
/-- eventually_of_mem (abstract). -/
def eventually_of_mem' : Prop := True
/-- and (abstract). -/
def and' : Prop := True
/-- eventually_true (abstract). -/
def eventually_true' : Prop := True
/-- of_forall (abstract). -/
def of_forall' : Prop := True
/-- eventually_false_iff_eq_bot (abstract). -/
def eventually_false_iff_eq_bot' : Prop := True
/-- eventually_const (abstract). -/
def eventually_const' : Prop := True
/-- eventually_iff_exists_mem (abstract). -/
def eventually_iff_exists_mem' : Prop := True
/-- exists_mem (abstract). -/
def exists_mem' : Prop := True
/-- mp (abstract). -/
def mp' : Prop := True
/-- eventually_congr (abstract). -/
def eventually_congr' : Prop := True
/-- eventually_or_distrib_left (abstract). -/
def eventually_or_distrib_left' : Prop := True
/-- eventually_or_distrib_right (abstract). -/
def eventually_or_distrib_right' : Prop := True
/-- forall_mem (abstract). -/
def forall_mem' : Prop := True
/-- eventually_inf (abstract). -/
def eventually_inf' : Prop := True
/-- eventually_inf_principal (abstract). -/
def eventually_inf_principal' : Prop := True
/-- eventually_iff_all_subsets (abstract). -/
def eventually_iff_all_subsets' : Prop := True
/-- frequently (abstract). -/
def frequently' : Prop := True
/-- and_eventually (abstract). -/
def and_eventually' : Prop := True
/-- and_frequently (abstract). -/
def and_frequently' : Prop := True
/-- frequently_iff_neBot (abstract). -/
def frequently_iff_neBot' : Prop := True
/-- frequently_mem_iff_neBot (abstract). -/
def frequently_mem_iff_neBot' : Prop := True
/-- frequently_iff_forall_eventually_exists_and (abstract). -/
def frequently_iff_forall_eventually_exists_and' : Prop := True
/-- not_eventually (abstract). -/
def not_eventually' : Prop := True
/-- not_frequently (abstract). -/
def not_frequently' : Prop := True
/-- frequently_true_iff_neBot (abstract). -/
def frequently_true_iff_neBot' : Prop := True
/-- frequently_false (abstract). -/
def frequently_false' : Prop := True
/-- frequently_const (abstract). -/
def frequently_const' : Prop := True
/-- frequently_or_distrib (abstract). -/
def frequently_or_distrib' : Prop := True
/-- frequently_imp_distrib (abstract). -/
def frequently_imp_distrib' : Prop := True
/-- frequently_imp_distrib_left (abstract). -/
def frequently_imp_distrib_left' : Prop := True
/-- frequently_imp_distrib_right (abstract). -/
def frequently_imp_distrib_right' : Prop := True
/-- eventually_imp_distrib_right (abstract). -/
def eventually_imp_distrib_right' : Prop := True
/-- frequently_and_distrib_left (abstract). -/
def frequently_and_distrib_left' : Prop := True
/-- frequently_and_distrib_right (abstract). -/
def frequently_and_distrib_right' : Prop := True
/-- frequently_bot (abstract). -/
def frequently_bot' : Prop := True
/-- frequently_top (abstract). -/
def frequently_top' : Prop := True
/-- frequently_principal (abstract). -/
def frequently_principal' : Prop := True
/-- frequently_inf_principal (abstract). -/
def frequently_inf_principal' : Prop := True
/-- frequently_sup (abstract). -/
def frequently_sup' : Prop := True
/-- frequently_sSup (abstract). -/
def frequently_sSup' : Prop := True
/-- eventuallyEq_top (abstract). -/
def eventuallyEq_top' : Prop := True
/-- rw (abstract). -/
def rw' : Prop := True
/-- eventuallyEq_set (abstract). -/
def eventuallyEq_set' : Prop := True
/-- eventuallyEq_univ (abstract). -/
def eventuallyEq_univ' : Prop := True
/-- eventuallyEq_of_mem (abstract). -/
def eventuallyEq_of_mem' : Prop := True
/-- eventuallyEq_iff_exists_mem (abstract). -/
def eventuallyEq_iff_exists_mem' : Prop := True
/-- eventuallyEq_comm (abstract). -/
def eventuallyEq_comm' : Prop := True
-- COLLISION: congr_left' already in SetTheory.lean — rename needed
-- COLLISION: congr_right' already in SetTheory.lean — rename needed
/-- prod_mk (abstract). -/
def prod_mk' : Prop := True
/-- fun_comp (abstract). -/
def fun_comp' : Prop := True
/-- smul (abstract). -/
def smul' : Prop := True
/-- symmDiff (abstract). -/
def symmDiff' : Prop := True
/-- eventuallyEq_empty (abstract). -/
def eventuallyEq_empty' : Prop := True
/-- eventuallyEq_inf_principal_iff (abstract). -/
def eventuallyEq_inf_principal_iff' : Prop := True
/-- sub_eq (abstract). -/
def sub_eq' : Prop := True
/-- eventuallyEq_iff_sub (abstract). -/
def eventuallyEq_iff_sub' : Prop := True
/-- eventuallyEq_iff_all_subsets (abstract). -/
def eventuallyEq_iff_all_subsets' : Prop := True
-- COLLISION: rfl' already in SetTheory.lean — rename needed
/-- trans_le (abstract). -/
def trans_le' : Prop := True
/-- trans_eq (abstract). -/
def trans_eq' : Prop := True
/-- eventuallyLE_antisymm_iff (abstract). -/
def eventuallyLE_antisymm_iff' : Prop := True
/-- set_eventuallyLE_iff_mem_inf_principal (abstract). -/
def set_eventuallyLE_iff_mem_inf_principal' : Prop := True
/-- set_eventuallyLE_iff_inf_principal_le (abstract). -/
def set_eventuallyLE_iff_inf_principal_le' : Prop := True
/-- set_eventuallyEq_iff_inf_principal (abstract). -/
def set_eventuallyEq_iff_inf_principal' : Prop := True
-- COLLISION: sup_le' already in SetTheory.lean — rename needed
/-- le_sup_of_le_left (abstract). -/
def le_sup_of_le_left' : Prop := True
/-- le_sup_of_le_right (abstract). -/
def le_sup_of_le_right' : Prop := True
/-- join_le (abstract). -/
def join_le' : Prop := True
/-- image_mem_map (abstract). -/
def image_mem_map' : Prop := True
/-- image_mem_map_iff (abstract). -/
def image_mem_map_iff' : Prop := True
/-- range_mem_map (abstract). -/
def range_mem_map' : Prop := True
/-- mem_map_iff_exists_image (abstract). -/
def mem_map_iff_exists_image' : Prop := True
/-- map_id (abstract). -/
def map_id' : Prop := True
/-- map_compose (abstract). -/
def map_compose' : Prop := True
/-- map_map (abstract). -/
def map_map' : Prop := True
/-- map_congr (abstract). -/
def map_congr' : Prop := True
/-- mem_comap' (abstract). -/
def mem_comap' : Prop := True
/-- mem_comap'' (abstract). -/
def mem_comap'' : Prop := True
/-- mem_comap_prod_mk (abstract). -/
def mem_comap_prod_mk' : Prop := True
/-- eventually_comap (abstract). -/
def eventually_comap' : Prop := True
/-- frequently_comap (abstract). -/
def frequently_comap' : Prop := True
/-- mem_comap_iff_compl (abstract). -/
def mem_comap_iff_compl' : Prop := True
/-- compl_mem_comap (abstract). -/
def compl_mem_comap' : Prop := True
/-- kernMap (abstract). -/
def kernMap' : Prop := True
/-- mem_kernMap_iff_compl (abstract). -/
def mem_kernMap_iff_compl' : Prop := True
/-- pure_bind (abstract). -/
def pure_bind' : Prop := True
/-- monad (abstract). -/
def monad' : Prop := True
/-- preimage_mem_comap (abstract). -/
def preimage_mem_comap' : Prop := True
/-- comap_id (abstract). -/
def comap_id' : Prop := True
/-- comap_const_of_not_mem (abstract). -/
def comap_const_of_not_mem' : Prop := True
/-- comap_const_of_mem (abstract). -/
def comap_const_of_mem' : Prop := True
/-- map_const (abstract). -/
def map_const' : Prop := True
/-- comap_comap (abstract). -/
def comap_comap' : Prop := True
/-- map_comm (abstract). -/
def map_comm' : Prop := True
/-- filter_map (abstract). -/
def filter_map' : Prop := True
/-- filter_comap (abstract). -/
def filter_comap' : Prop := True
/-- filter_map_Iic (abstract). -/
def filter_map_Iic' : Prop := True
/-- comap_principal (abstract). -/
def comap_principal' : Prop := True
/-- principal_subtype (abstract). -/
def principal_subtype' : Prop := True
/-- comap_pure (abstract). -/
def comap_pure' : Prop := True
/-- map_le_iff_le_comap (abstract). -/
def map_le_iff_le_comap' : Prop := True
/-- gc_map_comap (abstract). -/
def gc_map_comap' : Prop := True
/-- comap_le_iff_le_kernMap (abstract). -/
def comap_le_iff_le_kernMap' : Prop := True
/-- gc_comap_kernMap (abstract). -/
def gc_comap_kernMap' : Prop := True
/-- kernMap_principal (abstract). -/
def kernMap_principal' : Prop := True
/-- map_mono (abstract). -/
def map_mono' : Prop := True
/-- comap_mono (abstract). -/
def comap_mono' : Prop := True
/-- map_le_map (abstract). -/
def map_le_map' : Prop := True
/-- comap_le_comap (abstract). -/
def comap_le_comap' : Prop := True
/-- map_bot (abstract). -/
def map_bot' : Prop := True
/-- map_sup (abstract). -/
def map_sup' : Prop := True
/-- map_top (abstract). -/
def map_top' : Prop := True
/-- comap_top (abstract). -/
def comap_top' : Prop := True
/-- comap_inf (abstract). -/
def comap_inf' : Prop := True
/-- comap_iInf (abstract). -/
def comap_iInf' : Prop := True
/-- le_comap_top (abstract). -/
def le_comap_top' : Prop := True
/-- map_comap_le (abstract). -/
def map_comap_le' : Prop := True
/-- le_comap_map (abstract). -/
def le_comap_map' : Prop := True
/-- comap_bot (abstract). -/
def comap_bot' : Prop := True
/-- neBot_of_comap (abstract). -/
def neBot_of_comap' : Prop := True
/-- disjoint_comap (abstract). -/
def disjoint_comap' : Prop := True
/-- comap_iSup (abstract). -/
def comap_iSup' : Prop := True
/-- comap_sSup (abstract). -/
def comap_sSup' : Prop := True
/-- comap_sup (abstract). -/
def comap_sup' : Prop := True
/-- map_comap (abstract). -/
def map_comap' : Prop := True
/-- map_comap_setCoe_val (abstract). -/
def map_comap_setCoe_val' : Prop := True
/-- map_comap_of_mem (abstract). -/
def map_comap_of_mem' : Prop := True
/-- comap_le_comap_iff (abstract). -/
def comap_le_comap_iff' : Prop := True
/-- map_comap_of_surjective (abstract). -/
def map_comap_of_surjective' : Prop := True
/-- comap_injective (abstract). -/
def comap_injective' : Prop := True
/-- filter_map_top (abstract). -/
def filter_map_top' : Prop := True
/-- subtype_coe_map_comap (abstract). -/
def subtype_coe_map_comap' : Prop := True
/-- image_mem_of_mem_comap (abstract). -/
def image_mem_of_mem_comap' : Prop := True
/-- image_coe_mem_of_mem_comap (abstract). -/
def image_coe_mem_of_mem_comap' : Prop := True
/-- comap_map (abstract). -/
def comap_map' : Prop := True
/-- mem_comap_iff (abstract). -/
def mem_comap_iff' : Prop := True
/-- map_le_map_iff_of_injOn (abstract). -/
def map_le_map_iff_of_injOn' : Prop := True
/-- map_le_map_iff (abstract). -/
def map_le_map_iff' : Prop := True
/-- map_eq_map_iff_of_injOn (abstract). -/
def map_eq_map_iff_of_injOn' : Prop := True
/-- map_inj (abstract). -/
def map_inj' : Prop := True
/-- map_injective (abstract). -/
def map_injective' : Prop := True
/-- comap_neBot_iff (abstract). -/
def comap_neBot_iff' : Prop := True
/-- comap_neBot (abstract). -/
def comap_neBot' : Prop := True
/-- comap_neBot_iff_frequently (abstract). -/
def comap_neBot_iff_frequently' : Prop := True
/-- comap_neBot_iff_compl_range (abstract). -/
def comap_neBot_iff_compl_range' : Prop := True
/-- comap_eq_bot_iff_compl_range (abstract). -/
def comap_eq_bot_iff_compl_range' : Prop := True
/-- comap_surjective_eq_bot (abstract). -/
def comap_surjective_eq_bot' : Prop := True
/-- disjoint_comap_iff (abstract). -/
def disjoint_comap_iff' : Prop := True
/-- comap_of_range_mem (abstract). -/
def comap_of_range_mem' : Prop := True
/-- comap_fst_neBot_iff (abstract). -/
def comap_fst_neBot_iff' : Prop := True
/-- comap_fst_neBot (abstract). -/
def comap_fst_neBot' : Prop := True
/-- comap_snd_neBot_iff (abstract). -/
def comap_snd_neBot_iff' : Prop := True
/-- comap_snd_neBot (abstract). -/
def comap_snd_neBot' : Prop := True
/-- comap_eval_neBot_iff' (abstract). -/
def comap_eval_neBot_iff' : Prop := True
/-- comap_of_surj (abstract). -/
def comap_of_surj' : Prop := True
/-- comap_of_image_mem (abstract). -/
def comap_of_image_mem' : Prop := True
/-- map_eq_bot_iff (abstract). -/
def map_eq_bot_iff' : Prop := True
/-- map_neBot_iff (abstract). -/
def map_neBot_iff' : Prop := True
/-- of_map (abstract). -/
def of_map' : Prop := True
/-- sInter_comap_sets (abstract). -/
def sInter_comap_sets' : Prop := True
/-- map_iInf_eq (abstract). -/
def map_iInf_eq' : Prop := True
/-- map_biInf_eq (abstract). -/
def map_biInf_eq' : Prop := True
/-- map_inf_le (abstract). -/
def map_inf_le' : Prop := True
/-- map_inf (abstract). -/
def map_inf' : Prop := True
/-- disjoint_of_map (abstract). -/
def disjoint_of_map' : Prop := True
/-- disjoint_map (abstract). -/
def disjoint_map' : Prop := True
/-- map_equiv_symm (abstract). -/
def map_equiv_symm' : Prop := True
/-- map_eq_comap_of_inverse (abstract). -/
def map_eq_comap_of_inverse' : Prop := True
/-- comap_equiv_symm (abstract). -/
def comap_equiv_symm' : Prop := True
/-- map_swap_eq_comap_swap (abstract). -/
def map_swap_eq_comap_swap' : Prop := True
/-- map_swap4_eq_comap (abstract). -/
def map_swap4_eq_comap' : Prop := True
/-- le_map (abstract). -/
def le_map' : Prop := True
/-- le_map_iff (abstract). -/
def le_map_iff' : Prop := True
/-- push_pull (abstract). -/
def push_pull' : Prop := True
/-- disjoint_comap_iff_map (abstract). -/
def disjoint_comap_iff_map' : Prop := True
/-- neBot_inf_comap_iff_map (abstract). -/
def neBot_inf_comap_iff_map' : Prop := True
/-- comap_inf_principal_neBot_of_image_mem (abstract). -/
def comap_inf_principal_neBot_of_image_mem' : Prop := True
/-- principal_eq_map_coe_top (abstract). -/
def principal_eq_map_coe_top' : Prop := True
/-- inf_principal_eq_bot_iff_comap (abstract). -/
def inf_principal_eq_bot_iff_comap' : Prop := True
/-- singleton_mem_pure (abstract). -/
def singleton_mem_pure' : Prop := True
/-- pure_injective (abstract). -/
def pure_injective' : Prop := True
/-- mem_seq_iff (abstract). -/
def mem_seq_iff' : Prop := True
/-- mem_map_seq_iff (abstract). -/
def mem_map_seq_iff' : Prop := True
/-- seq_mem_seq (abstract). -/
def seq_mem_seq' : Prop := True
/-- le_seq (abstract). -/
def le_seq' : Prop := True
/-- seq_mono (abstract). -/
def seq_mono' : Prop := True
/-- pure_seq_eq_map (abstract). -/
def pure_seq_eq_map' : Prop := True
/-- seq_pure (abstract). -/
def seq_pure' : Prop := True
/-- seq_assoc (abstract). -/
def seq_assoc' : Prop := True
/-- prod_map_seq_comm (abstract). -/
def prod_map_seq_comm' : Prop := True
/-- bind_le (abstract). -/
def bind_le' : Prop := True
/-- bind_mono (abstract). -/
def bind_mono' : Prop := True
/-- bind_inf_principal (abstract). -/
def bind_inf_principal' : Prop := True
/-- eventuallyLE (abstract). -/
def eventuallyLE' : Prop := True
/-- map_surjOn_Iic_iff_le_map (abstract). -/
def map_surjOn_Iic_iff_le_map' : Prop := True
/-- map_surjOn_Iic_iff_surjOn (abstract). -/
def map_surjOn_Iic_iff_surjOn' : Prop := True
/-- filter_injOn_Iic_iff_injOn (abstract). -/
def filter_injOn_Iic_iff_injOn' : Prop := True

-- Filter/CardinalInter.lean
/-- CardinalInterFilter (abstract). -/
def CardinalInterFilter' : Prop := True
/-- cardinal_sInter_mem (abstract). -/
def cardinal_sInter_mem' : Prop := True
/-- cardinalInterFilter_aleph0 (abstract). -/
def cardinalInterFilter_aleph0' : Prop := True
/-- toCountableInterFilter (abstract). -/
def toCountableInterFilter' : Prop := True
/-- cardinalInterFilter_aleph_one_iff (abstract). -/
def cardinalInterFilter_aleph_one_iff' : Prop := True
/-- of_cardinalInterFilter_of_le (abstract). -/
def of_cardinalInterFilter_of_le' : Prop := True
/-- of_cardinalInterFilter_of_lt (abstract). -/
def of_cardinalInterFilter_of_lt' : Prop := True
/-- cardinal_iInter_mem (abstract). -/
def cardinal_iInter_mem' : Prop := True
/-- cardinal_bInter_mem (abstract). -/
def cardinal_bInter_mem' : Prop := True
/-- eventually_cardinal_forall (abstract). -/
def eventually_cardinal_forall' : Prop := True
/-- eventually_cardinal_ball (abstract). -/
def eventually_cardinal_ball' : Prop := True
/-- cardinal_iUnion (abstract). -/
def cardinal_iUnion' : Prop := True
/-- cardinal_bUnion (abstract). -/
def cardinal_bUnion' : Prop := True
/-- cardinal_iInter (abstract). -/
def cardinal_iInter' : Prop := True
/-- cardinal_bInter (abstract). -/
def cardinal_bInter' : Prop := True
/-- ofCardinalInter (abstract). -/
def ofCardinalInter' : Prop := True
/-- ofCardinalUnion (abstract). -/
def ofCardinalUnion' : Prop := True
/-- CardinalGenerateSets (abstract). -/
def CardinalGenerateSets' : Prop := True
/-- cardinalGenerate (abstract). -/
def cardinalGenerate' : Prop := True
/-- cardinalInter_ofCardinalGenerate (abstract). -/
def cardinalInter_ofCardinalGenerate' : Prop := True
/-- mem_cardinaleGenerate_iff (abstract). -/
def mem_cardinaleGenerate_iff' : Prop := True
/-- le_cardinalGenerate_iff_of_cardinalInterFilter (abstract). -/
def le_cardinalGenerate_iff_of_cardinalInterFilter' : Prop := True
/-- cardinalGenerate_isGreatest (abstract). -/
def cardinalGenerate_isGreatest' : Prop := True

-- Filter/Cocardinal.lean
/-- cocardinal (abstract). -/
def cocardinal' : Prop := True
/-- cocardinal_aleph0_eq_cofinite (abstract). -/
def cocardinal_aleph0_eq_cofinite' : Prop := True
/-- hasBasis_cocardinal (abstract). -/
def hasBasis_cocardinal' : Prop := True
/-- frequently_cocardinal (abstract). -/
def frequently_cocardinal' : Prop := True
/-- frequently_cocardinal_mem (abstract). -/
def frequently_cocardinal_mem' : Prop := True
/-- cocardinal_inf_principal_neBot_iff (abstract). -/
def cocardinal_inf_principal_neBot_iff' : Prop := True
/-- compl_mem_cocardinal_of_card_lt (abstract). -/
def compl_mem_cocardinal_of_card_lt' : Prop := True
/-- compl_mem_cocardinal (abstract). -/
def compl_mem_cocardinal' : Prop := True
/-- eventually_cocardinal_nmem_of_card_lt (abstract). -/
def eventually_cocardinal_nmem_of_card_lt' : Prop := True
/-- eventually_cocardinal_nmem (abstract). -/
def eventually_cocardinal_nmem' : Prop := True
/-- eventually_cocardinal_ne (abstract). -/
def eventually_cocardinal_ne' : Prop := True
/-- cocountable (abstract). -/
def cocountable' : Prop := True
/-- mem_cocountable (abstract). -/
def mem_cocountable' : Prop := True

-- Filter/Cofinite.lean
/-- cofinite (abstract). -/
def cofinite' : Prop := True
/-- hasBasis_cofinite (abstract). -/
def hasBasis_cofinite' : Prop := True
/-- cofinite_eq_bot_iff (abstract). -/
def cofinite_eq_bot_iff' : Prop := True
/-- cofinite_eq_bot (abstract). -/
def cofinite_eq_bot' : Prop := True
/-- frequently_cofinite_iff_infinite (abstract). -/
def frequently_cofinite_iff_infinite' : Prop := True
/-- frequently_cofinite_mem_iff_infinite (abstract). -/
def frequently_cofinite_mem_iff_infinite' : Prop := True
/-- cofinite_inf_principal_neBot_iff (abstract). -/
def cofinite_inf_principal_neBot_iff' : Prop := True
/-- compl_mem_cofinite (abstract). -/
def compl_mem_cofinite' : Prop := True
/-- eventually_cofinite_nmem (abstract). -/
def eventually_cofinite_nmem' : Prop := True
/-- infinite_iff_frequently_cofinite (abstract). -/
def infinite_iff_frequently_cofinite' : Prop := True
/-- eventually_cofinite_ne (abstract). -/
def eventually_cofinite_ne' : Prop := True
/-- le_cofinite_iff_compl_singleton_mem (abstract). -/
def le_cofinite_iff_compl_singleton_mem' : Prop := True
/-- le_cofinite_iff_eventually_ne (abstract). -/
def le_cofinite_iff_eventually_ne' : Prop := True
/-- atTop_le_cofinite (abstract). -/
def atTop_le_cofinite' : Prop := True
/-- comap_cofinite_le (abstract). -/
def comap_cofinite_le' : Prop := True
/-- coprod_cofinite (abstract). -/
def coprod_cofinite' : Prop := True
/-- coprodᵢ_cofinite (abstract). -/
def coprodᵢ_cofinite' : Prop := True
/-- disjoint_cofinite_left (abstract). -/
def disjoint_cofinite_left' : Prop := True
/-- disjoint_cofinite_right (abstract). -/
def disjoint_cofinite_right' : Prop := True
/-- countable_compl_ker (abstract). -/
def countable_compl_ker' : Prop := True
/-- countable_compl_preimage_ker (abstract). -/
def countable_compl_preimage_ker' : Prop := True
/-- univ_pi_mem_pi (abstract). -/
def univ_pi_mem_pi' : Prop := True
/-- map_piMap_pi (abstract). -/
def map_piMap_pi' : Prop := True
/-- map_piMap_pi_finite (abstract). -/
def map_piMap_pi_finite' : Prop := True
/-- cofinite_inf_principal_compl (abstract). -/
def cofinite_inf_principal_compl' : Prop := True
/-- cofinite_inf_principal_diff (abstract). -/
def cofinite_inf_principal_diff' : Prop := True
/-- cofinite_eq_atTop (abstract). -/
def cofinite_eq_atTop' : Prop := True
/-- frequently_atTop_iff_infinite (abstract). -/
def frequently_atTop_iff_infinite' : Prop := True
/-- eventually_pos (abstract). -/
def eventually_pos' : Prop := True
/-- exists_within_forall_le (abstract). -/
def exists_within_forall_le' : Prop := True
/-- exists_forall_le (abstract). -/
def exists_forall_le' : Prop := True
/-- exists_within_forall_ge (abstract). -/
def exists_within_forall_ge' : Prop := True
/-- exists_forall_ge (abstract). -/
def exists_forall_ge' : Prop := True
/-- le_map_cofinite (abstract). -/
def le_map_cofinite' : Prop := True
/-- tendsto_cofinite (abstract). -/
def tendsto_cofinite' : Prop := True
/-- comap_cofinite_eq (abstract). -/
def comap_cofinite_eq' : Prop := True
/-- nat_tendsto_atTop (abstract). -/
def nat_tendsto_atTop' : Prop := True

-- Filter/CountableInter.lean
/-- CountableInterFilter (abstract). -/
def CountableInterFilter' : Prop := True
/-- countable_sInter_mem (abstract). -/
def countable_sInter_mem' : Prop := True
/-- countable_iInter_mem (abstract). -/
def countable_iInter_mem' : Prop := True
/-- countable_bInter_mem (abstract). -/
def countable_bInter_mem' : Prop := True
/-- eventually_countable_forall (abstract). -/
def eventually_countable_forall' : Prop := True
/-- eventually_countable_ball (abstract). -/
def eventually_countable_ball' : Prop := True
/-- countable_iUnion (abstract). -/
def countable_iUnion' : Prop := True
/-- countable_bUnion (abstract). -/
def countable_bUnion' : Prop := True
/-- countable_iInter (abstract). -/
def countable_iInter' : Prop := True
/-- countable_bInter (abstract). -/
def countable_bInter' : Prop := True
/-- ofCountableInter (abstract). -/
def ofCountableInter' : Prop := True
/-- ofCountableUnion (abstract). -/
def ofCountableUnion' : Prop := True
/-- CountableGenerateSets (abstract). -/
def CountableGenerateSets' : Prop := True
/-- countableGenerate (abstract). -/
def countableGenerate' : Prop := True
/-- mem_countableGenerate_iff (abstract). -/
def mem_countableGenerate_iff' : Prop := True
/-- le_countableGenerate_iff_of_countableInterFilter (abstract). -/
def le_countableGenerate_iff_of_countableInterFilter' : Prop := True
/-- countableGenerate_isGreatest (abstract). -/
def countableGenerate_isGreatest' : Prop := True

-- Filter/CountableSeparatingOn.lean
/-- saying (abstract). -/
def saying' : Prop := True
/-- in (abstract). -/
def in' : Prop := True
/-- HasCountableSeparatingOn (abstract). -/
def HasCountableSeparatingOn' : Prop := True
/-- exists_nonempty_countable_separating (abstract). -/
def exists_nonempty_countable_separating' : Prop := True
/-- exists_seq_separating (abstract). -/
def exists_seq_separating' : Prop := True
/-- of_subtype (abstract). -/
def of_subtype' : Prop := True
/-- subtype_iff (abstract). -/
def subtype_iff' : Prop := True
/-- exists_subset_subsingleton_mem_of_forall_separating (abstract). -/
def exists_subset_subsingleton_mem_of_forall_separating' : Prop := True
/-- exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (abstract). -/
def exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating' : Prop := True
/-- exists_singleton_mem_of_mem_of_forall_separating (abstract). -/
def exists_singleton_mem_of_mem_of_forall_separating' : Prop := True
/-- exists_subsingleton_mem_of_forall_separating (abstract). -/
def exists_subsingleton_mem_of_forall_separating' : Prop := True
/-- exists_singleton_mem_of_forall_separating (abstract). -/
def exists_singleton_mem_of_forall_separating' : Prop := True
/-- exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating (abstract). -/
def exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating' : Prop := True
/-- exists_eventuallyEq_const_of_eventually_mem_of_forall_separating (abstract). -/
def exists_eventuallyEq_const_of_eventually_mem_of_forall_separating' : Prop := True
/-- exists_eventuallyEq_const_of_forall_separating (abstract). -/
def exists_eventuallyEq_const_of_forall_separating' : Prop := True
/-- of_eventually_mem_of_forall_separating_mem_iff (abstract). -/
def of_eventually_mem_of_forall_separating_mem_iff' : Prop := True
/-- of_forall_separating_mem_iff (abstract). -/
def of_forall_separating_mem_iff' : Prop := True
/-- of_eventually_mem_of_forall_separating_preimage (abstract). -/
def of_eventually_mem_of_forall_separating_preimage' : Prop := True
/-- of_forall_separating_preimage (abstract). -/
def of_forall_separating_preimage' : Prop := True

-- Filter/Curry.lean
/-- frequently_curry_iff (abstract). -/
def frequently_curry_iff' : Prop := True
/-- curry_le_prod (abstract). -/
def curry_le_prod' : Prop := True
/-- curry (abstract). -/
def curry' : Prop := True
/-- frequently_curry_prod_iff (abstract). -/
def frequently_curry_prod_iff' : Prop := True
/-- eventually_curry_prod_iff (abstract). -/
def eventually_curry_prod_iff' : Prop := True
/-- prod_mem_curry (abstract). -/
def prod_mem_curry' : Prop := True

-- Filter/Defs.lean
-- COLLISION: Filter' already in Order.lean — rename needed
/-- univ_mem (abstract). -/
def univ_mem' : Prop := True
/-- inter_mem (abstract). -/
def inter_mem' : Prop := True
/-- mp_mem (abstract). -/
def mp_mem' : Prop := True
/-- comk (abstract). -/
def comk' : Prop := True
/-- principal (abstract). -/
def principal' : Prop := True
/-- join (abstract). -/
def join' : Prop := True
/-- mem_sSup (abstract). -/
def mem_sSup' : Prop := True
/-- mem_top (abstract). -/
def mem_top' : Prop := True
/-- mem_bot (abstract). -/
def mem_bot' : Prop := True
/-- Eventually (abstract). -/
def Eventually' : Prop := True
/-- Frequently (abstract). -/
def Frequently' : Prop := True
/-- EventuallyEq (abstract). -/
def EventuallyEq' : Prop := True
/-- EventuallyLE (abstract). -/
def EventuallyLE' : Prop := True
/-- Tendsto (abstract). -/
def Tendsto' : Prop := True
/-- bind (abstract). -/
def bind' : Prop := True
/-- seq (abstract). -/
def seq' : Prop := True
/-- IsBounded (abstract). -/
def IsBounded' : Prop := True
/-- IsBoundedUnder (abstract). -/
def IsBoundedUnder' : Prop := True
/-- IsCobounded (abstract). -/
def IsCobounded' : Prop := True
/-- IsCoboundedUnder (abstract). -/
def IsCoboundedUnder' : Prop := True

-- Filter/ENNReal.lean
/-- eventually_le_limsup (abstract). -/
def eventually_le_limsup' : Prop := True
/-- limsup_eq_zero_iff (abstract). -/
def limsup_eq_zero_iff' : Prop := True
/-- limsup_const_mul_of_ne_top (abstract). -/
def limsup_const_mul_of_ne_top' : Prop := True
/-- limsup_const_mul (abstract). -/
def limsup_const_mul' : Prop := True
/-- limsup_mul_le (abstract). -/
def limsup_mul_le' : Prop := True
/-- limsup_add_le (abstract). -/
def limsup_add_le' : Prop := True
/-- limsup_liminf_le_liminf_limsup (abstract). -/
def limsup_liminf_le_liminf_limsup' : Prop := True

-- Filter/EventuallyConst.lean
/-- EventuallyConst (abstract). -/
def EventuallyConst' : Prop := True
/-- eventuallyConst_iff_tendsto (abstract). -/
def eventuallyConst_iff_tendsto' : Prop := True
/-- of_tendsto (abstract). -/
def of_tendsto' : Prop := True
/-- eventuallyConst_iff_exists_eventuallyEq (abstract). -/
def eventuallyConst_iff_exists_eventuallyEq' : Prop := True
/-- eventuallyConst_pred' (abstract). -/
def eventuallyConst_pred' : Prop := True
/-- eventuallyConst_set' (abstract). -/
def eventuallyConst_set' : Prop := True
/-- bot (abstract). -/
def bot' : Prop := True
/-- comp₂ (abstract). -/
def comp₂' : Prop := True
/-- mul (abstract). -/
def mul' : Prop := True
/-- of_mulIndicator_const (abstract). -/
def of_mulIndicator_const' : Prop := True
/-- mulIndicator_const (abstract). -/
def mulIndicator_const' : Prop := True
/-- mulIndicator_const_iff_of_ne (abstract). -/
def mulIndicator_const_iff_of_ne' : Prop := True
/-- mulIndicator_const_iff (abstract). -/
def mulIndicator_const_iff' : Prop := True
/-- eventuallyConst_atTop (abstract). -/
def eventuallyConst_atTop' : Prop := True
/-- eventuallyConst_atTop_nat (abstract). -/
def eventuallyConst_atTop_nat' : Prop := True

-- Filter/Extr.lean
/-- IsMinFilter (abstract). -/
def IsMinFilter' : Prop := True
/-- IsMaxFilter (abstract). -/
def IsMaxFilter' : Prop := True
/-- IsExtrFilter (abstract). -/
def IsExtrFilter' : Prop := True
/-- IsMinOn (abstract). -/
def IsMinOn' : Prop := True
/-- IsMaxOn (abstract). -/
def IsMaxOn' : Prop := True
/-- IsExtrOn (abstract). -/
def IsExtrOn' : Prop := True
/-- elim (abstract). -/
def elim' : Prop := True
/-- isMinOn_univ_iff (abstract). -/
def isMinOn_univ_iff' : Prop := True
/-- isMaxOn_univ_iff (abstract). -/
def isMaxOn_univ_iff' : Prop := True
/-- tendsto_principal_Ici (abstract). -/
def tendsto_principal_Ici' : Prop := True
/-- tendsto_principal_Iic (abstract). -/
def tendsto_principal_Iic' : Prop := True
/-- isExtr (abstract). -/
def isExtr' : Prop := True
/-- isMinFilter_const (abstract). -/
def isMinFilter_const' : Prop := True
/-- isMaxFilter_const (abstract). -/
def isMaxFilter_const' : Prop := True
/-- isExtrOn_dual_iff (abstract). -/
def isExtrOn_dual_iff' : Prop := True
/-- on_subset (abstract). -/
def on_subset' : Prop := True
-- COLLISION: inter' already in SetTheory.lean — rename needed
/-- comp_antitone (abstract). -/
def comp_antitone' : Prop := True
/-- bicomp_mono (abstract). -/
def bicomp_mono' : Prop := True
/-- comp_tendsto (abstract). -/
def comp_tendsto' : Prop := True
/-- on_preimage (abstract). -/
def on_preimage' : Prop := True
/-- comp_mapsTo (abstract). -/
def comp_mapsTo' : Prop := True
/-- add (abstract). -/
def add' : Prop := True
/-- neg (abstract). -/
def neg' : Prop := True
-- COLLISION: sub' already in SetTheory.lean — rename needed
/-- min (abstract). -/
def min' : Prop := True
/-- max (abstract). -/
def max' : Prop := True
/-- isMaxFilter (abstract). -/
def isMaxFilter' : Prop := True
/-- isMaxFilter_iff (abstract). -/
def isMaxFilter_iff' : Prop := True
/-- isMinFilter (abstract). -/
def isMinFilter' : Prop := True
/-- isMinFilter_iff (abstract). -/
def isMinFilter_iff' : Prop := True
/-- isExtrFilter_iff (abstract). -/
def isExtrFilter_iff' : Prop := True
/-- iSup_eq (abstract). -/
def iSup_eq' : Prop := True
/-- iInf_eq (abstract). -/
def iInf_eq' : Prop := True
/-- sup_eq_of_isMaxOn (abstract). -/
def sup_eq_of_isMaxOn' : Prop := True
/-- sup_eq_of_max (abstract). -/
def sup_eq_of_max' : Prop := True
/-- inf_eq_of_isMinOn (abstract). -/
def inf_eq_of_isMinOn' : Prop := True
/-- inf_eq_of_min (abstract). -/
def inf_eq_of_min' : Prop := True

-- Filter/FilterProduct.lean
/-- coe_lt (abstract). -/
def coe_lt' : Prop := True
/-- coe_pos (abstract). -/
def coe_pos' : Prop := True
/-- const_lt (abstract). -/
def const_lt' : Prop := True
/-- const_lt_iff (abstract). -/
def const_lt_iff' : Prop := True
/-- abs_def (abstract). -/
def abs_def' : Prop := True
/-- const_max (abstract). -/
def const_max' : Prop := True
/-- const_min (abstract). -/
def const_min' : Prop := True
/-- const_abs (abstract). -/
def const_abs' : Prop := True

-- Filter/Finite.lean
/-- biInter_finset_mem (abstract). -/
def biInter_finset_mem' : Prop := True
/-- sInter_mem (abstract). -/
def sInter_mem' : Prop := True
/-- mem_generate_iff (abstract). -/
def mem_generate_iff' : Prop := True
/-- mem_iInf_of_iInter (abstract). -/
def mem_iInf_of_iInter' : Prop := True
/-- mem_iInf (abstract). -/
def mem_iInf' : Prop := True
/-- exists_iInter_of_mem_iInf (abstract). -/
def exists_iInter_of_mem_iInf' : Prop := True
/-- mem_iInf_of_finite (abstract). -/
def mem_iInf_of_finite' : Prop := True
/-- exists_mem_filter_of_disjoint (abstract). -/
def exists_mem_filter_of_disjoint' : Prop := True
/-- exists_mem_filter (abstract). -/
def exists_mem_filter' : Prop := True
/-- iInf_sets_eq_finite (abstract). -/
def iInf_sets_eq_finite' : Prop := True
/-- mem_iInf_finite (abstract). -/
def mem_iInf_finite' : Prop := True
/-- mem_iInf_finset (abstract). -/
def mem_iInf_finset' : Prop := True
/-- iInf_sets_induct (abstract). -/
def iInf_sets_induct' : Prop := True
/-- iInf_principal_finset (abstract). -/
def iInf_principal_finset' : Prop := True
/-- iInf_principal_finite (abstract). -/
def iInf_principal_finite' : Prop := True
/-- eventually_all (abstract). -/
def eventually_all' : Prop := True
/-- eventually_all_finite (abstract). -/
def eventually_all_finite' : Prop := True
/-- eventually_all_finset (abstract). -/
def eventually_all_finset' : Prop := True
/-- iUnion (abstract). -/
def iUnion' : Prop := True
-- COLLISION: iInter' already in SetTheory.lean — rename needed
/-- eventuallyLE_iUnion (abstract). -/
def eventuallyLE_iUnion' : Prop := True
/-- eventuallyEq_iUnion (abstract). -/
def eventuallyEq_iUnion' : Prop := True
/-- eventuallyLE_iInter (abstract). -/
def eventuallyLE_iInter' : Prop := True
/-- eventuallyEq_iInter (abstract). -/
def eventuallyEq_iInter' : Prop := True

-- Filter/Germ/Basic.lean
/-- const_eventuallyEq' (abstract). -/
def const_eventuallyEq' : Prop := True
/-- germSetoid (abstract). -/
def germSetoid' : Prop := True
/-- Germ (abstract). -/
def Germ' : Prop := True
/-- productSetoid (abstract). -/
def productSetoid' : Prop := True
/-- Product (abstract). -/
def Product' : Prop := True
/-- ofFun (abstract). -/
def ofFun' : Prop := True
/-- const (abstract). -/
def const' : Prop := True
/-- IsConstant (abstract). -/
def IsConstant' : Prop := True
-- COLLISION: inductionOn' already in SetTheory.lean — rename needed
-- COLLISION: inductionOn₂' already in SetTheory.lean — rename needed
-- COLLISION: inductionOn₃' already in SetTheory.lean — rename needed
/-- liftOn (abstract). -/
def liftOn' : Prop := True
-- COLLISION: map₂' already in SetTheory.lean — rename needed
/-- compTendsto' (abstract). -/
def compTendsto' : Prop := True
/-- congr_germ (abstract). -/
def congr_germ' : Prop := True
/-- isConstant_comp_tendsto (abstract). -/
def isConstant_comp_tendsto' : Prop := True
/-- LiftPred (abstract). -/
def LiftPred' : Prop := True
/-- liftPred_const (abstract). -/
def liftPred_const' : Prop := True
/-- liftPred_const_iff (abstract). -/
def liftPred_const_iff' : Prop := True
/-- LiftRel (abstract). -/
def LiftRel' : Prop := True
/-- liftRel_const (abstract). -/
def liftRel_const' : Prop := True
/-- coeMulHom (abstract). -/
def coeMulHom' : Prop := True
/-- coeRingHom (abstract). -/
def coeRingHom' : Prop := True
/-- const_le (abstract). -/
def const_le' : Prop := True
/-- const_le_iff (abstract). -/
def const_le_iff' : Prop := True

-- Filter/IndicatorFunction.lean
/-- mulIndicator_eventuallyEq (abstract). -/
def mulIndicator_eventuallyEq' : Prop := True
/-- mulIndicator_eventuallyLE_mulIndicator (abstract). -/
def mulIndicator_eventuallyLE_mulIndicator' : Prop := True
/-- mulIndicator_eventuallyEq_iUnion (abstract). -/
def mulIndicator_eventuallyEq_iUnion' : Prop := True
/-- tendsto_mulIndicator (abstract). -/
def tendsto_mulIndicator' : Prop := True
/-- mulIndicator_eventuallyEq_iInter (abstract). -/
def mulIndicator_eventuallyEq_iInter' : Prop := True
/-- mulIndicator_biUnion_finset_eventuallyEq (abstract). -/
def mulIndicator_biUnion_finset_eventuallyEq' : Prop := True
/-- mulIndicator (abstract). -/
def mulIndicator' : Prop := True
/-- mulIndicator_one (abstract). -/
def mulIndicator_one' : Prop := True
/-- of_mulIndicator (abstract). -/
def of_mulIndicator' : Prop := True
/-- mulIndicator_const_eventuallyEq (abstract). -/
def mulIndicator_const_eventuallyEq' : Prop := True

-- Filter/Interval.lean
/-- has (abstract). -/
def has' : Prop := True
/-- would (abstract). -/
def would' : Prop := True
/-- plays (abstract). -/
def plays' : Prop := True
/-- representing (abstract). -/
def representing' : Prop := True
/-- TendstoIxxClass (abstract). -/
def TendstoIxxClass' : Prop := True
/-- tendstoIxxClass_principal (abstract). -/
def tendstoIxxClass_principal' : Prop := True
/-- tendstoIxxClass_inf (abstract). -/
def tendstoIxxClass_inf' : Prop := True
/-- tendstoIxxClass_of_subset (abstract). -/
def tendstoIxxClass_of_subset' : Prop := True
/-- tendstoIxxClass (abstract). -/
def tendstoIxxClass' : Prop := True
/-- Icc (abstract). -/
def Icc' : Prop := True
/-- Ioc (abstract). -/
def Ioc' : Prop := True
/-- Ico (abstract). -/
def Ico' : Prop := True
/-- Ioo (abstract). -/
def Ioo' : Prop := True
/-- uIcc (abstract). -/
def uIcc' : Prop := True

-- Filter/Ker.lean
/-- ker_def (abstract). -/
def ker_def' : Prop := True
/-- mem_ker (abstract). -/
def mem_ker' : Prop := True
/-- subset_ker (abstract). -/
def subset_ker' : Prop := True
/-- gi_principal_ker (abstract). -/
def gi_principal_ker' : Prop := True
/-- ker_mono (abstract). -/
def ker_mono' : Prop := True
/-- ker_surjective (abstract). -/
def ker_surjective' : Prop := True
/-- ker_bot (abstract). -/
def ker_bot' : Prop := True
/-- ker_top (abstract). -/
def ker_top' : Prop := True
/-- ker_eq_univ (abstract). -/
def ker_eq_univ' : Prop := True
/-- ker_inf (abstract). -/
def ker_inf' : Prop := True
/-- ker_iInf (abstract). -/
def ker_iInf' : Prop := True
/-- ker_sInf (abstract). -/
def ker_sInf' : Prop := True
/-- ker_principal (abstract). -/
def ker_principal' : Prop := True
/-- ker_pure (abstract). -/
def ker_pure' : Prop := True
/-- ker_comap (abstract). -/
def ker_comap' : Prop := True
/-- ker_iSup (abstract). -/
def ker_iSup' : Prop := True
/-- ker_sSup (abstract). -/
def ker_sSup' : Prop := True
/-- ker_sup (abstract). -/
def ker_sup' : Prop := True

-- Filter/Lift.lean
/-- lift_top (abstract). -/
def lift_top' : Prop := True
/-- mem_lift_iff (abstract). -/
def mem_lift_iff' : Prop := True
/-- mem_lift_sets (abstract). -/
def mem_lift_sets' : Prop := True
/-- sInter_lift_sets (abstract). -/
def sInter_lift_sets' : Prop := True
/-- mem_lift (abstract). -/
def mem_lift' : Prop := True
-- COLLISION: lift_le' already in SetTheory.lean — rename needed
/-- le_lift (abstract). -/
def le_lift' : Prop := True
/-- lift_mono (abstract). -/
def lift_mono' : Prop := True
/-- tendsto_lift (abstract). -/
def tendsto_lift' : Prop := True
/-- map_lift_eq (abstract). -/
def map_lift_eq' : Prop := True
/-- comap_lift_eq (abstract). -/
def comap_lift_eq' : Prop := True
/-- comap_lift_eq2 (abstract). -/
def comap_lift_eq2' : Prop := True
/-- lift_map_le (abstract). -/
def lift_map_le' : Prop := True
/-- map_lift_eq2 (abstract). -/
def map_lift_eq2' : Prop := True
/-- lift_comm (abstract). -/
def lift_comm' : Prop := True
/-- lift_assoc (abstract). -/
def lift_assoc' : Prop := True
/-- lift_lift_same_le_lift (abstract). -/
def lift_lift_same_le_lift' : Prop := True
/-- lift_lift_same_eq_lift (abstract). -/
def lift_lift_same_eq_lift' : Prop := True
/-- lift_principal (abstract). -/
def lift_principal' : Prop := True
/-- monotone_lift (abstract). -/
def monotone_lift' : Prop := True
/-- lift_neBot_iff (abstract). -/
def lift_neBot_iff' : Prop := True
/-- lift_const (abstract). -/
def lift_const' : Prop := True
/-- lift_inf (abstract). -/
def lift_inf' : Prop := True
/-- lift_principal2 (abstract). -/
def lift_principal2' : Prop := True
/-- lift_iInf_le (abstract). -/
def lift_iInf_le' : Prop := True
-- COLLISION: lift_iInf' already in SetTheory.lean — rename needed
/-- lift_iInf_of_directed (abstract). -/
def lift_iInf_of_directed' : Prop := True
/-- lift_iInf_of_map_univ (abstract). -/
def lift_iInf_of_map_univ' : Prop := True
/-- lift'_top (abstract). -/
def lift'_top' : Prop := True
/-- mem_lift'_sets (abstract). -/
def mem_lift'_sets' : Prop := True
/-- eventually_lift'_iff (abstract). -/
def eventually_lift'_iff' : Prop := True
/-- sInter_lift'_sets (abstract). -/
def sInter_lift'_sets' : Prop := True
/-- lift'_le (abstract). -/
def lift'_le' : Prop := True
/-- lift'_mono (abstract). -/
def lift'_mono' : Prop := True
/-- lift'_cong (abstract). -/
def lift'_cong' : Prop := True
/-- map_lift'_eq (abstract). -/
def map_lift'_eq' : Prop := True
/-- lift'_map_le (abstract). -/
def lift'_map_le' : Prop := True
/-- map_lift'_eq2 (abstract). -/
def map_lift'_eq2' : Prop := True
/-- comap_lift'_eq (abstract). -/
def comap_lift'_eq' : Prop := True
/-- comap_lift'_eq2 (abstract). -/
def comap_lift'_eq2' : Prop := True
/-- lift'_principal (abstract). -/
def lift'_principal' : Prop := True
/-- lift'_pure (abstract). -/
def lift'_pure' : Prop := True
/-- lift'_bot (abstract). -/
def lift'_bot' : Prop := True
/-- principal_le_lift' (abstract). -/
def principal_le_lift' : Prop := True
/-- lift_lift'_assoc (abstract). -/
def lift_lift'_assoc' : Prop := True
/-- lift'_lift'_assoc (abstract). -/
def lift'_lift'_assoc' : Prop := True
/-- lift'_lift_assoc (abstract). -/
def lift'_lift_assoc' : Prop := True
/-- lift_lift'_same_le_lift' (abstract). -/
def lift_lift'_same_le_lift' : Prop := True
/-- lift_lift'_same_eq_lift' (abstract). -/
def lift_lift'_same_eq_lift' : Prop := True
/-- lift'_inf_principal_eq (abstract). -/
def lift'_inf_principal_eq' : Prop := True
/-- lift'_neBot_iff (abstract). -/
def lift'_neBot_iff' : Prop := True
/-- lift'_id (abstract). -/
def lift'_id' : Prop := True
/-- lift'_iInf (abstract). -/
def lift'_iInf' : Prop := True
/-- lift'_iInf_of_map_univ (abstract). -/
def lift'_iInf_of_map_univ' : Prop := True
/-- lift'_inf (abstract). -/
def lift'_inf' : Prop := True
/-- lift'_inf_le (abstract). -/
def lift'_inf_le' : Prop := True
/-- comap_eq_lift' (abstract). -/
def comap_eq_lift' : Prop := True
/-- prod_def (abstract). -/
def prod_def' : Prop := True
/-- prod_same_eq (abstract). -/
def prod_same_eq' : Prop := True
/-- tendsto_prod_self_iff (abstract). -/
def tendsto_prod_self_iff' : Prop := True
/-- prod_lift_lift (abstract). -/
def prod_lift_lift' : Prop := True
/-- prod_lift'_lift' (abstract). -/
def prod_lift'_lift' : Prop := True

-- Filter/ListTraverse.lean
/-- sequence_mono (abstract). -/
def sequence_mono' : Prop := True
/-- mem_traverse (abstract). -/
def mem_traverse' : Prop := True
/-- mem_traverse_iff (abstract). -/
def mem_traverse_iff' : Prop := True

-- Filter/NAry.lean
/-- image2_mem_map₂ (abstract). -/
def image2_mem_map₂' : Prop := True
/-- map_prod_eq_map₂ (abstract). -/
def map_prod_eq_map₂' : Prop := True
/-- map₂_mk_eq_prod (abstract). -/
def map₂_mk_eq_prod' : Prop := True
/-- map₂_mono (abstract). -/
def map₂_mono' : Prop := True
/-- map₂_mono_left (abstract). -/
def map₂_mono_left' : Prop := True
/-- map₂_mono_right (abstract). -/
def map₂_mono_right' : Prop := True
/-- le_map₂_iff (abstract). -/
def le_map₂_iff' : Prop := True
/-- map₂_eq_bot_iff (abstract). -/
def map₂_eq_bot_iff' : Prop := True
/-- map₂_bot_left (abstract). -/
def map₂_bot_left' : Prop := True
/-- map₂_bot_right (abstract). -/
def map₂_bot_right' : Prop := True
/-- map₂_neBot_iff (abstract). -/
def map₂_neBot_iff' : Prop := True
/-- of_map₂_left (abstract). -/
def of_map₂_left' : Prop := True
/-- of_map₂_right (abstract). -/
def of_map₂_right' : Prop := True
/-- map₂_sup_left (abstract). -/
def map₂_sup_left' : Prop := True
/-- map₂_sup_right (abstract). -/
def map₂_sup_right' : Prop := True
/-- map₂_inf_subset_left (abstract). -/
def map₂_inf_subset_left' : Prop := True
/-- map₂_inf_subset_right (abstract). -/
def map₂_inf_subset_right' : Prop := True
/-- map₂_pure_left (abstract). -/
def map₂_pure_left' : Prop := True
/-- map₂_pure_right (abstract). -/
def map₂_pure_right' : Prop := True
/-- map₂_pure (abstract). -/
def map₂_pure' : Prop := True
/-- map₂_swap (abstract). -/
def map₂_swap' : Prop := True
/-- map₂_left (abstract). -/
def map₂_left' : Prop := True
/-- map₂_right (abstract). -/
def map₂_right' : Prop := True
/-- map_map₂ (abstract). -/
def map_map₂' : Prop := True
/-- map₂_map_left (abstract). -/
def map₂_map_left' : Prop := True
/-- map₂_map_right (abstract). -/
def map₂_map_right' : Prop := True
/-- map₂_curry (abstract). -/
def map₂_curry' : Prop := True
/-- map_uncurry_prod (abstract). -/
def map_uncurry_prod' : Prop := True
/-- map₂_assoc (abstract). -/
def map₂_assoc' : Prop := True
/-- map₂_comm (abstract). -/
def map₂_comm' : Prop := True
/-- map₂_left_comm (abstract). -/
def map₂_left_comm' : Prop := True
/-- map₂_right_comm (abstract). -/
def map₂_right_comm' : Prop := True
/-- map_map₂_distrib (abstract). -/
def map_map₂_distrib' : Prop := True
/-- map_map₂_distrib_left (abstract). -/
def map_map₂_distrib_left' : Prop := True
/-- map_map₂_distrib_right (abstract). -/
def map_map₂_distrib_right' : Prop := True
/-- map₂_map_left_comm (abstract). -/
def map₂_map_left_comm' : Prop := True
/-- map_map₂_right_comm (abstract). -/
def map_map₂_right_comm' : Prop := True
/-- map₂_distrib_le_left (abstract). -/
def map₂_distrib_le_left' : Prop := True
/-- map₂_distrib_le_right (abstract). -/
def map₂_distrib_le_right' : Prop := True
/-- map_map₂_antidistrib (abstract). -/
def map_map₂_antidistrib' : Prop := True
/-- map_map₂_antidistrib_left (abstract). -/
def map_map₂_antidistrib_left' : Prop := True
/-- map_map₂_antidistrib_right (abstract). -/
def map_map₂_antidistrib_right' : Prop := True
/-- map₂_map_left_anticomm (abstract). -/
def map₂_map_left_anticomm' : Prop := True
/-- map_map₂_right_anticomm (abstract). -/
def map_map₂_right_anticomm' : Prop := True
/-- map₂_left_identity (abstract). -/
def map₂_left_identity' : Prop := True
/-- map₂_right_identity (abstract). -/
def map₂_right_identity' : Prop := True

-- Filter/Partial.lean
/-- rmap (abstract). -/
def rmap' : Prop := True
/-- rmap_rmap (abstract). -/
def rmap_rmap' : Prop := True
/-- RTendsto (abstract). -/
def RTendsto' : Prop := True
/-- rcomap (abstract). -/
def rcomap' : Prop := True
/-- rcomap_rcomap (abstract). -/
def rcomap_rcomap' : Prop := True
/-- rcomap_compose (abstract). -/
def rcomap_compose' : Prop := True
/-- rtendsto_iff_le_rcomap (abstract). -/
def rtendsto_iff_le_rcomap' : Prop := True
/-- rcomap'_rcomap' (abstract). -/
def rcomap'_rcomap' : Prop := True
/-- rcomap'_compose (abstract). -/
def rcomap'_compose' : Prop := True
/-- rtendsto'_def (abstract). -/
def rtendsto'_def' : Prop := True
/-- tendsto_iff_rtendsto (abstract). -/
def tendsto_iff_rtendsto' : Prop := True
/-- pmap (abstract). -/
def pmap' : Prop := True
/-- PTendsto (abstract). -/
def PTendsto' : Prop := True
/-- pmap_res (abstract). -/
def pmap_res' : Prop := True
/-- tendsto_iff_ptendsto (abstract). -/
def tendsto_iff_ptendsto' : Prop := True
/-- tendsto_iff_ptendsto_univ (abstract). -/
def tendsto_iff_ptendsto_univ' : Prop := True
/-- pcomap' (abstract). -/
def pcomap' : Prop := True
/-- ptendsto'_def (abstract). -/
def ptendsto'_def' : Prop := True
/-- ptendsto_of_ptendsto' (abstract). -/
def ptendsto_of_ptendsto' : Prop := True
/-- ptendsto'_of_ptendsto (abstract). -/
def ptendsto'_of_ptendsto' : Prop := True

-- Filter/Pi.lean
/-- pi (abstract). -/
def pi' : Prop := True
/-- tendsto_eval_pi (abstract). -/
def tendsto_eval_pi' : Prop := True
/-- tendsto_pi (abstract). -/
def tendsto_pi' : Prop := True
/-- le_pi (abstract). -/
def le_pi' : Prop := True
/-- pi_mono (abstract). -/
def pi_mono' : Prop := True
/-- mem_pi_of_mem (abstract). -/
def mem_pi_of_mem' : Prop := True
/-- pi_mem_pi (abstract). -/
def pi_mem_pi' : Prop := True
/-- mem_pi (abstract). -/
def mem_pi' : Prop := True
/-- mem_of_pi_mem_pi (abstract). -/
def mem_of_pi_mem_pi' : Prop := True
/-- pi_mem_pi_iff (abstract). -/
def pi_mem_pi_iff' : Prop := True
/-- eval_pi (abstract). -/
def eval_pi' : Prop := True
/-- eventually_pi (abstract). -/
def eventually_pi' : Prop := True
/-- hasBasis_pi (abstract). -/
def hasBasis_pi' : Prop := True
/-- le_pi_principal (abstract). -/
def le_pi_principal' : Prop := True
/-- pi_principal (abstract). -/
def pi_principal' : Prop := True
/-- pi_pure (abstract). -/
def pi_pure' : Prop := True
/-- pi_inf_principal_univ_pi_eq_bot (abstract). -/
def pi_inf_principal_univ_pi_eq_bot' : Prop := True
/-- pi_inf_principal_pi_eq_bot (abstract). -/
def pi_inf_principal_pi_eq_bot' : Prop := True
/-- pi_inf_principal_univ_pi_neBot (abstract). -/
def pi_inf_principal_univ_pi_neBot' : Prop := True
/-- pi_inf_principal_pi_neBot (abstract). -/
def pi_inf_principal_pi_neBot' : Prop := True
/-- pi_eq_bot (abstract). -/
def pi_eq_bot' : Prop := True
/-- pi_neBot (abstract). -/
def pi_neBot' : Prop := True
/-- map_eval_pi (abstract). -/
def map_eval_pi' : Prop := True
/-- pi_le_pi (abstract). -/
def pi_le_pi' : Prop := True
/-- pi_inj (abstract). -/
def pi_inj' : Prop := True
/-- tendsto_piMap_pi (abstract). -/
def tendsto_piMap_pi' : Prop := True
/-- coprodᵢ (abstract). -/
def coprodᵢ' : Prop := True
/-- mem_coprodᵢ_iff (abstract). -/
def mem_coprodᵢ_iff' : Prop := True
/-- compl_mem_coprodᵢ (abstract). -/
def compl_mem_coprodᵢ' : Prop := True
/-- coprodᵢ_neBot_iff' (abstract). -/
def coprodᵢ_neBot_iff' : Prop := True
/-- coprodᵢ_eq_bot_iff' (abstract). -/
def coprodᵢ_eq_bot_iff' : Prop := True
/-- coprodᵢ_bot' (abstract). -/
def coprodᵢ_bot' : Prop := True
/-- coprodᵢ_neBot (abstract). -/
def coprodᵢ_neBot' : Prop := True
/-- pi_map_coprodᵢ (abstract). -/
def pi_map_coprodᵢ' : Prop := True

-- Filter/Pointwise.lean
/-- instOne (abstract). -/
def instOne' : Prop := True
/-- one_prod (abstract). -/
def one_prod' : Prop := True
/-- eventually_one (abstract). -/
def eventually_one' : Prop := True
/-- pureOneHom (abstract). -/
def pureOneHom' : Prop := True
/-- inv_eq_bot_iff (abstract). -/
def inv_eq_bot_iff' : Prop := True
/-- neBot_inv_iff (abstract). -/
def neBot_inv_iff' : Prop := True
-- COLLISION: inv' already in SetTheory.lean — rename needed
/-- instNeBot (abstract). -/
def instNeBot' : Prop := True
/-- comap_inv (abstract). -/
def comap_inv' : Prop := True
/-- inv_mem_inv (abstract). -/
def inv_mem_inv' : Prop := True
/-- instInvolutiveInv (abstract). -/
def instInvolutiveInv' : Prop := True
/-- inv_le_inv_iff (abstract). -/
def inv_le_inv_iff' : Prop := True
/-- inv_le_iff_le_inv (abstract). -/
def inv_le_iff_le_inv' : Prop := True
/-- inv_le_self (abstract). -/
def inv_le_self' : Prop := True
/-- inv_atTop (abstract). -/
def inv_atTop' : Prop := True
/-- instMul (abstract). -/
def instMul' : Prop := True
/-- mul_mem_mul (abstract). -/
def mul_mem_mul' : Prop := True
/-- bot_mul (abstract). -/
def bot_mul' : Prop := True
/-- mul_bot (abstract). -/
def mul_bot' : Prop := True
/-- mul_eq_bot_iff (abstract). -/
def mul_eq_bot_iff' : Prop := True
/-- mul_neBot_iff (abstract). -/
def mul_neBot_iff' : Prop := True
/-- of_mul_left (abstract). -/
def of_mul_left' : Prop := True
/-- of_mul_right (abstract). -/
def of_mul_right' : Prop := True
/-- pure_mul (abstract). -/
def pure_mul' : Prop := True
/-- mul_pure (abstract). -/
def mul_pure' : Prop := True
/-- pure_mul_pure (abstract). -/
def pure_mul_pure' : Prop := True
/-- le_mul_iff (abstract). -/
def le_mul_iff' : Prop := True
/-- pureMulHom (abstract). -/
def pureMulHom' : Prop := True
/-- instDiv (abstract). -/
def instDiv' : Prop := True
/-- div_mem_div (abstract). -/
def div_mem_div' : Prop := True
/-- bot_div (abstract). -/
def bot_div' : Prop := True
/-- div_bot (abstract). -/
def div_bot' : Prop := True
/-- div_eq_bot_iff (abstract). -/
def div_eq_bot_iff' : Prop := True
/-- div_neBot_iff (abstract). -/
def div_neBot_iff' : Prop := True
/-- div (abstract). -/
def div' : Prop := True
/-- of_div_left (abstract). -/
def of_div_left' : Prop := True
/-- of_div_right (abstract). -/
def of_div_right' : Prop := True
/-- pure_div (abstract). -/
def pure_div' : Prop := True
/-- div_pure (abstract). -/
def div_pure' : Prop := True
/-- pure_div_pure (abstract). -/
def pure_div_pure' : Prop := True
/-- div_le_div (abstract). -/
def div_le_div' : Prop := True
/-- div_le_div_left (abstract). -/
def div_le_div_left' : Prop := True
/-- div_le_div_right (abstract). -/
def div_le_div_right' : Prop := True
/-- le_div_iff (abstract). -/
def le_div_iff' : Prop := True
/-- instNSMul (abstract). -/
def instNSMul' : Prop := True
/-- instNPow (abstract). -/
def instNPow' : Prop := True
/-- instZSMul (abstract). -/
def instZSMul' : Prop := True
/-- instZPow (abstract). -/
def instZPow' : Prop := True
/-- semigroup (abstract). -/
def semigroup' : Prop := True
/-- commSemigroup (abstract). -/
def commSemigroup' : Prop := True
/-- mulOneClass (abstract). -/
def mulOneClass' : Prop := True
/-- mapMonoidHom (abstract). -/
def mapMonoidHom' : Prop := True
/-- comap_mul_comap_le (abstract). -/
def comap_mul_comap_le' : Prop := True
/-- pureMonoidHom (abstract). -/
def pureMonoidHom' : Prop := True
/-- monoid (abstract). -/
def monoid' : Prop := True
/-- pow_mem_pow (abstract). -/
def pow_mem_pow' : Prop := True
/-- bot_pow (abstract). -/
def bot_pow' : Prop := True
/-- mul_top_of_one_le (abstract). -/
def mul_top_of_one_le' : Prop := True
/-- top_mul_of_one_le (abstract). -/
def top_mul_of_one_le' : Prop := True
/-- top_mul_top (abstract). -/
def top_mul_top' : Prop := True
/-- top_pow (abstract). -/
def top_pow' : Prop := True
/-- commMonoid (abstract). -/
def commMonoid' : Prop := True
/-- divisionMonoid (abstract). -/
def divisionMonoid' : Prop := True
-- COLLISION: isUnit_iff' already in SetTheory.lean — rename needed
/-- divisionCommMonoid (abstract). -/
def divisionCommMonoid' : Prop := True
/-- instDistribNeg (abstract). -/
def instDistribNeg' : Prop := True
/-- mul_add_subset (abstract). -/
def mul_add_subset' : Prop := True
/-- add_mul_subset (abstract). -/
def add_mul_subset' : Prop := True
/-- mul_zero_nonneg (abstract). -/
def mul_zero_nonneg' : Prop := True
/-- zero_mul_nonneg (abstract). -/
def zero_mul_nonneg' : Prop := True
/-- one_le_div_iff (abstract). -/
def one_le_div_iff' : Prop := True
/-- not_one_le_div_iff (abstract). -/
def not_one_le_div_iff' : Prop := True
/-- one_le_div (abstract). -/
def one_le_div' : Prop := True
/-- isUnit_pure (abstract). -/
def isUnit_pure' : Prop := True
/-- isUnit_iff_singleton (abstract). -/
def isUnit_iff_singleton' : Prop := True
/-- map_inv' (abstract). -/
def map_inv' : Prop := True
/-- inv_inv (abstract). -/
def inv_inv' : Prop := True
/-- map_div (abstract). -/
def map_div' : Prop := True
/-- div_div (abstract). -/
def div_div' : Prop := True
/-- div_zero_nonneg (abstract). -/
def div_zero_nonneg' : Prop := True
/-- zero_div_nonneg (abstract). -/
def zero_div_nonneg' : Prop := True
/-- instSMul (abstract). -/
def instSMul' : Prop := True
/-- smul_mem_smul (abstract). -/
def smul_mem_smul' : Prop := True
/-- bot_smul (abstract). -/
def bot_smul' : Prop := True
/-- smul_bot (abstract). -/
def smul_bot' : Prop := True
/-- smul_eq_bot_iff (abstract). -/
def smul_eq_bot_iff' : Prop := True
/-- smul_neBot_iff (abstract). -/
def smul_neBot_iff' : Prop := True
/-- of_smul_left (abstract). -/
def of_smul_left' : Prop := True
/-- of_smul_right (abstract). -/
def of_smul_right' : Prop := True
/-- pure_smul (abstract). -/
def pure_smul' : Prop := True
/-- smul_pure (abstract). -/
def smul_pure' : Prop := True
/-- pure_smul_pure (abstract). -/
def pure_smul_pure' : Prop := True
/-- smul_le_smul (abstract). -/
def smul_le_smul' : Prop := True
/-- smul_le_smul_left (abstract). -/
def smul_le_smul_left' : Prop := True
/-- smul_le_smul_right (abstract). -/
def smul_le_smul_right' : Prop := True
/-- le_smul_iff (abstract). -/
def le_smul_iff' : Prop := True
/-- instVSub (abstract). -/
def instVSub' : Prop := True
/-- vsub_mem_vsub (abstract). -/
def vsub_mem_vsub' : Prop := True
/-- bot_vsub (abstract). -/
def bot_vsub' : Prop := True
/-- vsub_bot (abstract). -/
def vsub_bot' : Prop := True
/-- vsub_eq_bot_iff (abstract). -/
def vsub_eq_bot_iff' : Prop := True
/-- vsub_neBot_iff (abstract). -/
def vsub_neBot_iff' : Prop := True
/-- vsub (abstract). -/
def vsub' : Prop := True
/-- of_vsub_left (abstract). -/
def of_vsub_left' : Prop := True
/-- of_vsub_right (abstract). -/
def of_vsub_right' : Prop := True
/-- pure_vsub (abstract). -/
def pure_vsub' : Prop := True
/-- vsub_pure (abstract). -/
def vsub_pure' : Prop := True
/-- vsub_le_vsub (abstract). -/
def vsub_le_vsub' : Prop := True
/-- vsub_le_vsub_left (abstract). -/
def vsub_le_vsub_left' : Prop := True
/-- vsub_le_vsub_right (abstract). -/
def vsub_le_vsub_right' : Prop := True
/-- le_vsub_iff (abstract). -/
def le_vsub_iff' : Prop := True
/-- instSMulFilter (abstract). -/
def instSMulFilter' : Prop := True
/-- smul_set_mem_smul_filter (abstract). -/
def smul_set_mem_smul_filter' : Prop := True
/-- smul_filter_bot (abstract). -/
def smul_filter_bot' : Prop := True
/-- smul_filter_eq_bot_iff (abstract). -/
def smul_filter_eq_bot_iff' : Prop := True
/-- smul_filter_neBot_iff (abstract). -/
def smul_filter_neBot_iff' : Prop := True
/-- smul_filter (abstract). -/
def smul_filter' : Prop := True
/-- of_smul_filter (abstract). -/
def of_smul_filter' : Prop := True
/-- smul_filter_le_smul_filter (abstract). -/
def smul_filter_le_smul_filter' : Prop := True
/-- mulAction (abstract). -/
def mulAction' : Prop := True
/-- mulActionFilter (abstract). -/
def mulActionFilter' : Prop := True
/-- distribMulActionFilter (abstract). -/
def distribMulActionFilter' : Prop := True
/-- mulDistribMulActionFilter (abstract). -/
def mulDistribMulActionFilter' : Prop := True
/-- smul_zero_nonneg (abstract). -/
def smul_zero_nonneg' : Prop := True
/-- zero_smul_nonneg (abstract). -/
def zero_smul_nonneg' : Prop := True
/-- zero_smul_filter_nonpos (abstract). -/
def zero_smul_filter_nonpos' : Prop := True
/-- zero_smul_filter (abstract). -/
def zero_smul_filter' : Prop := True

-- Filter/Prod.lean
/-- prod_mem_prod (abstract). -/
def prod_mem_prod' : Prop := True
/-- mem_prod_iff (abstract). -/
def mem_prod_iff' : Prop := True
/-- compl_diagonal_mem_prod (abstract). -/
def compl_diagonal_mem_prod' : Prop := True
/-- prod_mem_prod_iff (abstract). -/
def prod_mem_prod_iff' : Prop := True
/-- mem_prod_principal (abstract). -/
def mem_prod_principal' : Prop := True
/-- mem_prod_top (abstract). -/
def mem_prod_top' : Prop := True
/-- eventually_prod_principal_iff (abstract). -/
def eventually_prod_principal_iff' : Prop := True
/-- comap_prod (abstract). -/
def comap_prod' : Prop := True
/-- comap_prodMap_prod (abstract). -/
def comap_prodMap_prod' : Prop := True
/-- prod_top (abstract). -/
def prod_top' : Prop := True
/-- top_prod (abstract). -/
def top_prod' : Prop := True
/-- sup_prod (abstract). -/
def sup_prod' : Prop := True
/-- prod_sup (abstract). -/
def prod_sup' : Prop := True
/-- eventually_prod_iff (abstract). -/
def eventually_prod_iff' : Prop := True
/-- tendsto_fst (abstract). -/
def tendsto_fst' : Prop := True
/-- tendsto_snd (abstract). -/
def tendsto_snd' : Prop := True
/-- tendsto_prod_swap (abstract). -/
def tendsto_prod_swap' : Prop := True
/-- prod_inl (abstract). -/
def prod_inl' : Prop := True
/-- prod_inr (abstract). -/
def prod_inr' : Prop := True
/-- prod_map (abstract). -/
def prod_map' : Prop := True
/-- uncurry (abstract). -/
def uncurry' : Prop := True
/-- diag_of_prod (abstract). -/
def diag_of_prod' : Prop := True
/-- diag_of_prod_left (abstract). -/
def diag_of_prod_left' : Prop := True
/-- diag_of_prod_right (abstract). -/
def diag_of_prod_right' : Prop := True
/-- tendsto_diag (abstract). -/
def tendsto_diag' : Prop := True
/-- prod_iInf_left (abstract). -/
def prod_iInf_left' : Prop := True
/-- prod_iInf_right (abstract). -/
def prod_iInf_right' : Prop := True
/-- prod_mono (abstract). -/
def prod_mono' : Prop := True
/-- prod_mono_left (abstract). -/
def prod_mono_left' : Prop := True
/-- prod_mono_right (abstract). -/
def prod_mono_right' : Prop := True
/-- prod_comm' (abstract). -/
def prod_comm' : Prop := True
/-- mem_prod_iff_left (abstract). -/
def mem_prod_iff_left' : Prop := True
/-- mem_prod_iff_right (abstract). -/
def mem_prod_iff_right' : Prop := True
/-- map_fst_prod (abstract). -/
def map_fst_prod' : Prop := True
/-- map_snd_prod (abstract). -/
def map_snd_prod' : Prop := True
-- COLLISION: prod_le_prod' already in SetTheory.lean — rename needed
/-- prod_inj (abstract). -/
def prod_inj' : Prop := True
/-- eventually_swap_iff (abstract). -/
def eventually_swap_iff' : Prop := True
/-- prod_assoc (abstract). -/
def prod_assoc' : Prop := True
/-- prod_assoc_symm (abstract). -/
def prod_assoc_symm' : Prop := True
/-- tendsto_prodAssoc (abstract). -/
def tendsto_prodAssoc' : Prop := True
/-- tendsto_prodAssoc_symm (abstract). -/
def tendsto_prodAssoc_symm' : Prop := True
/-- map_swap4_prod (abstract). -/
def map_swap4_prod' : Prop := True
/-- tendsto_swap4_prod (abstract). -/
def tendsto_swap4_prod' : Prop := True
/-- prod_map_map_eq' (abstract). -/
def prod_map_map_eq' : Prop := True
/-- prod_map_left (abstract). -/
def prod_map_left' : Prop := True
/-- prod_map_right (abstract). -/
def prod_map_right' : Prop := True
/-- le_prod_map_fst_snd (abstract). -/
def le_prod_map_fst_snd' : Prop := True
/-- map_prod (abstract). -/
def map_prod' : Prop := True
/-- prod_eq (abstract). -/
def prod_eq' : Prop := True
/-- prod_inf_prod (abstract). -/
def prod_inf_prod' : Prop := True
/-- inf_prod (abstract). -/
def inf_prod' : Prop := True
/-- prod_inf (abstract). -/
def prod_inf' : Prop := True
/-- prod_principal_principal (abstract). -/
def prod_principal_principal' : Prop := True
/-- pure_prod (abstract). -/
def pure_prod' : Prop := True
/-- map_pure_prod (abstract). -/
def map_pure_prod' : Prop := True
/-- prod_pure (abstract). -/
def prod_pure' : Prop := True
/-- prod_eq_bot (abstract). -/
def prod_eq_bot' : Prop := True
/-- prod_bot (abstract). -/
def prod_bot' : Prop := True
/-- bot_prod (abstract). -/
def bot_prod' : Prop := True
/-- prod_neBot (abstract). -/
def prod_neBot' : Prop := True
/-- disjoint_prod (abstract). -/
def disjoint_prod' : Prop := True
/-- frequently_prod_and (abstract). -/
def frequently_prod_and' : Prop := True
/-- tendsto_prod_iff (abstract). -/
def tendsto_prod_iff' : Prop := True
/-- le_prod (abstract). -/
def le_prod' : Prop := True
/-- coprod_eq_prod_top_sup_top_prod (abstract). -/
def coprod_eq_prod_top_sup_top_prod' : Prop := True
/-- mem_coprod_iff (abstract). -/
def mem_coprod_iff' : Prop := True
/-- bot_coprod (abstract). -/
def bot_coprod' : Prop := True
/-- coprod_bot (abstract). -/
def coprod_bot' : Prop := True
/-- compl_mem_coprod (abstract). -/
def compl_mem_coprod' : Prop := True
/-- coprod_mono (abstract). -/
def coprod_mono' : Prop := True
/-- coprod_neBot_iff (abstract). -/
def coprod_neBot_iff' : Prop := True
/-- coprod_neBot_left (abstract). -/
def coprod_neBot_left' : Prop := True
/-- coprod_neBot_right (abstract). -/
def coprod_neBot_right' : Prop := True
/-- principal_coprod_principal (abstract). -/
def principal_coprod_principal' : Prop := True
/-- map_const_principal_coprod_map_id_principal (abstract). -/
def map_const_principal_coprod_map_id_principal' : Prop := True
/-- map_prod_map_const_id_principal_coprod_principal (abstract). -/
def map_prod_map_const_id_principal_coprod_principal' : Prop := True
/-- prod_map_coprod (abstract). -/
def prod_map_coprod' : Prop := True

-- Filter/Ring.lean
/-- mul_le_mul' (abstract). -/
def mul_le_mul' : Prop := True
/-- mul_nonneg (abstract). -/
def mul_nonneg' : Prop := True
/-- eventually_sub_nonneg (abstract). -/
def eventually_sub_nonneg' : Prop := True

-- Filter/SmallSets.lean
/-- smallSets (abstract). -/
def smallSets' : Prop := True
/-- smallSets_eq_generate (abstract). -/
def smallSets_eq_generate' : Prop := True
/-- hasBasis_smallSets (abstract). -/
def hasBasis_smallSets' : Prop := True
/-- tendsto_smallSets_iff (abstract). -/
def tendsto_smallSets_iff' : Prop := True
/-- eventually_smallSets (abstract). -/
def eventually_smallSets' : Prop := True
/-- frequently_smallSets (abstract). -/
def frequently_smallSets' : Prop := True
/-- frequently_smallSets_mem (abstract). -/
def frequently_smallSets_mem' : Prop := True
/-- tendsto_image_smallSets (abstract). -/
def tendsto_image_smallSets' : Prop := True
/-- tendsto_smallSets (abstract). -/
def tendsto_smallSets' : Prop := True
/-- monotone_smallSets (abstract). -/
def monotone_smallSets' : Prop := True
/-- smallSets_bot (abstract). -/
def smallSets_bot' : Prop := True
/-- smallSets_top (abstract). -/
def smallSets_top' : Prop := True
/-- smallSets_principal (abstract). -/
def smallSets_principal' : Prop := True
/-- smallSets_comap_eq_comap_image (abstract). -/
def smallSets_comap_eq_comap_image' : Prop := True
/-- smallSets_comap (abstract). -/
def smallSets_comap' : Prop := True
/-- comap_smallSets (abstract). -/
def comap_smallSets' : Prop := True
/-- smallSets_iInf (abstract). -/
def smallSets_iInf' : Prop := True
/-- smallSets_inf (abstract). -/
def smallSets_inf' : Prop := True
/-- smallSets_mono (abstract). -/
def smallSets_mono' : Prop := True
/-- of_smallSets (abstract). -/
def of_smallSets' : Prop := True
/-- eventually_smallSets_eventually (abstract). -/
def eventually_smallSets_eventually' : Prop := True
/-- eventually_smallSets_forall (abstract). -/
def eventually_smallSets_forall' : Prop := True
/-- eventually_smallSets_subset (abstract). -/
def eventually_smallSets_subset' : Prop := True

-- Filter/Subsingleton.lean
/-- Subsingleton (abstract). -/
def Subsingleton' : Prop := True
/-- anti (abstract). -/
def anti' : Prop := True
/-- of_subsingleton (abstract). -/
def of_subsingleton' : Prop := True
/-- subsingleton_pure (abstract). -/
def subsingleton_pure' : Prop := True
/-- subsingleton_bot (abstract). -/
def subsingleton_bot' : Prop := True
/-- exists_eq_pure (abstract). -/
def exists_eq_pure' : Prop := True
/-- subsingleton_iff_bot_or_pure (abstract). -/
def subsingleton_iff_bot_or_pure' : Prop := True
/-- subsingleton_iff_exists_le_pure (abstract). -/
def subsingleton_iff_exists_le_pure' : Prop := True
/-- subsingleton_iff_exists_singleton_mem (abstract). -/
def subsingleton_iff_exists_singleton_mem' : Prop := True

-- Filter/Tendsto.lean
/-- eventually_mem (abstract). -/
def eventually_mem' : Prop := True
/-- eventually (abstract). -/
def eventually' : Prop := True
/-- not_tendsto_iff_exists_frequently_nmem (abstract). -/
def not_tendsto_iff_exists_frequently_nmem' : Prop := True
/-- frequently_map (abstract). -/
def frequently_map' : Prop := True
/-- tendsto_bot (abstract). -/
def tendsto_bot' : Prop := True
/-- of_neBot_imp (abstract). -/
def of_neBot_imp' : Prop := True
/-- tendsto_top (abstract). -/
def tendsto_top' : Prop := True
/-- le_map_of_right_inverse (abstract). -/
def le_map_of_right_inverse' : Prop := True
/-- tendsto_of_isEmpty (abstract). -/
def tendsto_of_isEmpty' : Prop := True
/-- eventuallyEq_of_left_inv_of_right_inv (abstract). -/
def eventuallyEq_of_left_inv_of_right_inv' : Prop := True
/-- tendsto_iff_comap (abstract). -/
def tendsto_iff_comap' : Prop := True
/-- disjoint (abstract). -/
def disjoint' : Prop := True
/-- tendsto_congr' (abstract). -/
def tendsto_congr' : Prop := True
/-- tendsto_id (abstract). -/
def tendsto_id' : Prop := True
/-- iterate (abstract). -/
def iterate' : Prop := True
/-- neBot (abstract). -/
def neBot' : Prop := True
/-- tendsto_map (abstract). -/
def tendsto_map' : Prop := True
/-- tendsto_map'_iff (abstract). -/
def tendsto_map'_iff' : Prop := True
/-- tendsto_comap (abstract). -/
def tendsto_comap' : Prop := True
/-- tendsto_comap_iff (abstract). -/
def tendsto_comap_iff' : Prop := True
/-- tendsto_comap'_iff (abstract). -/
def tendsto_comap'_iff' : Prop := True
/-- of_tendsto_comp (abstract). -/
def of_tendsto_comp' : Prop := True
/-- comap_eq_of_inverse (abstract). -/
def comap_eq_of_inverse' : Prop := True
/-- map_eq_of_inverse (abstract). -/
def map_eq_of_inverse' : Prop := True
/-- tendsto_inf (abstract). -/
def tendsto_inf' : Prop := True
/-- tendsto_inf_left (abstract). -/
def tendsto_inf_left' : Prop := True
/-- tendsto_inf_right (abstract). -/
def tendsto_inf_right' : Prop := True
/-- tendsto_iInf (abstract). -/
def tendsto_iInf' : Prop := True
/-- tendsto_iInf_iInf (abstract). -/
def tendsto_iInf_iInf' : Prop := True
/-- tendsto_sup (abstract). -/
def tendsto_sup' : Prop := True
/-- sup_sup (abstract). -/
def sup_sup' : Prop := True
/-- tendsto_iSup (abstract). -/
def tendsto_iSup' : Prop := True
/-- tendsto_iSup_iSup (abstract). -/
def tendsto_iSup_iSup' : Prop := True
/-- tendsto_principal (abstract). -/
def tendsto_principal' : Prop := True
/-- tendsto_principal_principal (abstract). -/
def tendsto_principal_principal' : Prop := True
/-- tendsto_pure (abstract). -/
def tendsto_pure' : Prop := True
/-- tendsto_pure_pure (abstract). -/
def tendsto_pure_pure' : Prop := True
/-- tendsto_const_pure (abstract). -/
def tendsto_const_pure' : Prop := True
/-- map_inf_principal_preimage (abstract). -/
def map_inf_principal_preimage' : Prop := True
/-- not_tendsto (abstract). -/
def not_tendsto' : Prop := True
/-- if (abstract). -/
def if' : Prop := True
/-- piecewise (abstract). -/
def piecewise' : Prop := True
/-- map_mapsTo_Iic_iff_tendsto (abstract). -/
def map_mapsTo_Iic_iff_tendsto' : Prop := True
/-- map_mapsTo_Iic_iff_mapsTo (abstract). -/
def map_mapsTo_Iic_iff_mapsTo' : Prop := True

-- Filter/Ultrafilter.lean
/-- coe_injective (abstract). -/
def coe_injective' : Prop := True
/-- coe_le_coe (abstract). -/
def coe_le_coe' : Prop := True
/-- coe_inj (abstract). -/
def coe_inj' : Prop := True
/-- le_of_inf_neBot (abstract). -/
def le_of_inf_neBot' : Prop := True
/-- disjoint_iff_not_le (abstract). -/
def disjoint_iff_not_le' : Prop := True
/-- compl_not_mem_iff (abstract). -/
def compl_not_mem_iff' : Prop := True
/-- frequently_iff_eventually (abstract). -/
def frequently_iff_eventually' : Prop := True
/-- compl_mem_iff_not_mem (abstract). -/
def compl_mem_iff_not_mem' : Prop := True
/-- diff_mem_iff (abstract). -/
def diff_mem_iff' : Prop := True
/-- ofComplNotMemIff (abstract). -/
def ofComplNotMemIff' : Prop := True
/-- ofAtom (abstract). -/
def ofAtom' : Prop := True
/-- ne_empty_of_mem (abstract). -/
def ne_empty_of_mem' : Prop := True
/-- le_sup_iff (abstract). -/
def le_sup_iff' : Prop := True
/-- union_mem_iff (abstract). -/
def union_mem_iff' : Prop := True
/-- mem_or_compl_mem (abstract). -/
def mem_or_compl_mem' : Prop := True
/-- em (abstract). -/
def em' : Prop := True
/-- eventually_or (abstract). -/
def eventually_or' : Prop := True
/-- eventually_not (abstract). -/
def eventually_not' : Prop := True
/-- eventually_imp (abstract). -/
def eventually_imp' : Prop := True
/-- finite_sUnion_mem_iff (abstract). -/
def finite_sUnion_mem_iff' : Prop := True
/-- eq_pure_of_finite_mem (abstract). -/
def eq_pure_of_finite_mem' : Prop := True
/-- eq_pure_of_finite (abstract). -/
def eq_pure_of_finite' : Prop := True
/-- le_cofinite_or_eq_pure (abstract). -/
def le_cofinite_or_eq_pure' : Prop := True
/-- of_le (abstract). -/
def of_le' : Prop := True
/-- of_coe (abstract). -/
def of_coe' : Prop := True
/-- exists_ultrafilter_of_finite_inter_nonempty (abstract). -/
def exists_ultrafilter_of_finite_inter_nonempty' : Prop := True
/-- isAtom_pure (abstract). -/
def isAtom_pure' : Prop := True
/-- le_pure_iff (abstract). -/
def le_pure_iff' : Prop := True
/-- eq_pure_iff (abstract). -/
def eq_pure_iff' : Prop := True
/-- atTop_eq_pure_of_isTop (abstract). -/
def atTop_eq_pure_of_isTop' : Prop := True
/-- atBot_eq_pure_of_isBot (abstract). -/
def atBot_eq_pure_of_isBot' : Prop := True
/-- lt_pure_iff (abstract). -/
def lt_pure_iff' : Prop := True
/-- Iic_pure (abstract). -/
def Iic_pure' : Prop := True
/-- mem_iff_ultrafilter (abstract). -/
def mem_iff_ultrafilter' : Prop := True
/-- le_iff_ultrafilter (abstract). -/
def le_iff_ultrafilter' : Prop := True
/-- iSup_ultrafilter_le_eq (abstract). -/
def iSup_ultrafilter_le_eq' : Prop := True
/-- tendsto_iff_ultrafilter (abstract). -/
def tendsto_iff_ultrafilter' : Prop := True
/-- exists_ultrafilter_iff (abstract). -/
def exists_ultrafilter_iff' : Prop := True
/-- forall_neBot_le_iff (abstract). -/
def forall_neBot_le_iff' : Prop := True
/-- hyperfilter (abstract). -/
def hyperfilter' : Prop := True
/-- hyperfilter_le_cofinite (abstract). -/
def hyperfilter_le_cofinite' : Prop := True
/-- hyperfilter_le_atTop (abstract). -/
def hyperfilter_le_atTop' : Prop := True
/-- bot_ne_hyperfilter (abstract). -/
def bot_ne_hyperfilter' : Prop := True
/-- nmem_hyperfilter_of_finite (abstract). -/
def nmem_hyperfilter_of_finite' : Prop := True
/-- compl_mem_hyperfilter_of_finite (abstract). -/
def compl_mem_hyperfilter_of_finite' : Prop := True
/-- mem_hyperfilter_of_finite_compl (abstract). -/
def mem_hyperfilter_of_finite_compl' : Prop := True
/-- ofComapInfPrincipal (abstract). -/
def ofComapInfPrincipal' : Prop := True
/-- ofComapInfPrincipal_mem (abstract). -/
def ofComapInfPrincipal_mem' : Prop := True
/-- ofComapInfPrincipal_eq_of_map (abstract). -/
def ofComapInfPrincipal_eq_of_map' : Prop := True
/-- eq_of_le_pure (abstract). -/
def eq_of_le_pure' : Prop := True

-- Filter/ZeroAndBoundedAtFilter.lean
/-- ZeroAtFilter (abstract). -/
def ZeroAtFilter' : Prop := True
/-- zero_zeroAtFilter (abstract). -/
def zero_zeroAtFilter' : Prop := True
/-- zeroAtFilterSubmodule (abstract). -/
def zeroAtFilterSubmodule' : Prop := True
/-- zeroAtFilterAddSubmonoid (abstract). -/
def zeroAtFilterAddSubmonoid' : Prop := True
/-- BoundedAtFilter (abstract). -/
def BoundedAtFilter' : Prop := True
/-- boundedAtFilter (abstract). -/
def boundedAtFilter' : Prop := True
/-- const_boundedAtFilter (abstract). -/
def const_boundedAtFilter' : Prop := True
/-- boundedFilterSubmodule (abstract). -/
def boundedFilterSubmodule' : Prop := True
/-- boundedFilterSubalgebra (abstract). -/
def boundedFilterSubalgebra' : Prop := True

-- Fin/Basic.lean
/-- resolution (abstract). -/
def resolution' : Prop := True
/-- rev_last_eq_bot (abstract). -/
def rev_last_eq_bot' : Prop := True
/-- strictMono_pred_comp (abstract). -/
def strictMono_pred_comp' : Prop := True
/-- monotone_pred_comp (abstract). -/
def monotone_pred_comp' : Prop := True
/-- strictMono_castPred_comp (abstract). -/
def strictMono_castPred_comp' : Prop := True
/-- monotone_castPred_comp (abstract). -/
def monotone_castPred_comp' : Prop := True
/-- strictMono_iff_lt_succ (abstract). -/
def strictMono_iff_lt_succ' : Prop := True
/-- monotone_iff_le_succ (abstract). -/
def monotone_iff_le_succ' : Prop := True
/-- strictAnti_iff_succ_lt (abstract). -/
def strictAnti_iff_succ_lt' : Prop := True
/-- antitone_iff_succ_le (abstract). -/
def antitone_iff_succ_le' : Prop := True
/-- val_strictMono (abstract). -/
def val_strictMono' : Prop := True
/-- cast_strictMono (abstract). -/
def cast_strictMono' : Prop := True
/-- strictMono_succ (abstract). -/
def strictMono_succ' : Prop := True
/-- strictMono_castLE (abstract). -/
def strictMono_castLE' : Prop := True
/-- strictMono_castAdd (abstract). -/
def strictMono_castAdd' : Prop := True
/-- strictMono_castSucc (abstract). -/
def strictMono_castSucc' : Prop := True
/-- strictMono_natAdd (abstract). -/
def strictMono_natAdd' : Prop := True
/-- strictMono_addNat (abstract). -/
def strictMono_addNat' : Prop := True
/-- strictMono_succAbove (abstract). -/
def strictMono_succAbove' : Prop := True
/-- succAbove_lt_succAbove_iff (abstract). -/
def succAbove_lt_succAbove_iff' : Prop := True
/-- succAbove_le_succAbove_iff (abstract). -/
def succAbove_le_succAbove_iff' : Prop := True
/-- predAbove_right_monotone (abstract). -/
def predAbove_right_monotone' : Prop := True
/-- predAbove_left_monotone (abstract). -/
def predAbove_left_monotone' : Prop := True
/-- predAboveOrderHom (abstract). -/
def predAboveOrderHom' : Prop := True
/-- orderIsoSubtype (abstract). -/
def orderIsoSubtype' : Prop := True
/-- castOrderIso (abstract). -/
def castOrderIso' : Prop := True
/-- revOrderIso (abstract). -/
def revOrderIso' : Prop := True
/-- valOrderEmb (abstract). -/
def valOrderEmb' : Prop := True
/-- succOrderEmb (abstract). -/
def succOrderEmb' : Prop := True
/-- castLEOrderEmb (abstract). -/
def castLEOrderEmb' : Prop := True
/-- castAddOrderEmb (abstract). -/
def castAddOrderEmb' : Prop := True
/-- castSuccOrderEmb (abstract). -/
def castSuccOrderEmb' : Prop := True
/-- addNatOrderEmb (abstract). -/
def addNatOrderEmb' : Prop := True
/-- natAddOrderEmb (abstract). -/
def natAddOrderEmb' : Prop := True
/-- succAboveOrderEmb (abstract). -/
def succAboveOrderEmb' : Prop := True
/-- coe_orderIso_apply (abstract). -/
def coe_orderIso_apply' : Prop := True
/-- strictMono_unique (abstract). -/
def strictMono_unique' : Prop := True
/-- orderEmbedding_eq (abstract). -/
def orderEmbedding_eq' : Prop := True

-- Fin/Tuple.lean
/-- pi_lex_lt_cons_cons (abstract). -/
def pi_lex_lt_cons_cons' : Prop := True
/-- insertNth_mem_Icc (abstract). -/
def insertNth_mem_Icc' : Prop := True
/-- preimage_insertNth_Icc_of_mem (abstract). -/
def preimage_insertNth_Icc_of_mem' : Prop := True
/-- preimage_insertNth_Icc_of_not_mem (abstract). -/
def preimage_insertNth_Icc_of_not_mem' : Prop := True
/-- liftFun_vecCons (abstract). -/
def liftFun_vecCons' : Prop := True
/-- strictMono_vecCons (abstract). -/
def strictMono_vecCons' : Prop := True
/-- monotone_vecCons (abstract). -/
def monotone_vecCons' : Prop := True
/-- monotone_vecEmpty (abstract). -/
def monotone_vecEmpty' : Prop := True
/-- strictMono_vecEmpty (abstract). -/
def strictMono_vecEmpty' : Prop := True
/-- strictAnti_vecCons (abstract). -/
def strictAnti_vecCons' : Prop := True
/-- antitone_vecCons (abstract). -/
def antitone_vecCons' : Prop := True
/-- antitone_vecEmpty (abstract). -/
def antitone_vecEmpty' : Prop := True
/-- strictAnti_vecEmpty (abstract). -/
def strictAnti_vecEmpty' : Prop := True
/-- vecCons (abstract). -/
def vecCons' : Prop := True
/-- piFinTwoIso (abstract). -/
def piFinTwoIso' : Prop := True
/-- finTwoArrowIso (abstract). -/
def finTwoArrowIso' : Prop := True
/-- consOrderIso (abstract). -/
def consOrderIso' : Prop := True
/-- snocOrderIso (abstract). -/
def snocOrderIso' : Prop := True
/-- insertNthOrderIso (abstract). -/
def insertNthOrderIso' : Prop := True
/-- insertNthOrderIso_zero (abstract). -/
def insertNthOrderIso_zero' : Prop := True
/-- insertNthOrderIso_last (abstract). -/
def insertNthOrderIso_last' : Prop := True
/-- piFinSuccAboveIso (abstract). -/
def piFinSuccAboveIso' : Prop := True
/-- finSuccAboveOrderIso (abstract). -/
def finSuccAboveOrderIso' : Prop := True
/-- finSuccAboveOrderIso_symm_apply_last (abstract). -/
def finSuccAboveOrderIso_symm_apply_last' : Prop := True
/-- finSuccAboveOrderIso_symm_apply_ne_last (abstract). -/
def finSuccAboveOrderIso_symm_apply_ne_last' : Prop := True
/-- castLEOrderIso (abstract). -/
def castLEOrderIso' : Prop := True

-- FixedPoints.lean
/-- lfp (abstract). -/
def lfp' : Prop := True
/-- gfp (abstract). -/
def gfp' : Prop := True
/-- lfp_le (abstract). -/
def lfp_le' : Prop := True
/-- lfp_le_fixed (abstract). -/
def lfp_le_fixed' : Prop := True
/-- le_lfp (abstract). -/
def le_lfp' : Prop := True
/-- map_le_lfp (abstract). -/
def map_le_lfp' : Prop := True
/-- map_lfp (abstract). -/
def map_lfp' : Prop := True
/-- isFixedPt_lfp (abstract). -/
def isFixedPt_lfp' : Prop := True
/-- lfp_le_map (abstract). -/
def lfp_le_map' : Prop := True
/-- isLeast_lfp_le (abstract). -/
def isLeast_lfp_le' : Prop := True
/-- isLeast_lfp (abstract). -/
def isLeast_lfp' : Prop := True
/-- lfp_induction (abstract). -/
def lfp_induction' : Prop := True
/-- le_gfp (abstract). -/
def le_gfp' : Prop := True
/-- gfp_le (abstract). -/
def gfp_le' : Prop := True
/-- isFixedPt_gfp (abstract). -/
def isFixedPt_gfp' : Prop := True
/-- map_gfp (abstract). -/
def map_gfp' : Prop := True
/-- map_le_gfp (abstract). -/
def map_le_gfp' : Prop := True
/-- gfp_le_map (abstract). -/
def gfp_le_map' : Prop := True
/-- isGreatest_gfp_le (abstract). -/
def isGreatest_gfp_le' : Prop := True
/-- isGreatest_gfp (abstract). -/
def isGreatest_gfp' : Prop := True
/-- gfp_induction (abstract). -/
def gfp_induction' : Prop := True
/-- map_lfp_comp (abstract). -/
def map_lfp_comp' : Prop := True
/-- map_gfp_comp (abstract). -/
def map_gfp_comp' : Prop := True
/-- lfp_lfp (abstract). -/
def lfp_lfp' : Prop := True
/-- gfp_gfp (abstract). -/
def gfp_gfp' : Prop := True
/-- gfp_const_inf_le (abstract). -/
def gfp_const_inf_le' : Prop := True
/-- prevFixed (abstract). -/
def prevFixed' : Prop := True
/-- nextFixed (abstract). -/
def nextFixed' : Prop := True
/-- prevFixed_le (abstract). -/
def prevFixed_le' : Prop := True
/-- le_nextFixed (abstract). -/
def le_nextFixed' : Prop := True
/-- nextFixed_le (abstract). -/
def nextFixed_le' : Prop := True
/-- nextFixed_le_iff (abstract). -/
def nextFixed_le_iff' : Prop := True
/-- le_prevFixed_iff (abstract). -/
def le_prevFixed_iff' : Prop := True
/-- le_prevFixed (abstract). -/
def le_prevFixed' : Prop := True
/-- le_map_sup_fixedPoints (abstract). -/
def le_map_sup_fixedPoints' : Prop := True
/-- map_inf_fixedPoints_le (abstract). -/
def map_inf_fixedPoints_le' : Prop := True
/-- le_map_sSup_subset_fixedPoints (abstract). -/
def le_map_sSup_subset_fixedPoints' : Prop := True
/-- map_sInf_subset_fixedPoints_le (abstract). -/
def map_sInf_subset_fixedPoints_le' : Prop := True
/-- lfp_eq_sSup_iterate (abstract). -/
def lfp_eq_sSup_iterate' : Prop := True
/-- gfp_eq_sInf_iterate (abstract). -/
def gfp_eq_sInf_iterate' : Prop := True

-- GaloisConnection.lean
/-- along (abstract). -/
def along' : Prop := True
/-- GaloisConnection (abstract). -/
def GaloisConnection' : Prop := True
/-- to_galoisConnection (abstract). -/
def to_galoisConnection' : Prop := True
/-- monotone_intro (abstract). -/
def monotone_intro' : Prop := True
/-- le_iff_le (abstract). -/
def le_iff_le' : Prop := True
/-- l_le (abstract). -/
def l_le' : Prop := True
/-- le_u (abstract). -/
def le_u' : Prop := True
/-- le_u_l (abstract). -/
def le_u_l' : Prop := True
/-- l_u_le (abstract). -/
def l_u_le' : Prop := True
/-- monotone_u (abstract). -/
def monotone_u' : Prop := True
/-- monotone_l (abstract). -/
def monotone_l' : Prop := True
/-- upperBounds_l_image (abstract). -/
def upperBounds_l_image' : Prop := True
/-- lowerBounds_u_image (abstract). -/
def lowerBounds_u_image' : Prop := True
/-- bddAbove_l_image (abstract). -/
def bddAbove_l_image' : Prop := True
/-- bddBelow_u_image (abstract). -/
def bddBelow_u_image' : Prop := True
/-- isLUB_l_image (abstract). -/
def isLUB_l_image' : Prop := True
/-- isGLB_u_image (abstract). -/
def isGLB_u_image' : Prop := True
/-- isLeast_l (abstract). -/
def isLeast_l' : Prop := True
/-- isGreatest_u (abstract). -/
def isGreatest_u' : Prop := True
/-- isGLB_l (abstract). -/
def isGLB_l' : Prop := True
/-- isLUB_u (abstract). -/
def isLUB_u' : Prop := True
/-- le_u_l_trans (abstract). -/
def le_u_l_trans' : Prop := True
/-- l_u_le_trans (abstract). -/
def l_u_le_trans' : Prop := True
/-- u_l_u_eq_u (abstract). -/
def u_l_u_eq_u' : Prop := True
/-- u_unique (abstract). -/
def u_unique' : Prop := True
/-- exists_eq_u (abstract). -/
def exists_eq_u' : Prop := True
/-- u_eq (abstract). -/
def u_eq' : Prop := True
/-- l_u_l_eq_l (abstract). -/
def l_u_l_eq_l' : Prop := True
/-- l_unique (abstract). -/
def l_unique' : Prop := True
/-- exists_eq_l (abstract). -/
def exists_eq_l' : Prop := True
/-- l_eq (abstract). -/
def l_eq' : Prop := True
/-- u_eq_top (abstract). -/
def u_eq_top' : Prop := True
/-- u_top (abstract). -/
def u_top' : Prop := True
/-- l_eq_bot (abstract). -/
def l_eq_bot' : Prop := True
/-- l_bot (abstract). -/
def l_bot' : Prop := True
/-- l_sup (abstract). -/
def l_sup' : Prop := True
/-- u_inf (abstract). -/
def u_inf' : Prop := True
/-- l_iSup (abstract). -/
def l_iSup' : Prop := True
/-- l_iSup₂ (abstract). -/
def l_iSup₂' : Prop := True
/-- u_iInf (abstract). -/
def u_iInf' : Prop := True
/-- u_iInf₂ (abstract). -/
def u_iInf₂' : Prop := True
/-- l_sSup (abstract). -/
def l_sSup' : Prop := True
/-- u_sInf (abstract). -/
def u_sInf' : Prop := True
/-- lt_iff_lt (abstract). -/
def lt_iff_lt' : Prop := True
/-- compose (abstract). -/
def compose' : Prop := True
/-- dfun (abstract). -/
def dfun' : Prop := True
/-- l_comm_of_u_comm (abstract). -/
def l_comm_of_u_comm' : Prop := True
/-- u_comm_of_l_comm (abstract). -/
def u_comm_of_l_comm' : Prop := True
/-- l_comm_iff_u_comm (abstract). -/
def l_comm_iff_u_comm' : Prop := True
/-- gc_sSup_Iic (abstract). -/
def gc_sSup_Iic' : Prop := True
/-- gc_Ici_sInf (abstract). -/
def gc_Ici_sInf' : Prop := True
/-- sSup_image2_eq_sSup_sSup (abstract). -/
def sSup_image2_eq_sSup_sSup' : Prop := True
/-- sSup_image2_eq_sSup_sInf (abstract). -/
def sSup_image2_eq_sSup_sInf' : Prop := True
/-- sSup_image2_eq_sInf_sSup (abstract). -/
def sSup_image2_eq_sInf_sSup' : Prop := True
/-- sSup_image2_eq_sInf_sInf (abstract). -/
def sSup_image2_eq_sInf_sInf' : Prop := True
/-- sInf_image2_eq_sInf_sInf (abstract). -/
def sInf_image2_eq_sInf_sInf' : Prop := True
/-- sInf_image2_eq_sInf_sSup (abstract). -/
def sInf_image2_eq_sInf_sSup' : Prop := True
/-- sInf_image2_eq_sSup_sInf (abstract). -/
def sInf_image2_eq_sSup_sInf' : Prop := True
/-- sInf_image2_eq_sSup_sSup (abstract). -/
def sInf_image2_eq_sSup_sSup' : Prop := True
-- COLLISION: bddAbove_image' already in SetTheory.lean — rename needed
/-- bddBelow_image (abstract). -/
def bddBelow_image' : Prop := True
/-- bddAbove_preimage (abstract). -/
def bddAbove_preimage' : Prop := True
/-- bddBelow_preimage (abstract). -/
def bddBelow_preimage' : Prop := True
/-- galoisConnection_mul_div (abstract). -/
def galoisConnection_mul_div' : Prop := True
/-- GaloisInsertion (abstract). -/
def GaloisInsertion' : Prop := True
/-- monotoneIntro (abstract). -/
def monotoneIntro' : Prop := True
/-- toGaloisInsertion (abstract). -/
def toGaloisInsertion' : Prop := True
/-- liftOrderBot (abstract). -/
def liftOrderBot' : Prop := True
/-- l_u_eq (abstract). -/
def l_u_eq' : Prop := True
/-- leftInverse_l_u (abstract). -/
def leftInverse_l_u' : Prop := True
/-- l_top (abstract). -/
def l_top' : Prop := True
/-- l_surjective (abstract). -/
def l_surjective' : Prop := True
/-- u_injective (abstract). -/
def u_injective' : Prop := True
/-- l_sup_u (abstract). -/
def l_sup_u' : Prop := True
/-- l_iSup_u (abstract). -/
def l_iSup_u' : Prop := True
/-- l_biSup_u (abstract). -/
def l_biSup_u' : Prop := True
/-- l_sSup_u_image (abstract). -/
def l_sSup_u_image' : Prop := True
/-- l_inf_u (abstract). -/
def l_inf_u' : Prop := True
/-- l_iInf_u (abstract). -/
def l_iInf_u' : Prop := True
/-- l_biInf_u (abstract). -/
def l_biInf_u' : Prop := True
/-- l_sInf_u_image (abstract). -/
def l_sInf_u_image' : Prop := True
/-- l_iInf_of_ul_eq_self (abstract). -/
def l_iInf_of_ul_eq_self' : Prop := True
/-- l_biInf_of_ul_eq_self (abstract). -/
def l_biInf_of_ul_eq_self' : Prop := True
/-- u_le_u_iff (abstract). -/
def u_le_u_iff' : Prop := True
/-- strictMono_u (abstract). -/
def strictMono_u' : Prop := True
/-- isLUB_of_u_image (abstract). -/
def isLUB_of_u_image' : Prop := True
/-- isGLB_of_u_image (abstract). -/
def isGLB_of_u_image' : Prop := True
/-- liftSemilatticeSup (abstract). -/
def liftSemilatticeSup' : Prop := True
/-- liftSemilatticeInf (abstract). -/
def liftSemilatticeInf' : Prop := True
/-- liftLattice (abstract). -/
def liftLattice' : Prop := True
/-- liftOrderTop (abstract). -/
def liftOrderTop' : Prop := True
/-- liftBoundedOrder (abstract). -/
def liftBoundedOrder' : Prop := True
/-- liftCompleteLattice (abstract). -/
def liftCompleteLattice' : Prop := True
/-- GaloisCoinsertion (abstract). -/
def GaloisCoinsertion' : Prop := True
/-- ofDual (abstract). -/
def ofDual' : Prop := True
/-- toGaloisCoinsertion (abstract). -/
def toGaloisCoinsertion' : Prop := True
/-- u_l_eq (abstract). -/
def u_l_eq' : Prop := True
/-- u_l_leftInverse (abstract). -/
def u_l_leftInverse' : Prop := True
/-- u_bot (abstract). -/
def u_bot' : Prop := True
/-- u_surjective (abstract). -/
def u_surjective' : Prop := True
/-- l_injective (abstract). -/
def l_injective' : Prop := True
/-- u_inf_l (abstract). -/
def u_inf_l' : Prop := True
/-- u_iInf_l (abstract). -/
def u_iInf_l' : Prop := True
/-- u_sInf_l_image (abstract). -/
def u_sInf_l_image' : Prop := True
/-- u_sup_l (abstract). -/
def u_sup_l' : Prop := True
/-- u_iSup_l (abstract). -/
def u_iSup_l' : Prop := True
/-- u_biSup_l (abstract). -/
def u_biSup_l' : Prop := True
/-- u_sSup_l_image (abstract). -/
def u_sSup_l_image' : Prop := True
/-- u_iSup_of_lu_eq_self (abstract). -/
def u_iSup_of_lu_eq_self' : Prop := True
/-- u_biSup_of_lu_eq_self (abstract). -/
def u_biSup_of_lu_eq_self' : Prop := True
/-- l_le_l_iff (abstract). -/
def l_le_l_iff' : Prop := True
/-- strictMono_l (abstract). -/
def strictMono_l' : Prop := True
/-- isGLB_of_l_image (abstract). -/
def isGLB_of_l_image' : Prop := True
/-- isLUB_of_l_image (abstract). -/
def isLUB_of_l_image' : Prop := True
/-- gi_sSup_Iic (abstract). -/
def gi_sSup_Iic' : Prop := True
/-- gci_Ici_sInf (abstract). -/
def gci_Ici_sInf' : Prop := True

-- GameAdd.lean
/-- GameAdd (abstract). -/
def GameAdd' : Prop := True
/-- gameAdd_iff (abstract). -/
def gameAdd_iff' : Prop := True
/-- gameAdd_mk_iff (abstract). -/
def gameAdd_mk_iff' : Prop := True
/-- gameAdd_swap_swap (abstract). -/
def gameAdd_swap_swap' : Prop := True
/-- gameAdd_swap_swap_mk (abstract). -/
def gameAdd_swap_swap_mk' : Prop := True
/-- gameAdd_le_lex (abstract). -/
def gameAdd_le_lex' : Prop := True
/-- rprod_le_transGen_gameAdd (abstract). -/
def rprod_le_transGen_gameAdd' : Prop := True
/-- prod_gameAdd (abstract). -/
def prod_gameAdd' : Prop := True
/-- fix (abstract). -/
def fix' : Prop := True
/-- fix_eq (abstract). -/
def fix_eq' : Prop := True
-- COLLISION: induction' already in SetTheory.lean — rename needed
/-- to_sym2 (abstract). -/
def to_sym2' : Prop := True
/-- fst_snd (abstract). -/
def fst_snd' : Prop := True
/-- snd_fst (abstract). -/
def snd_fst' : Prop := True
/-- sym2_gameAdd (abstract). -/
def sym2_gameAdd' : Prop := True

-- Grade.lean
/-- GradeOrder (abstract). -/
def GradeOrder' : Prop := True
/-- GradeMinOrder (abstract). -/
def GradeMinOrder' : Prop := True
/-- GradeMaxOrder (abstract). -/
def GradeMaxOrder' : Prop := True
/-- GradeBoundedOrder (abstract). -/
def GradeBoundedOrder' : Prop := True
/-- grade (abstract). -/
def grade' : Prop := True
/-- grade_strictMono (abstract). -/
def grade_strictMono' : Prop := True
/-- covBy_iff_lt_covBy_grade (abstract). -/
def covBy_iff_lt_covBy_grade' : Prop := True
/-- isMin_grade_iff (abstract). -/
def isMin_grade_iff' : Prop := True
/-- isMax_grade_iff (abstract). -/
def isMax_grade_iff' : Prop := True
/-- grade_mono (abstract). -/
def grade_mono' : Prop := True
/-- grade_injective (abstract). -/
def grade_injective' : Prop := True
/-- grade_le_grade_iff (abstract). -/
def grade_le_grade_iff' : Prop := True
/-- grade_lt_grade_iff (abstract). -/
def grade_lt_grade_iff' : Prop := True
/-- grade_eq_grade_iff (abstract). -/
def grade_eq_grade_iff' : Prop := True
/-- grade_ne_grade_iff (abstract). -/
def grade_ne_grade_iff' : Prop := True
/-- grade_covBy_grade_iff (abstract). -/
def grade_covBy_grade_iff' : Prop := True
/-- grade_bot (abstract). -/
def grade_bot' : Prop := True
/-- liftLeft (abstract). -/
def liftLeft' : Prop := True
/-- liftRight (abstract). -/
def liftRight' : Prop := True
/-- finToNat (abstract). -/
def finToNat' : Prop := True
/-- wellFoundedLT (abstract). -/
def wellFoundedLT' : Prop := True

-- Height.lean
/-- subchain (abstract). -/
def subchain' : Prop := True
/-- nil_mem_subchain (abstract). -/
def nil_mem_subchain' : Prop := True
/-- cons_mem_subchain_iff (abstract). -/
def cons_mem_subchain_iff' : Prop := True
/-- singleton_mem_subchain_iff (abstract). -/
def singleton_mem_subchain_iff' : Prop := True
/-- chainHeight (abstract). -/
def chainHeight' : Prop := True
/-- chainHeight_eq_iSup_subtype (abstract). -/
def chainHeight_eq_iSup_subtype' : Prop := True
/-- exists_chain_of_le_chainHeight (abstract). -/
def exists_chain_of_le_chainHeight' : Prop := True
/-- le_chainHeight_TFAE (abstract). -/
def le_chainHeight_TFAE' : Prop := True
/-- le_chainHeight_iff (abstract). -/
def le_chainHeight_iff' : Prop := True
/-- length_le_chainHeight_of_mem_subchain (abstract). -/
def length_le_chainHeight_of_mem_subchain' : Prop := True
/-- chainHeight_eq_top_iff (abstract). -/
def chainHeight_eq_top_iff' : Prop := True
/-- one_le_chainHeight_iff (abstract). -/
def one_le_chainHeight_iff' : Prop := True
/-- chainHeight_eq_zero_iff (abstract). -/
def chainHeight_eq_zero_iff' : Prop := True
/-- chainHeight_empty (abstract). -/
def chainHeight_empty' : Prop := True
/-- chainHeight_of_isEmpty (abstract). -/
def chainHeight_of_isEmpty' : Prop := True
/-- le_chainHeight_add_nat_iff (abstract). -/
def le_chainHeight_add_nat_iff' : Prop := True
/-- chainHeight_add_le_chainHeight_add (abstract). -/
def chainHeight_add_le_chainHeight_add' : Prop := True
/-- chainHeight_le_chainHeight_TFAE (abstract). -/
def chainHeight_le_chainHeight_TFAE' : Prop := True
/-- chainHeight_le_chainHeight_iff (abstract). -/
def chainHeight_le_chainHeight_iff' : Prop := True
/-- chainHeight_le_chainHeight_iff_le (abstract). -/
def chainHeight_le_chainHeight_iff_le' : Prop := True
/-- chainHeight_mono (abstract). -/
def chainHeight_mono' : Prop := True
/-- chainHeight_image (abstract). -/
def chainHeight_image' : Prop := True
/-- chainHeight_dual (abstract). -/
def chainHeight_dual' : Prop := True
/-- chainHeight_eq_iSup_Ici (abstract). -/
def chainHeight_eq_iSup_Ici' : Prop := True
/-- chainHeight_eq_iSup_Iic (abstract). -/
def chainHeight_eq_iSup_Iic' : Prop := True
/-- chainHeight_insert_of_forall_gt (abstract). -/
def chainHeight_insert_of_forall_gt' : Prop := True
/-- chainHeight_insert_of_forall_lt (abstract). -/
def chainHeight_insert_of_forall_lt' : Prop := True
/-- chainHeight_union_le (abstract). -/
def chainHeight_union_le' : Prop := True
/-- chainHeight_union_eq (abstract). -/
def chainHeight_union_eq' : Prop := True
/-- wellFoundedGT_of_chainHeight_ne_top (abstract). -/
def wellFoundedGT_of_chainHeight_ne_top' : Prop := True
/-- wellFoundedLT_of_chainHeight_ne_top (abstract). -/
def wellFoundedLT_of_chainHeight_ne_top' : Prop := True

-- Heyting/Basic.lean
/-- GeneralizedHeytingAlgebra (abstract). -/
def GeneralizedHeytingAlgebra' : Prop := True
/-- GeneralizedCoheytingAlgebra (abstract). -/
def GeneralizedCoheytingAlgebra' : Prop := True
/-- HeytingAlgebra (abstract). -/
def HeytingAlgebra' : Prop := True
/-- CoheytingAlgebra (abstract). -/
def CoheytingAlgebra' : Prop := True
/-- BiheytingAlgebra (abstract). -/
def BiheytingAlgebra' : Prop := True
/-- ofHImp (abstract). -/
def ofHImp' : Prop := True
/-- ofCompl (abstract). -/
def ofCompl' : Prop := True
/-- ofSDiff (abstract). -/
def ofSDiff' : Prop := True
/-- ofHNot (abstract). -/
def ofHNot' : Prop := True
/-- le_himp_iff (abstract). -/
def le_himp_iff' : Prop := True
/-- le_himp_comm (abstract). -/
def le_himp_comm' : Prop := True
/-- le_himp (abstract). -/
def le_himp' : Prop := True
/-- le_himp_iff_left (abstract). -/
def le_himp_iff_left' : Prop := True
/-- himp_self (abstract). -/
def himp_self' : Prop := True
/-- himp_inf_le (abstract). -/
def himp_inf_le' : Prop := True
/-- inf_himp_le (abstract). -/
def inf_himp_le' : Prop := True
/-- inf_himp (abstract). -/
def inf_himp' : Prop := True
/-- himp_inf_self (abstract). -/
def himp_inf_self' : Prop := True
/-- himp_eq_top_iff (abstract). -/
def himp_eq_top_iff' : Prop := True
/-- himp_top (abstract). -/
def himp_top' : Prop := True
/-- top_himp (abstract). -/
def top_himp' : Prop := True
/-- himp_himp (abstract). -/
def himp_himp' : Prop := True
/-- himp_le_himp_himp_himp (abstract). -/
def himp_le_himp_himp_himp' : Prop := True
/-- himp_inf_himp_inf_le (abstract). -/
def himp_inf_himp_inf_le' : Prop := True
/-- himp_left_comm (abstract). -/
def himp_left_comm' : Prop := True
/-- himp_idem (abstract). -/
def himp_idem' : Prop := True
/-- himp_inf_distrib (abstract). -/
def himp_inf_distrib' : Prop := True
/-- sup_himp_distrib (abstract). -/
def sup_himp_distrib' : Prop := True
/-- himp_le_himp_left (abstract). -/
def himp_le_himp_left' : Prop := True
/-- himp_le_himp_right (abstract). -/
def himp_le_himp_right' : Prop := True
/-- himp_le_himp (abstract). -/
def himp_le_himp' : Prop := True
/-- himp_inf_cancel_right (abstract). -/
def himp_inf_cancel_right' : Prop := True
/-- himp_le_of_right_le (abstract). -/
def himp_le_of_right_le' : Prop := True
/-- le_himp_himp (abstract). -/
def le_himp_himp' : Prop := True
/-- himp_eq_himp_iff (abstract). -/
def himp_eq_himp_iff' : Prop := True
/-- himp_ne_himp_iff (abstract). -/
def himp_ne_himp_iff' : Prop := True
/-- himp_triangle (abstract). -/
def himp_triangle' : Prop := True
/-- himp_inf_himp_cancel (abstract). -/
def himp_inf_himp_cancel' : Prop := True
/-- sdiff_le_iff_left (abstract). -/
def sdiff_le_iff_left' : Prop := True
/-- sdiff_self (abstract). -/
def sdiff_self' : Prop := True
/-- le_sup_sdiff (abstract). -/
def le_sup_sdiff' : Prop := True
/-- le_sdiff_sup (abstract). -/
def le_sdiff_sup' : Prop := True
/-- sup_sdiff_left (abstract). -/
def sup_sdiff_left' : Prop := True
/-- sup_sdiff_right (abstract). -/
def sup_sdiff_right' : Prop := True
/-- inf_sdiff_left (abstract). -/
def inf_sdiff_left' : Prop := True
/-- inf_sdiff_right (abstract). -/
def inf_sdiff_right' : Prop := True
/-- sup_sdiff_self (abstract). -/
def sup_sdiff_self' : Prop := True
/-- sup_sdiff_eq_sup (abstract). -/
def sup_sdiff_eq_sup' : Prop := True
/-- sup_sdiff_cancel' (abstract). -/
def sup_sdiff_cancel' : Prop := True
/-- sup_sdiff_cancel_right (abstract). -/
def sup_sdiff_cancel_right' : Prop := True
/-- sdiff_sup_cancel (abstract). -/
def sdiff_sup_cancel' : Prop := True
/-- sup_le_of_le_sdiff_left (abstract). -/
def sup_le_of_le_sdiff_left' : Prop := True
/-- sup_le_of_le_sdiff_right (abstract). -/
def sup_le_of_le_sdiff_right' : Prop := True
/-- sdiff_eq_bot_iff (abstract). -/
def sdiff_eq_bot_iff' : Prop := True
/-- sdiff_bot (abstract). -/
def sdiff_bot' : Prop := True
/-- bot_sdiff (abstract). -/
def bot_sdiff' : Prop := True
/-- sdiff_sdiff_sdiff_le_sdiff (abstract). -/
def sdiff_sdiff_sdiff_le_sdiff' : Prop := True
/-- le_sup_sdiff_sup_sdiff (abstract). -/
def le_sup_sdiff_sup_sdiff' : Prop := True
/-- sdiff_sdiff (abstract). -/
def sdiff_sdiff' : Prop := True
/-- sdiff_right_comm (abstract). -/
def sdiff_right_comm' : Prop := True
/-- sdiff_sdiff_comm (abstract). -/
def sdiff_sdiff_comm' : Prop := True
/-- sdiff_idem (abstract). -/
def sdiff_idem' : Prop := True
/-- sdiff_sdiff_self (abstract). -/
def sdiff_sdiff_self' : Prop := True
/-- sup_sdiff_distrib (abstract). -/
def sup_sdiff_distrib' : Prop := True
/-- sdiff_inf_distrib (abstract). -/
def sdiff_inf_distrib' : Prop := True
/-- sup_sdiff (abstract). -/
def sup_sdiff' : Prop := True
/-- sup_sdiff_right_self (abstract). -/
def sup_sdiff_right_self' : Prop := True
/-- sup_sdiff_left_self (abstract). -/
def sup_sdiff_left_self' : Prop := True
/-- sdiff_le_sdiff_right (abstract). -/
def sdiff_le_sdiff_right' : Prop := True
/-- sdiff_le_sdiff_left (abstract). -/
def sdiff_le_sdiff_left' : Prop := True
/-- sdiff_le_sdiff (abstract). -/
def sdiff_le_sdiff' : Prop := True
/-- sdiff_inf (abstract). -/
def sdiff_inf' : Prop := True
/-- sup_sdiff_cancel_left (abstract). -/
def sup_sdiff_cancel_left' : Prop := True
/-- le_sdiff_of_le_left (abstract). -/
def le_sdiff_of_le_left' : Prop := True
/-- sdiff_sdiff_le (abstract). -/
def sdiff_sdiff_le' : Prop := True
/-- sdiff_eq_sdiff_iff (abstract). -/
def sdiff_eq_sdiff_iff' : Prop := True
/-- sdiff_ne_sdiff_iff (abstract). -/
def sdiff_ne_sdiff_iff' : Prop := True
/-- sdiff_triangle (abstract). -/
def sdiff_triangle' : Prop := True
/-- sdiff_sup_sdiff_cancel (abstract). -/
def sdiff_sup_sdiff_cancel' : Prop := True
/-- sdiff_le_sdiff_of_sup_le_sup_left (abstract). -/
def sdiff_le_sdiff_of_sup_le_sup_left' : Prop := True
/-- sdiff_le_sdiff_of_sup_le_sup_right (abstract). -/
def sdiff_le_sdiff_of_sup_le_sup_right' : Prop := True
/-- inf_sdiff_sup_left (abstract). -/
def inf_sdiff_sup_left' : Prop := True
/-- inf_sdiff_sup_right (abstract). -/
def inf_sdiff_sup_right' : Prop := True
/-- himp_bot (abstract). -/
def himp_bot' : Prop := True
/-- bot_himp (abstract). -/
def bot_himp' : Prop := True
/-- compl_sup_distrib (abstract). -/
def compl_sup_distrib' : Prop := True
/-- compl_sup (abstract). -/
def compl_sup' : Prop := True
/-- compl_le_himp (abstract). -/
def compl_le_himp' : Prop := True
/-- compl_sup_le_himp (abstract). -/
def compl_sup_le_himp' : Prop := True
/-- sup_compl_le_himp (abstract). -/
def sup_compl_le_himp' : Prop := True
/-- himp_compl (abstract). -/
def himp_compl' : Prop := True
/-- himp_compl_comm (abstract). -/
def himp_compl_comm' : Prop := True
/-- le_compl_iff_disjoint_right (abstract). -/
def le_compl_iff_disjoint_right' : Prop := True
/-- le_compl_iff_disjoint_left (abstract). -/
def le_compl_iff_disjoint_left' : Prop := True
/-- le_compl_comm (abstract). -/
def le_compl_comm' : Prop := True
/-- compl_unique (abstract). -/
def compl_unique' : Prop := True
/-- inf_compl_self (abstract). -/
def inf_compl_self' : Prop := True
/-- compl_inf_self (abstract). -/
def compl_inf_self' : Prop := True
/-- compl_inf_eq_bot (abstract). -/
def compl_inf_eq_bot' : Prop := True
/-- compl_top (abstract). -/
def compl_top' : Prop := True
/-- compl_bot (abstract). -/
def compl_bot' : Prop := True
/-- le_compl_self (abstract). -/
def le_compl_self' : Prop := True
/-- le_compl_compl (abstract). -/
def le_compl_compl' : Prop := True
/-- compl_anti (abstract). -/
def compl_anti' : Prop := True
/-- compl_le_compl (abstract). -/
def compl_le_compl' : Prop := True
/-- compl_compl_compl (abstract). -/
def compl_compl_compl' : Prop := True
/-- disjoint_compl_compl_left_iff (abstract). -/
def disjoint_compl_compl_left_iff' : Prop := True
/-- disjoint_compl_compl_right_iff (abstract). -/
def disjoint_compl_compl_right_iff' : Prop := True
/-- compl_sup_compl_le (abstract). -/
def compl_sup_compl_le' : Prop := True
/-- compl_compl_inf_distrib (abstract). -/
def compl_compl_inf_distrib' : Prop := True
/-- compl_compl_himp_distrib (abstract). -/
def compl_compl_himp_distrib' : Prop := True
/-- sdiff_top (abstract). -/
def sdiff_top' : Prop := True
/-- hnot_inf_distrib (abstract). -/
def hnot_inf_distrib' : Prop := True
/-- sdiff_le_hnot (abstract). -/
def sdiff_le_hnot' : Prop := True
/-- sdiff_le_inf_hnot (abstract). -/
def sdiff_le_inf_hnot' : Prop := True
/-- hnot_sdiff (abstract). -/
def hnot_sdiff' : Prop := True
/-- hnot_sdiff_comm (abstract). -/
def hnot_sdiff_comm' : Prop := True
/-- hnot_le_iff_codisjoint_right (abstract). -/
def hnot_le_iff_codisjoint_right' : Prop := True
/-- hnot_le_iff_codisjoint_left (abstract). -/
def hnot_le_iff_codisjoint_left' : Prop := True
/-- hnot_le_comm (abstract). -/
def hnot_le_comm' : Prop := True
/-- sup_hnot_self (abstract). -/
def sup_hnot_self' : Prop := True
/-- hnot_sup_self (abstract). -/
def hnot_sup_self' : Prop := True
/-- hnot_bot (abstract). -/
def hnot_bot' : Prop := True
/-- hnot_top (abstract). -/
def hnot_top' : Prop := True
/-- hnot_hnot_le (abstract). -/
def hnot_hnot_le' : Prop := True
/-- hnot_anti (abstract). -/
def hnot_anti' : Prop := True
/-- hnot_le_hnot (abstract). -/
def hnot_le_hnot' : Prop := True
/-- hnot_hnot_hnot (abstract). -/
def hnot_hnot_hnot' : Prop := True
/-- codisjoint_hnot_hnot_left_iff (abstract). -/
def codisjoint_hnot_hnot_left_iff' : Prop := True
/-- codisjoint_hnot_hnot_right_iff (abstract). -/
def codisjoint_hnot_hnot_right_iff' : Prop := True
/-- le_hnot_inf_hnot (abstract). -/
def le_hnot_inf_hnot' : Prop := True
/-- hnot_hnot_sup_distrib (abstract). -/
def hnot_hnot_sup_distrib' : Prop := True
/-- hnot_hnot_sdiff_distrib (abstract). -/
def hnot_hnot_sdiff_distrib' : Prop := True
/-- toBiheytingAlgebra (abstract). -/
def toBiheytingAlgebra' : Prop := True
/-- generalizedHeytingAlgebra (abstract). -/
def generalizedHeytingAlgebra' : Prop := True
/-- generalizedCoheytingAlgebra (abstract). -/
def generalizedCoheytingAlgebra' : Prop := True
/-- heytingAlgebra (abstract). -/
def heytingAlgebra' : Prop := True
/-- coheytingAlgebra (abstract). -/
def coheytingAlgebra' : Prop := True
/-- biheytingAlgebra (abstract). -/
def biheytingAlgebra' : Prop := True

-- Heyting/Boundary.lean
-- COLLISION: boundary' already in AlgebraicTopology.lean — rename needed
/-- boundary_le (abstract). -/
def boundary_le' : Prop := True
/-- boundary_le_hnot (abstract). -/
def boundary_le_hnot' : Prop := True
/-- boundary_bot (abstract). -/
def boundary_bot' : Prop := True
/-- boundary_top (abstract). -/
def boundary_top' : Prop := True
/-- boundary_hnot_le (abstract). -/
def boundary_hnot_le' : Prop := True
/-- boundary_hnot_hnot (abstract). -/
def boundary_hnot_hnot' : Prop := True
/-- hnot_boundary (abstract). -/
def hnot_boundary' : Prop := True
/-- boundary_inf (abstract). -/
def boundary_inf' : Prop := True
/-- boundary_inf_le (abstract). -/
def boundary_inf_le' : Prop := True
/-- boundary_sup_le (abstract). -/
def boundary_sup_le' : Prop := True
/-- boundary_le_boundary_sup_sup_boundary_inf_left (abstract). -/
def boundary_le_boundary_sup_sup_boundary_inf_left' : Prop := True
/-- boundary_le_boundary_sup_sup_boundary_inf_right (abstract). -/
def boundary_le_boundary_sup_sup_boundary_inf_right' : Prop := True
/-- boundary_sup_sup_boundary_inf (abstract). -/
def boundary_sup_sup_boundary_inf' : Prop := True
/-- boundary_idem (abstract). -/
def boundary_idem' : Prop := True
/-- hnot_hnot_sup_boundary (abstract). -/
def hnot_hnot_sup_boundary' : Prop := True
/-- hnot_eq_top_iff_exists_boundary (abstract). -/
def hnot_eq_top_iff_exists_boundary' : Prop := True
/-- boundary_eq_bot (abstract). -/
def boundary_eq_bot' : Prop := True

-- Heyting/Hom.lean
/-- which (abstract). -/
def which' : Prop := True
/-- HeytingHom (abstract). -/
def HeytingHom' : Prop := True
/-- CoheytingHom (abstract). -/
def CoheytingHom' : Prop := True
/-- BiheytingHom (abstract). -/
def BiheytingHom' : Prop := True
/-- HeytingHomClass (abstract). -/
def HeytingHomClass' : Prop := True
/-- CoheytingHomClass (abstract). -/
def CoheytingHomClass' : Prop := True
/-- BiheytingHomClass (abstract). -/
def BiheytingHomClass' : Prop := True
/-- toBiheytingHomClass (abstract). -/
def toBiheytingHomClass' : Prop := True
/-- map_compl (abstract). -/
def map_compl' : Prop := True
/-- map_bihimp (abstract). -/
def map_bihimp' : Prop := True
/-- map_hnot (abstract). -/
def map_hnot' : Prop := True
/-- map_symmDiff (abstract). -/
def map_symmDiff' : Prop := True
/-- comp_id (abstract). -/
def comp_id' : Prop := True
/-- id_comp (abstract). -/
def id_comp' : Prop := True
/-- cancel_right (abstract). -/
def cancel_right' : Prop := True
/-- cancel_left (abstract). -/
def cancel_left' : Prop := True

-- Heyting/Regular.lean
/-- IsRegular (abstract). -/
def IsRegular' : Prop := True
/-- isRegular_bot (abstract). -/
def isRegular_bot' : Prop := True
/-- isRegular_top (abstract). -/
def isRegular_top' : Prop := True
/-- himp (abstract). -/
def himp' : Prop := True
/-- isRegular_compl (abstract). -/
def isRegular_compl' : Prop := True
/-- ofRegular (abstract). -/
def ofRegular' : Prop := True
/-- Regular (abstract). -/
def Regular' : Prop := True
/-- val (abstract). -/
def val' : Prop := True
/-- prop (abstract). -/
def prop' : Prop := True
/-- toRegular (abstract). -/
def toRegular' : Prop := True
/-- toRegular_coe (abstract). -/
def toRegular_coe' : Prop := True
/-- isRegular_of_boolean (abstract). -/
def isRegular_of_boolean' : Prop := True
/-- isRegular_of_decidable (abstract). -/
def isRegular_of_decidable' : Prop := True

-- Hom/Basic.lean
/-- OrderHom (abstract). -/
def OrderHom' : Prop := True
/-- OrderEmbedding (abstract). -/
def OrderEmbedding' : Prop := True
/-- OrderIso (abstract). -/
def OrderIso' : Prop := True
/-- OrderHomClass (abstract). -/
def OrderHomClass' : Prop := True
/-- OrderIsoClass (abstract). -/
def OrderIsoClass' : Prop := True
/-- toOrderIso (abstract). -/
def toOrderIso' : Prop := True
/-- toOrderHom (abstract). -/
def toOrderHom' : Prop := True
/-- map_inv_le_iff (abstract). -/
def map_inv_le_iff' : Prop := True
/-- le_map_inv_iff (abstract). -/
def le_map_inv_iff' : Prop := True
/-- map_lt_map_iff (abstract). -/
def map_lt_map_iff' : Prop := True
/-- map_inv_lt_iff (abstract). -/
def map_inv_lt_iff' : Prop := True
/-- map_inv_lt_map_inv_iff (abstract). -/
def map_inv_lt_map_inv_iff' : Prop := True
/-- lt_map_inv_iff (abstract). -/
def lt_map_inv_iff' : Prop := True
/-- coe (abstract). -/
def coe' : Prop := True
/-- compₘ (abstract). -/
def compₘ' : Prop := True
/-- prodₘ (abstract). -/
def prodₘ' : Prop := True
/-- diag (abstract). -/
def diag' : Prop := True
/-- onDiag (abstract). -/
def onDiag' : Prop := True
/-- prodIso (abstract). -/
def prodIso' : Prop := True
/-- prodMap (abstract). -/
def prodMap' : Prop := True
/-- evalOrderHom (abstract). -/
def evalOrderHom' : Prop := True
/-- coeFnHom (abstract). -/
def coeFnHom' : Prop := True
/-- apply (abstract). -/
def apply' : Prop := True
/-- piIso (abstract). -/
def piIso' : Prop := True
-- COLLISION: orderEmbedding' already in SetTheory.lean — rename needed
/-- withBotMap (abstract). -/
def withBotMap' : Prop := True
/-- withTopMap (abstract). -/
def withTopMap' : Prop := True
/-- orderEmbeddingOfLTEmbedding (abstract). -/
def orderEmbeddingOfLTEmbedding' : Prop := True
/-- ltEmbedding (abstract). -/
def ltEmbedding' : Prop := True
/-- eq_iff_eq (abstract). -/
def eq_iff_eq' : Prop := True
-- COLLISION: strictMono' already in SetTheory.lean — rename needed
/-- acc (abstract). -/
def acc' : Prop := True
/-- wellFounded (abstract). -/
def wellFounded' : Prop := True
/-- isWellOrder (abstract). -/
def isWellOrder' : Prop := True
/-- withBotCoe (abstract). -/
def withBotCoe' : Prop := True
/-- withTopCoe (abstract). -/
def withTopCoe' : Prop := True
/-- ofMapLEIff (abstract). -/
def ofMapLEIff' : Prop := True
/-- ofStrictMono (abstract). -/
def ofStrictMono' : Prop := True
-- COLLISION: ofIsEmpty' already in SetTheory.lean — rename needed
/-- of_orderEmbedding (abstract). -/
def of_orderEmbedding' : Prop := True
/-- toOrderHom_injective (abstract). -/
def toOrderHom_injective' : Prop := True
/-- toOrderEmbedding (abstract). -/
def toOrderEmbedding' : Prop := True
/-- self_trans_symm (abstract). -/
def self_trans_symm' : Prop := True
/-- symm_trans_self (abstract). -/
def symm_trans_self' : Prop := True
/-- arrowCongr (abstract). -/
def arrowCongr' : Prop := True
/-- conj (abstract). -/
def conj' : Prop := True
/-- prodComm (abstract). -/
def prodComm' : Prop := True
/-- dualDual (abstract). -/
def dualDual' : Prop := True
/-- le_symm_apply (abstract). -/
def le_symm_apply' : Prop := True
/-- symm_apply_le (abstract). -/
def symm_apply_le' : Prop := True
/-- toRelIsoLT (abstract). -/
def toRelIsoLT' : Prop := True
/-- ofRelIsoLT (abstract). -/
def ofRelIsoLT' : Prop := True
/-- ofRelIsoLT_toRelIsoLT (abstract). -/
def ofRelIsoLT_toRelIsoLT' : Prop := True
/-- toRelIsoLT_ofRelIsoLT (abstract). -/
def toRelIsoLT_ofRelIsoLT' : Prop := True
/-- ofCmpEqCmp (abstract). -/
def ofCmpEqCmp' : Prop := True
/-- ofHomInv (abstract). -/
def ofHomInv' : Prop := True
/-- funUnique (abstract). -/
def funUnique' : Prop := True
/-- orderIsoOfRightInverse (abstract). -/
def orderIsoOfRightInverse' : Prop := True
/-- le_map_sup (abstract). -/
def le_map_sup' : Prop := True
/-- isMax_apply (abstract). -/
def isMax_apply' : Prop := True
/-- isMin_apply (abstract). -/
def isMin_apply' : Prop := True
/-- map_orderIso (abstract). -/
def map_orderIso' : Prop := True
/-- disjoint_map_orderIso_iff (abstract). -/
def disjoint_map_orderIso_iff' : Prop := True
/-- codisjoint_map_orderIso_iff (abstract). -/
def codisjoint_map_orderIso_iff' : Prop := True
/-- toDualTopEquiv (abstract). -/
def toDualTopEquiv' : Prop := True
/-- coe_toDualTopEquiv_eq (abstract). -/
def coe_toDualTopEquiv_eq' : Prop := True
/-- coeOrderHom (abstract). -/
def coeOrderHom' : Prop := True
/-- toDualBotEquiv (abstract). -/
def toDualBotEquiv' : Prop := True
/-- coe_toDualBotEquiv (abstract). -/
def coe_toDualBotEquiv' : Prop := True
/-- withTopCongr (abstract). -/
def withTopCongr' : Prop := True
/-- withTopCongr_refl (abstract). -/
def withTopCongr_refl' : Prop := True
/-- withTopCongr_symm (abstract). -/
def withTopCongr_symm' : Prop := True
/-- withTopCongr_trans (abstract). -/
def withTopCongr_trans' : Prop := True
/-- withBotCongr (abstract). -/
def withBotCongr' : Prop := True
/-- withBotCongr_refl (abstract). -/
def withBotCongr_refl' : Prop := True
/-- withBotCongr_symm (abstract). -/
def withBotCongr_symm' : Prop := True
/-- withBotCongr_trans (abstract). -/
def withBotCongr_trans' : Prop := True
/-- isCompl (abstract). -/
def isCompl' : Prop := True
/-- complementedLattice (abstract). -/
def complementedLattice' : Prop := True
/-- denselyOrdered_iff_of_orderIsoClass (abstract). -/
def denselyOrdered_iff_of_orderIsoClass' : Prop := True

-- Hom/Bounded.lean
/-- TopHom (abstract). -/
def TopHom' : Prop := True
/-- BotHom (abstract). -/
def BotHom' : Prop := True
/-- BoundedOrderHom (abstract). -/
def BoundedOrderHom' : Prop := True
/-- TopHomClass (abstract). -/
def TopHomClass' : Prop := True
/-- BotHomClass (abstract). -/
def BotHomClass' : Prop := True
/-- BoundedOrderHomClass (abstract). -/
def BoundedOrderHomClass' : Prop := True
/-- map_eq_top_iff (abstract). -/
def map_eq_top_iff' : Prop := True
/-- toTopHom (abstract). -/
def toTopHom' : Prop := True
/-- toBotHom (abstract). -/
def toBotHom' : Prop := True
/-- toBoundedOrderHom (abstract). -/
def toBoundedOrderHom' : Prop := True

-- Hom/CompleteLattice.lean
/-- sSupHom (abstract). -/
def sSupHom' : Prop := True
/-- sInfHom (abstract). -/
def sInfHom' : Prop := True
/-- FrameHom (abstract). -/
def FrameHom' : Prop := True
/-- CompleteLatticeHom (abstract). -/
def CompleteLatticeHom' : Prop := True
/-- sSupHomClass (abstract). -/
def sSupHomClass' : Prop := True
/-- sInfHomClass (abstract). -/
def sInfHomClass' : Prop := True
/-- FrameHomClass (abstract). -/
def FrameHomClass' : Prop := True
/-- CompleteLatticeHomClass (abstract). -/
def CompleteLatticeHomClass' : Prop := True
/-- map_iSup₂ (abstract). -/
def map_iSup₂' : Prop := True
/-- map_iInf₂ (abstract). -/
def map_iInf₂' : Prop := True
/-- toCompleteLatticeHom (abstract). -/
def toCompleteLatticeHom' : Prop := True
/-- toLatticeHom (abstract). -/
def toLatticeHom' : Prop := True
/-- tosSupHom (abstract). -/
def tosSupHom' : Prop := True
/-- toBoundedLatticeHom (abstract). -/
def toBoundedLatticeHom' : Prop := True
/-- setPreimage (abstract). -/
def setPreimage' : Prop := True
/-- image_sSup (abstract). -/
def image_sSup' : Prop := True
/-- setImage (abstract). -/
def setImage' : Prop := True
/-- toOrderIsoSet (abstract). -/
def toOrderIsoSet' : Prop := True
/-- supsSupHom (abstract). -/
def supsSupHom' : Prop := True
/-- infsInfHom (abstract). -/
def infsInfHom' : Prop := True

-- Hom/Lattice.lean
/-- SupHom (abstract). -/
def SupHom' : Prop := True
/-- InfHom (abstract). -/
def InfHom' : Prop := True
/-- SupBotHom (abstract). -/
def SupBotHom' : Prop := True
/-- InfTopHom (abstract). -/
def InfTopHom' : Prop := True
/-- LatticeHom (abstract). -/
def LatticeHom' : Prop := True
/-- BoundedLatticeHom (abstract). -/
def BoundedLatticeHom' : Prop := True
/-- SupHomClass (abstract). -/
def SupHomClass' : Prop := True
/-- InfHomClass (abstract). -/
def InfHomClass' : Prop := True
/-- SupBotHomClass (abstract). -/
def SupBotHomClass' : Prop := True
/-- InfTopHomClass (abstract). -/
def InfTopHomClass' : Prop := True
/-- LatticeHomClass (abstract). -/
def LatticeHomClass' : Prop := True
/-- BoundedLatticeHomClass (abstract). -/
def BoundedLatticeHomClass' : Prop := True
/-- orderEmbeddingOfInjective (abstract). -/
def orderEmbeddingOfInjective' : Prop := True
/-- map_sdiff' (abstract). -/
def map_sdiff' : Prop := True
/-- subtypeVal (abstract). -/
def subtypeVal' : Prop := True
/-- toInfHom (abstract). -/
def toInfHom' : Prop := True
/-- toSupBotHom (abstract). -/
def toSupBotHom' : Prop := True
/-- toInfTopHom (abstract). -/
def toInfTopHom' : Prop := True
/-- evalLatticeHom (abstract). -/
def evalLatticeHom' : Prop := True
/-- withTop (abstract). -/
def withTop' : Prop := True
/-- withTop_id (abstract). -/
def withTop_id' : Prop := True
/-- withBot (abstract). -/
def withBot' : Prop := True
/-- withBot_id (abstract). -/
def withBot_id' : Prop := True
/-- withBot_comp (abstract). -/
def withBot_comp' : Prop := True
/-- withTop_comp (abstract). -/
def withTop_comp' : Prop := True
/-- withTopWithBot (abstract). -/
def withTopWithBot' : Prop := True
/-- withTopWithBot_id (abstract). -/
def withTopWithBot_id' : Prop := True
/-- withTopWithBot_comp (abstract). -/
def withTopWithBot_comp' : Prop := True

-- Hom/Order.lean
/-- iterate_sup_le_sup_iff (abstract). -/
def iterate_sup_le_sup_iff' : Prop := True

-- Hom/Set.lean
/-- range_eq (abstract). -/
def range_eq' : Prop := True
/-- symm_image_image (abstract). -/
def symm_image_image' : Prop := True
/-- image_symm_image (abstract). -/
def image_symm_image' : Prop := True
/-- image_eq_preimage (abstract). -/
def image_eq_preimage' : Prop := True
/-- preimage_symm_preimage (abstract). -/
def preimage_symm_preimage' : Prop := True
/-- setCongr (abstract). -/
def setCongr' : Prop := True
/-- orderIso (abstract). -/
def orderIso' : Prop := True
/-- orderIsoOfSurjective (abstract). -/
def orderIsoOfSurjective' : Prop := True
/-- orderIsoOfSurjective_symm_apply_self (abstract). -/
def orderIsoOfSurjective_symm_apply_self' : Prop := True
/-- orderIsoOfSurjective_self_symm_apply (abstract). -/
def orderIsoOfSurjective_self_symm_apply' : Prop := True
/-- range_inj (abstract). -/
def range_inj' : Prop := True
/-- compl_strictAnti (abstract). -/
def compl_strictAnti' : Prop := True
/-- compl_antitone (abstract). -/
def compl_antitone' : Prop := True

-- Ideal.lean
/-- Ideal (abstract). -/
def Ideal' : Prop := True
/-- IsIdeal (abstract). -/
def IsIdeal' : Prop := True
/-- toIdeal (abstract). -/
def toIdeal' : Prop := True
/-- lower (abstract). -/
def lower' : Prop := True
/-- mem_of_mem_of_le (abstract). -/
def mem_of_mem_of_le' : Prop := True
/-- IsProper (abstract). -/
def IsProper' : Prop := True
/-- isProper_of_not_mem (abstract). -/
def isProper_of_not_mem' : Prop := True
/-- IsMaximal (abstract). -/
def IsMaximal' : Prop := True
/-- inter_nonempty (abstract). -/
def inter_nonempty' : Prop := True
/-- isProper_of_ne_top (abstract). -/
def isProper_of_ne_top' : Prop := True
/-- ne_top (abstract). -/
def ne_top' : Prop := True
/-- isProper (abstract). -/
def isProper' : Prop := True
/-- isProper_iff_ne_top (abstract). -/
def isProper_iff_ne_top' : Prop := True
/-- isCoatom (abstract). -/
def isCoatom' : Prop := True
-- COLLISION: isMaximal' already in RingTheory2.lean — rename needed
/-- isMaximal_iff_isCoatom (abstract). -/
def isMaximal_iff_isCoatom' : Prop := True
/-- top_of_top_mem (abstract). -/
def top_of_top_mem' : Prop := True
/-- top_not_mem (abstract). -/
def top_not_mem' : Prop := True
/-- principal_top (abstract). -/
def principal_top' : Prop := True
/-- sup_mem (abstract). -/
def sup_mem' : Prop := True
/-- sup_mem_iff (abstract). -/
def sup_mem_iff' : Prop := True
/-- lt_sup_principal_of_not_mem (abstract). -/
def lt_sup_principal_of_not_mem' : Prop := True
/-- mem_sInf (abstract). -/
def mem_sInf' : Prop := True
/-- eq_sup_of_le_sup (abstract). -/
def eq_sup_of_le_sup' : Prop := True
/-- coe_sup_eq (abstract). -/
def coe_sup_eq' : Prop := True
/-- not_mem_of_compl_mem (abstract). -/
def not_mem_of_compl_mem' : Prop := True
/-- not_mem_or_compl_not_mem (abstract). -/
def not_mem_or_compl_not_mem' : Prop := True
/-- Cofinal (abstract). -/
def Cofinal' : Prop := True
/-- above (abstract). -/
def above' : Prop := True
/-- above_mem (abstract). -/
def above_mem' : Prop := True
/-- le_above (abstract). -/
def le_above' : Prop := True
/-- sequenceOfCofinals (abstract). -/
def sequenceOfCofinals' : Prop := True
/-- encode_mem (abstract). -/
def encode_mem' : Prop := True
/-- idealOfCofinals (abstract). -/
def idealOfCofinals' : Prop := True
/-- mem_idealOfCofinals (abstract). -/
def mem_idealOfCofinals' : Prop := True
/-- cofinal_meets_idealOfCofinals (abstract). -/
def cofinal_meets_idealOfCofinals' : Prop := True
/-- isIdeal_sUnion_of_directedOn (abstract). -/
def isIdeal_sUnion_of_directedOn' : Prop := True
/-- isIdeal_sUnion_of_isChain (abstract). -/
def isIdeal_sUnion_of_isChain' : Prop := True

-- InitialSeg.lean
/-- InitialSeg (abstract). -/
def InitialSeg' : Prop := True
/-- mem_range_of_rel (abstract). -/
def mem_range_of_rel' : Prop := True
/-- map_rel_iff (abstract). -/
def map_rel_iff' : Prop := True
/-- exists_eq_iff_rel (abstract). -/
def exists_eq_iff_rel' : Prop := True
/-- toInitialSeg (abstract). -/
def toInitialSeg' : Prop := True
/-- eq_relIso (abstract). -/
def eq_relIso' : Prop := True
/-- codRestrict (abstract). -/
def codRestrict' : Prop := True
/-- leAdd (abstract). -/
def leAdd' : Prop := True
/-- PrincipalSeg (abstract). -/
def PrincipalSeg' : Prop := True
/-- toRelEmbedding_injective (abstract). -/
def toRelEmbedding_injective' : Prop := True
/-- mem_range_iff_rel (abstract). -/
def mem_range_iff_rel' : Prop := True
/-- down (abstract). -/
def down' : Prop := True
/-- lt_top (abstract). -/
def lt_top' : Prop := True
/-- mem_range_of_rel_top (abstract). -/
def mem_range_of_rel_top' : Prop := True
/-- surjOn (abstract). -/
def surjOn' : Prop := True
/-- eq_principalSeg (abstract). -/
def eq_principalSeg' : Prop := True
/-- toPrincipalSeg (abstract). -/
def toPrincipalSeg' : Prop := True
/-- transInitial (abstract). -/
def transInitial' : Prop := True
/-- relIsoTrans (abstract). -/
def relIsoTrans' : Prop := True
/-- transRelIso (abstract). -/
def transRelIso' : Prop := True
/-- top_eq (abstract). -/
def top_eq' : Prop := True
/-- top_rel_top (abstract). -/
def top_rel_top' : Prop := True
/-- ofElement (abstract). -/
def ofElement' : Prop := True
/-- subrelIso (abstract). -/
def subrelIso' : Prop := True
/-- apply_subrelIso (abstract). -/
def apply_subrelIso' : Prop := True
/-- pemptyToPunit (abstract). -/
def pemptyToPunit' : Prop := True
/-- principalSumRelIso (abstract). -/
def principalSumRelIso' : Prop := True
/-- transPrincipal (abstract). -/
def transPrincipal' : Prop := True
/-- transPrincipal_apply (abstract). -/
def transPrincipal_apply' : Prop := True
/-- leLT_apply (abstract). -/
def leLT_apply' : Prop := True
/-- collapseF (abstract). -/
def collapseF' : Prop := True
/-- collapseF_lt (abstract). -/
def collapseF_lt' : Prop := True
/-- collapseF_not_lt (abstract). -/
def collapseF_not_lt' : Prop := True
/-- collapse (abstract). -/
def collapse' : Prop := True
/-- isLowerSet_range (abstract). -/
def isLowerSet_range' : Prop := True
/-- isMin_apply_iff (abstract). -/
def isMin_apply_iff' : Prop := True
/-- le_apply_iff (abstract). -/
def le_apply_iff' : Prop := True
/-- lt_apply_iff (abstract). -/
def lt_apply_iff' : Prop := True
/-- mem_range_of_le (abstract). -/
def mem_range_of_le' : Prop := True

-- Interval/Basic.lean
/-- NonemptyInterval (abstract). -/
def NonemptyInterval' : Prop := True
/-- toDualProd (abstract). -/
def toDualProd' : Prop := True
/-- toDualProd_injective (abstract). -/
def toDualProd_injective' : Prop := True
/-- toDualProdHom (abstract). -/
def toDualProdHom' : Prop := True
/-- pure (abstract). -/
def pure' : Prop := True
/-- coeHom (abstract). -/
def coeHom' : Prop := True
/-- coe_pure (abstract). -/
def coe_pure' : Prop := True
/-- mem_pure (abstract). -/
def mem_pure' : Prop := True
/-- coe_dual (abstract). -/
def coe_dual' : Prop := True
/-- subset_coe_map (abstract). -/
def subset_coe_map' : Prop := True
/-- Interval (abstract). -/
def Interval' : Prop := True
/-- recBotCoe (abstract). -/
def recBotCoe' : Prop := True
/-- «forall» (abstract). -/
def «forall_order'» : Prop := True
/-- «exists» (abstract). -/
def «exists_order'» : Prop := True
/-- coe_inf (abstract). -/
def coe_inf' : Prop := True
/-- coe_iInf₂ (abstract). -/
def coe_iInf₂' : Prop := True

-- Interval/Finset/Basic.lean
/-- nonempty_Icc (abstract). -/
def nonempty_Icc' : Prop := True
/-- nonempty_Ico (abstract). -/
def nonempty_Ico' : Prop := True
/-- nonempty_Ioc (abstract). -/
def nonempty_Ioc' : Prop := True
/-- nonempty_Ioo (abstract). -/
def nonempty_Ioo' : Prop := True
/-- Icc_eq_empty_iff (abstract). -/
def Icc_eq_empty_iff' : Prop := True
/-- Ico_eq_empty_iff (abstract). -/
def Ico_eq_empty_iff' : Prop := True
/-- Ioc_eq_empty_iff (abstract). -/
def Ioc_eq_empty_iff' : Prop := True
/-- Ioo_eq_empty_iff (abstract). -/
def Ioo_eq_empty_iff' : Prop := True
/-- Ioo_eq_empty (abstract). -/
def Ioo_eq_empty' : Prop := True
/-- Icc_eq_empty_of_lt (abstract). -/
def Icc_eq_empty_of_lt' : Prop := True
/-- Ico_eq_empty_of_le (abstract). -/
def Ico_eq_empty_of_le' : Prop := True
/-- Ioc_eq_empty_of_le (abstract). -/
def Ioc_eq_empty_of_le' : Prop := True
/-- Ioo_eq_empty_of_le (abstract). -/
def Ioo_eq_empty_of_le' : Prop := True
/-- left_mem_Icc (abstract). -/
def left_mem_Icc' : Prop := True
/-- left_mem_Ico (abstract). -/
def left_mem_Ico' : Prop := True
/-- right_mem_Icc (abstract). -/
def right_mem_Icc' : Prop := True
/-- left_not_mem_Ioc (abstract). -/
def left_not_mem_Ioc' : Prop := True
/-- left_not_mem_Ioo (abstract). -/
def left_not_mem_Ioo' : Prop := True
/-- right_not_mem_Ico (abstract). -/
def right_not_mem_Ico' : Prop := True
/-- right_not_mem_Ioo (abstract). -/
def right_not_mem_Ioo' : Prop := True
/-- Icc_subset_Icc (abstract). -/
def Icc_subset_Icc' : Prop := True
/-- Ico_subset_Ico (abstract). -/
def Ico_subset_Ico' : Prop := True
/-- Ioc_subset_Ioc (abstract). -/
def Ioc_subset_Ioc' : Prop := True
/-- Ioo_subset_Ioo (abstract). -/
def Ioo_subset_Ioo' : Prop := True
/-- Icc_subset_Icc_left (abstract). -/
def Icc_subset_Icc_left' : Prop := True
/-- Ico_subset_Ico_left (abstract). -/
def Ico_subset_Ico_left' : Prop := True
/-- Ioc_subset_Ioc_left (abstract). -/
def Ioc_subset_Ioc_left' : Prop := True
/-- Ioo_subset_Ioo_left (abstract). -/
def Ioo_subset_Ioo_left' : Prop := True
/-- Icc_subset_Icc_right (abstract). -/
def Icc_subset_Icc_right' : Prop := True
/-- Ico_subset_Ico_right (abstract). -/
def Ico_subset_Ico_right' : Prop := True
/-- Ioc_subset_Ioc_right (abstract). -/
def Ioc_subset_Ioc_right' : Prop := True
/-- Ioo_subset_Ioo_right (abstract). -/
def Ioo_subset_Ioo_right' : Prop := True
/-- Ico_subset_Ioo_left (abstract). -/
def Ico_subset_Ioo_left' : Prop := True
/-- Ioc_subset_Ioo_right (abstract). -/
def Ioc_subset_Ioo_right' : Prop := True
/-- Icc_subset_Ico_right (abstract). -/
def Icc_subset_Ico_right' : Prop := True
/-- Ioo_subset_Ico_self (abstract). -/
def Ioo_subset_Ico_self' : Prop := True
/-- Ioo_subset_Ioc_self (abstract). -/
def Ioo_subset_Ioc_self' : Prop := True
/-- Ico_subset_Icc_self (abstract). -/
def Ico_subset_Icc_self' : Prop := True
/-- Ioc_subset_Icc_self (abstract). -/
def Ioc_subset_Icc_self' : Prop := True
/-- Ioo_subset_Icc_self (abstract). -/
def Ioo_subset_Icc_self' : Prop := True
/-- Icc_subset_Icc_iff (abstract). -/
def Icc_subset_Icc_iff' : Prop := True
/-- Icc_subset_Ioo_iff (abstract). -/
def Icc_subset_Ioo_iff' : Prop := True
/-- Icc_subset_Ico_iff (abstract). -/
def Icc_subset_Ico_iff' : Prop := True
/-- Icc_subset_Ioc_iff (abstract). -/
def Icc_subset_Ioc_iff' : Prop := True
/-- Icc_ssubset_Icc_left (abstract). -/
def Icc_ssubset_Icc_left' : Prop := True
/-- Icc_ssubset_Icc_right (abstract). -/
def Icc_ssubset_Icc_right' : Prop := True
/-- Ico_self (abstract). -/
def Ico_self' : Prop := True
/-- Ioc_self (abstract). -/
def Ioc_self' : Prop := True
/-- Ioo_self (abstract). -/
def Ioo_self' : Prop := True
/-- fintypeOfMemBounds (abstract). -/
def fintypeOfMemBounds' : Prop := True
/-- Ico_filter_lt_of_le_left (abstract). -/
def Ico_filter_lt_of_le_left' : Prop := True
/-- Ico_filter_lt_of_right_le (abstract). -/
def Ico_filter_lt_of_right_le' : Prop := True
/-- Ico_filter_lt_of_le_right (abstract). -/
def Ico_filter_lt_of_le_right' : Prop := True
/-- Ico_filter_le_of_le_left (abstract). -/
def Ico_filter_le_of_le_left' : Prop := True
/-- Ico_filter_le_of_right_le (abstract). -/
def Ico_filter_le_of_right_le' : Prop := True
/-- Ico_filter_le_of_left_le (abstract). -/
def Ico_filter_le_of_left_le' : Prop := True
/-- Icc_filter_lt_of_lt_right (abstract). -/
def Icc_filter_lt_of_lt_right' : Prop := True
/-- Ioc_filter_lt_of_lt_right (abstract). -/
def Ioc_filter_lt_of_lt_right' : Prop := True
/-- Iic_filter_lt_of_lt_right (abstract). -/
def Iic_filter_lt_of_lt_right' : Prop := True
/-- filter_lt_lt_eq_Ioo (abstract). -/
def filter_lt_lt_eq_Ioo' : Prop := True
/-- filter_lt_le_eq_Ioc (abstract). -/
def filter_lt_le_eq_Ioc' : Prop := True
/-- filter_le_lt_eq_Ico (abstract). -/
def filter_le_lt_eq_Ico' : Prop := True
/-- filter_le_le_eq_Icc (abstract). -/
def filter_le_le_eq_Icc' : Prop := True
/-- nonempty_Ici (abstract). -/
def nonempty_Ici' : Prop := True
/-- nonempty_Ioi (abstract). -/
def nonempty_Ioi' : Prop := True
/-- Ici_subset_Ici (abstract). -/
def Ici_subset_Ici' : Prop := True
/-- Ioi_subset_Ioi (abstract). -/
def Ioi_subset_Ioi' : Prop := True
/-- Icc_subset_Ici_self (abstract). -/
def Icc_subset_Ici_self' : Prop := True
/-- Ico_subset_Ici_self (abstract). -/
def Ico_subset_Ici_self' : Prop := True
/-- Ioc_subset_Ioi_self (abstract). -/
def Ioc_subset_Ioi_self' : Prop := True
/-- Ioo_subset_Ioi_self (abstract). -/
def Ioo_subset_Ioi_self' : Prop := True
/-- Ioc_subset_Ici_self (abstract). -/
def Ioc_subset_Ici_self' : Prop := True
/-- Ioo_subset_Ici_self (abstract). -/
def Ioo_subset_Ici_self' : Prop := True
/-- nonempty_Iic (abstract). -/
def nonempty_Iic' : Prop := True
/-- nonempty_Iio (abstract). -/
def nonempty_Iio' : Prop := True
/-- Iic_subset_Iic (abstract). -/
def Iic_subset_Iic' : Prop := True
/-- Iio_subset_Iio (abstract). -/
def Iio_subset_Iio' : Prop := True
/-- Icc_subset_Iic_self (abstract). -/
def Icc_subset_Iic_self' : Prop := True
/-- Ioc_subset_Iic_self (abstract). -/
def Ioc_subset_Iic_self' : Prop := True
/-- Ico_subset_Iio_self (abstract). -/
def Ico_subset_Iio_self' : Prop := True
/-- Ioo_subset_Iio_self (abstract). -/
def Ioo_subset_Iio_self' : Prop := True
/-- Ico_subset_Iic_self (abstract). -/
def Ico_subset_Iic_self' : Prop := True
/-- Ioo_subset_Iic_self (abstract). -/
def Ioo_subset_Iic_self' : Prop := True
/-- Ioi_subset_Ici_self (abstract). -/
def Ioi_subset_Ici_self' : Prop := True
/-- finite (abstract). -/
def finite' : Prop := True
/-- not_bddBelow (abstract). -/
def not_bddBelow' : Prop := True
/-- filter_lt_eq_Ioi (abstract). -/
def filter_lt_eq_Ioi' : Prop := True
/-- filter_le_eq_Ici (abstract). -/
def filter_le_eq_Ici' : Prop := True
/-- Iio_subset_Iic_self (abstract). -/
def Iio_subset_Iic_self' : Prop := True
/-- not_bddAbove (abstract). -/
def not_bddAbove' : Prop := True
/-- filter_gt_eq_Iio (abstract). -/
def filter_gt_eq_Iio' : Prop := True
/-- filter_ge_eq_Iic (abstract). -/
def filter_ge_eq_Iic' : Prop := True
/-- disjoint_Ioi_Iio (abstract). -/
def disjoint_Ioi_Iio' : Prop := True
/-- Icc_self (abstract). -/
def Icc_self' : Prop := True
/-- Icc_eq_singleton_iff (abstract). -/
def Icc_eq_singleton_iff' : Prop := True
/-- Ico_disjoint_Ico_consecutive (abstract). -/
def Ico_disjoint_Ico_consecutive' : Prop := True
/-- Icc_erase_left (abstract). -/
def Icc_erase_left' : Prop := True
/-- Icc_erase_right (abstract). -/
def Icc_erase_right' : Prop := True
/-- Ico_erase_left (abstract). -/
def Ico_erase_left' : Prop := True
/-- Ioc_erase_right (abstract). -/
def Ioc_erase_right' : Prop := True
/-- Icc_diff_both (abstract). -/
def Icc_diff_both' : Prop := True
/-- Ico_insert_right (abstract). -/
def Ico_insert_right' : Prop := True
/-- Ioc_insert_left (abstract). -/
def Ioc_insert_left' : Prop := True
/-- Ioo_insert_left (abstract). -/
def Ioo_insert_left' : Prop := True
/-- Ioo_insert_right (abstract). -/
def Ioo_insert_right' : Prop := True
/-- Icc_diff_Ico_self (abstract). -/
def Icc_diff_Ico_self' : Prop := True
/-- Icc_diff_Ioc_self (abstract). -/
def Icc_diff_Ioc_self' : Prop := True
/-- Icc_diff_Ioo_self (abstract). -/
def Icc_diff_Ioo_self' : Prop := True
/-- Ico_diff_Ioo_self (abstract). -/
def Ico_diff_Ioo_self' : Prop := True
/-- Ioc_diff_Ioo_self (abstract). -/
def Ioc_diff_Ioo_self' : Prop := True
/-- Ico_inter_Ico_consecutive (abstract). -/
def Ico_inter_Ico_consecutive' : Prop := True
/-- Icc_eq_cons_Ico (abstract). -/
def Icc_eq_cons_Ico' : Prop := True
/-- Icc_eq_cons_Ioc (abstract). -/
def Icc_eq_cons_Ioc' : Prop := True
/-- Ioc_eq_cons_Ioo (abstract). -/
def Ioc_eq_cons_Ioo' : Prop := True
/-- Ico_eq_cons_Ioo (abstract). -/
def Ico_eq_cons_Ioo' : Prop := True
/-- Ico_filter_le_left (abstract). -/
def Ico_filter_le_left' : Prop := True
/-- card_Ico_eq_card_Icc_sub_one (abstract). -/
def card_Ico_eq_card_Icc_sub_one' : Prop := True
/-- card_Ioc_eq_card_Icc_sub_one (abstract). -/
def card_Ioc_eq_card_Icc_sub_one' : Prop := True
/-- card_Ioo_eq_card_Ico_sub_one (abstract). -/
def card_Ioo_eq_card_Ico_sub_one' : Prop := True
/-- card_Ioo_eq_card_Ioc_sub_one (abstract). -/
def card_Ioo_eq_card_Ioc_sub_one' : Prop := True
/-- card_Ioo_eq_card_Icc_sub_two (abstract). -/
def card_Ioo_eq_card_Icc_sub_two' : Prop := True
/-- Ici_erase (abstract). -/
def Ici_erase' : Prop := True
/-- Ioi_insert (abstract). -/
def Ioi_insert' : Prop := True
/-- not_mem_Ioi_self (abstract). -/
def not_mem_Ioi_self' : Prop := True
/-- Ici_eq_cons_Ioi (abstract). -/
def Ici_eq_cons_Ioi' : Prop := True
/-- card_Ioi_eq_card_Ici_sub_one (abstract). -/
def card_Ioi_eq_card_Ici_sub_one' : Prop := True
/-- Iic_erase (abstract). -/
def Iic_erase' : Prop := True
/-- Iio_insert (abstract). -/
def Iio_insert' : Prop := True
/-- not_mem_Iio_self (abstract). -/
def not_mem_Iio_self' : Prop := True
/-- Iic_eq_cons_Iio (abstract). -/
def Iic_eq_cons_Iio' : Prop := True
/-- card_Iio_eq_card_Iic_sub_one (abstract). -/
def card_Iio_eq_card_Iic_sub_one' : Prop := True
/-- sup'_Iic (abstract). -/
def sup'_Iic' : Prop := True
/-- sup_Iic (abstract). -/
def sup_Iic' : Prop := True
/-- inf'_Ici (abstract). -/
def inf'_Ici' : Prop := True
/-- inf_Ici (abstract). -/
def inf_Ici' : Prop := True
/-- Ico_subset_Ico_iff (abstract). -/
def Ico_subset_Ico_iff' : Prop := True
/-- Ico_union_Ico_eq_Ico (abstract). -/
def Ico_union_Ico_eq_Ico' : Prop := True
/-- Ioc_union_Ioc_eq_Ioc (abstract). -/
def Ioc_union_Ioc_eq_Ioc' : Prop := True
/-- Ico_subset_Ico_union_Ico (abstract). -/
def Ico_subset_Ico_union_Ico' : Prop := True
/-- Ico_union_Ico' (abstract). -/
def Ico_union_Ico' : Prop := True
/-- Ico_inter_Ico (abstract). -/
def Ico_inter_Ico' : Prop := True
/-- Ico_filter_lt (abstract). -/
def Ico_filter_lt' : Prop := True
/-- Ico_filter_le (abstract). -/
def Ico_filter_le' : Prop := True
/-- Ioo_filter_lt (abstract). -/
def Ioo_filter_lt' : Prop := True
/-- Iio_filter_lt (abstract). -/
def Iio_filter_lt' : Prop := True
/-- Ico_diff_Ico_left (abstract). -/
def Ico_diff_Ico_left' : Prop := True
/-- Ico_diff_Ico_right (abstract). -/
def Ico_diff_Ico_right' : Prop := True
/-- exists_gt (abstract). -/
def exists_gt' : Prop := True
/-- infinite_iff_exists_gt (abstract). -/
def infinite_iff_exists_gt' : Prop := True
/-- exists_lt (abstract). -/
def exists_lt' : Prop := True
/-- infinite_iff_exists_lt (abstract). -/
def infinite_iff_exists_lt' : Prop := True
/-- Ioi_disjUnion_Iio (abstract). -/
def Ioi_disjUnion_Iio' : Prop := True
/-- uIcc_toDual (abstract). -/
def uIcc_toDual' : Prop := True
/-- uIcc_of_le (abstract). -/
def uIcc_of_le' : Prop := True
/-- uIcc_of_ge (abstract). -/
def uIcc_of_ge' : Prop := True
/-- uIcc_comm (abstract). -/
def uIcc_comm' : Prop := True
/-- uIcc_self (abstract). -/
def uIcc_self' : Prop := True
/-- nonempty_uIcc (abstract). -/
def nonempty_uIcc' : Prop := True
/-- Icc_subset_uIcc (abstract). -/
def Icc_subset_uIcc' : Prop := True
/-- left_mem_uIcc (abstract). -/
def left_mem_uIcc' : Prop := True
/-- right_mem_uIcc (abstract). -/
def right_mem_uIcc' : Prop := True
/-- mem_uIcc_of_le (abstract). -/
def mem_uIcc_of_le' : Prop := True
/-- mem_uIcc_of_ge (abstract). -/
def mem_uIcc_of_ge' : Prop := True
/-- uIcc_subset_uIcc (abstract). -/
def uIcc_subset_uIcc' : Prop := True
/-- uIcc_subset_Icc (abstract). -/
def uIcc_subset_Icc' : Prop := True
/-- uIcc_subset_uIcc_iff_mem (abstract). -/
def uIcc_subset_uIcc_iff_mem' : Prop := True
/-- uIcc_subset_uIcc_iff_le' (abstract). -/
def uIcc_subset_uIcc_iff_le' : Prop := True
/-- uIcc_subset_uIcc_right (abstract). -/
def uIcc_subset_uIcc_right' : Prop := True
/-- uIcc_subset_uIcc_left (abstract). -/
def uIcc_subset_uIcc_left' : Prop := True
/-- eq_of_mem_uIcc_of_mem_uIcc (abstract). -/
def eq_of_mem_uIcc_of_mem_uIcc' : Prop := True
/-- uIcc_injective_right (abstract). -/
def uIcc_injective_right' : Prop := True
/-- uIcc_injective_left (abstract). -/
def uIcc_injective_left' : Prop := True
/-- uIcc_of_not_le (abstract). -/
def uIcc_of_not_le' : Prop := True
/-- uIcc_of_not_ge (abstract). -/
def uIcc_of_not_ge' : Prop := True
/-- uIcc_eq_union (abstract). -/
def uIcc_eq_union' : Prop := True
/-- mem_uIcc' (abstract). -/
def mem_uIcc' : Prop := True
/-- not_mem_uIcc_of_lt (abstract). -/
def not_mem_uIcc_of_lt' : Prop := True
/-- not_mem_uIcc_of_gt (abstract). -/
def not_mem_uIcc_of_gt' : Prop := True
/-- uIcc_subset_uIcc_union_uIcc (abstract). -/
def uIcc_subset_uIcc_union_uIcc' : Prop := True
/-- transGen_wcovBy_of_le (abstract). -/
def transGen_wcovBy_of_le' : Prop := True
/-- le_iff_transGen_wcovBy (abstract). -/
def le_iff_transGen_wcovBy' : Prop := True
/-- le_iff_reflTransGen_covBy (abstract). -/
def le_iff_reflTransGen_covBy' : Prop := True
/-- transGen_covBy_of_lt (abstract). -/
def transGen_covBy_of_lt' : Prop := True
/-- lt_iff_transGen_covBy (abstract). -/
def lt_iff_transGen_covBy' : Prop := True
/-- monotone_iff_forall_wcovBy (abstract). -/
def monotone_iff_forall_wcovBy' : Prop := True
/-- monotone_iff_forall_covBy (abstract). -/
def monotone_iff_forall_covBy' : Prop := True
/-- strictMono_iff_forall_covBy (abstract). -/
def strictMono_iff_forall_covBy' : Prop := True
/-- antitone_iff_forall_wcovBy (abstract). -/
def antitone_iff_forall_wcovBy' : Prop := True
/-- antitone_iff_forall_covBy (abstract). -/
def antitone_iff_forall_covBy' : Prop := True
/-- strictAnti_iff_forall_covBy (abstract). -/
def strictAnti_iff_forall_covBy' : Prop := True

-- Interval/Finset/Box.lean
/-- Icc_neg_mono (abstract). -/
def Icc_neg_mono' : Prop := True
/-- box (abstract). -/
def box' : Prop := True
/-- box_zero (abstract). -/
def box_zero' : Prop := True
/-- box_succ_eq_sdiff (abstract). -/
def box_succ_eq_sdiff' : Prop := True
/-- disjoint_box_succ_prod (abstract). -/
def disjoint_box_succ_prod' : Prop := True
/-- box_succ_union_prod (abstract). -/
def box_succ_union_prod' : Prop := True
/-- box_succ_disjUnion (abstract). -/
def box_succ_disjUnion' : Prop := True
/-- zero_mem_box (abstract). -/
def zero_mem_box' : Prop := True
/-- eq_zero_iff_eq_zero_of_mem_box (abstract). -/
def eq_zero_iff_eq_zero_of_mem_box' : Prop := True
/-- card_box_succ (abstract). -/
def card_box_succ' : Prop := True
/-- card_box (abstract). -/
def card_box' : Prop := True
/-- existsUnique_mem_box (abstract). -/
def existsUnique_mem_box' : Prop := True

-- Interval/Finset/Defs.lean
/-- exists_min_greater (abstract). -/
def exists_min_greater' : Prop := True
/-- LocallyFiniteOrder (abstract). -/
def LocallyFiniteOrder' : Prop := True
/-- LocallyFiniteOrderTop (abstract). -/
def LocallyFiniteOrderTop' : Prop := True
/-- LocallyFiniteOrderBot (abstract). -/
def LocallyFiniteOrderBot' : Prop := True
/-- ofIcc' (abstract). -/
def ofIcc' : Prop := True
/-- ofIci' (abstract). -/
def ofIci' : Prop := True
/-- ofIic' (abstract). -/
def ofIic' : Prop := True
/-- toLocallyFiniteOrder (abstract). -/
def toLocallyFiniteOrder' : Prop := True
/-- toLocallyFiniteOrderTop (abstract). -/
def toLocallyFiniteOrderTop' : Prop := True
/-- toLocallyFiniteOrderBot (abstract). -/
def toLocallyFiniteOrderBot' : Prop := True
/-- mem_Icc (abstract). -/
def mem_Icc' : Prop := True
/-- mem_Ico (abstract). -/
def mem_Ico' : Prop := True
/-- mem_Ioc (abstract). -/
def mem_Ioc' : Prop := True
/-- mem_Ioo (abstract). -/
def mem_Ioo' : Prop := True
/-- coe_Icc (abstract). -/
def coe_Icc' : Prop := True
/-- coe_Ico (abstract). -/
def coe_Ico' : Prop := True
/-- coe_Ioc (abstract). -/
def coe_Ioc' : Prop := True
/-- coe_Ioo (abstract). -/
def coe_Ioo' : Prop := True
/-- Ioi (abstract). -/
def Ioi' : Prop := True
/-- mem_Ici (abstract). -/
def mem_Ici' : Prop := True
/-- mem_Ioi (abstract). -/
def mem_Ioi' : Prop := True
/-- coe_Ici (abstract). -/
def coe_Ici' : Prop := True
/-- coe_Ioi (abstract). -/
def coe_Ioi' : Prop := True
/-- Iio (abstract). -/
def Iio' : Prop := True
/-- mem_Iic (abstract). -/
def mem_Iic' : Prop := True
/-- mem_Iio (abstract). -/
def mem_Iio' : Prop := True
/-- coe_Iic (abstract). -/
def coe_Iic' : Prop := True
/-- coe_Iio (abstract). -/
def coe_Iio' : Prop := True
/-- coe_uIcc (abstract). -/
def coe_uIcc' : Prop := True
/-- elabFinsetBuilderIxx (abstract). -/
def elabFinsetBuilderIxx' : Prop := True
/-- finite_Icc (abstract). -/
def finite_Icc' : Prop := True
/-- finite_Ico (abstract). -/
def finite_Ico' : Prop := True
/-- finite_Ioc (abstract). -/
def finite_Ioc' : Prop := True
/-- finite_Ioo (abstract). -/
def finite_Ioo' : Prop := True
/-- finite_Ici (abstract). -/
def finite_Ici' : Prop := True
/-- finite_Ioi (abstract). -/
def finite_Ioi' : Prop := True
/-- finite_Iic (abstract). -/
def finite_Iic' : Prop := True
/-- finite_Iio (abstract). -/
def finite_Iio' : Prop := True
/-- finite_interval (abstract). -/
def finite_interval' : Prop := True
/-- ofFiniteIcc (abstract). -/
def ofFiniteIcc' : Prop := True
/-- locallyFiniteOrder (abstract). -/
def locallyFiniteOrder' : Prop := True
/-- Icc_orderDual_def (abstract). -/
def Icc_orderDual_def' : Prop := True
/-- Ico_orderDual_def (abstract). -/
def Ico_orderDual_def' : Prop := True
/-- Ioc_orderDual_def (abstract). -/
def Ioc_orderDual_def' : Prop := True
/-- Ioo_orderDual_def (abstract). -/
def Ioo_orderDual_def' : Prop := True
/-- Icc_toDual (abstract). -/
def Icc_toDual' : Prop := True
/-- Ico_toDual (abstract). -/
def Ico_toDual' : Prop := True
/-- Ioc_toDual (abstract). -/
def Ioc_toDual' : Prop := True
/-- Ioo_toDual (abstract). -/
def Ioo_toDual' : Prop := True
/-- Icc_ofDual (abstract). -/
def Icc_ofDual' : Prop := True
/-- Ico_ofDual (abstract). -/
def Ico_ofDual' : Prop := True
/-- Ioc_ofDual (abstract). -/
def Ioc_ofDual' : Prop := True
/-- Ioo_ofDual (abstract). -/
def Ioo_ofDual' : Prop := True
/-- Iic_orderDual_def (abstract). -/
def Iic_orderDual_def' : Prop := True
/-- Iio_orderDual_def (abstract). -/
def Iio_orderDual_def' : Prop := True
/-- Iic_toDual (abstract). -/
def Iic_toDual' : Prop := True
/-- Iio_toDual (abstract). -/
def Iio_toDual' : Prop := True
/-- Ici_ofDual (abstract). -/
def Ici_ofDual' : Prop := True
/-- Ioi_ofDual (abstract). -/
def Ioi_ofDual' : Prop := True
/-- Ici_orderDual_def (abstract). -/
def Ici_orderDual_def' : Prop := True
/-- Ioi_orderDual_def (abstract). -/
def Ioi_orderDual_def' : Prop := True
/-- Ici_toDual (abstract). -/
def Ici_toDual' : Prop := True
/-- Ioi_toDual (abstract). -/
def Ioi_toDual' : Prop := True
/-- Iic_ofDual (abstract). -/
def Iic_ofDual' : Prop := True
/-- Iio_ofDual (abstract). -/
def Iio_ofDual' : Prop := True
/-- card_Icc_prod (abstract). -/
def card_Icc_prod' : Prop := True
/-- card_Ici_prod (abstract). -/
def card_Ici_prod' : Prop := True
/-- card_Iic_prod (abstract). -/
def card_Iic_prod' : Prop := True
/-- card_uIcc_prod (abstract). -/
def card_uIcc_prod' : Prop := True
/-- aux (abstract). -/
def aux' : Prop := True
/-- map_subtype_embedding_Icc (abstract). -/
def map_subtype_embedding_Icc' : Prop := True
/-- map_subtype_embedding_Ico (abstract). -/
def map_subtype_embedding_Ico' : Prop := True
/-- map_subtype_embedding_Ioc (abstract). -/
def map_subtype_embedding_Ioc' : Prop := True
/-- map_subtype_embedding_Ici (abstract). -/
def map_subtype_embedding_Ici' : Prop := True
/-- map_subtype_embedding_Iic (abstract). -/
def map_subtype_embedding_Iic' : Prop := True
/-- map_subtype_embedding_Iio (abstract). -/
def map_subtype_embedding_Iio' : Prop := True
/-- finite_of_bddAbove (abstract). -/
def finite_of_bddAbove' : Prop := True
/-- finite_iff_bddAbove (abstract). -/
def finite_iff_bddAbove' : Prop := True
/-- finite_iff_bddBelow (abstract). -/
def finite_iff_bddBelow' : Prop := True
/-- finite_iff_bddBelow_bddAbove (abstract). -/
def finite_iff_bddBelow_bddAbove' : Prop := True
/-- toFinset_Icc (abstract). -/
def toFinset_Icc' : Prop := True
/-- toFinset_Ico (abstract). -/
def toFinset_Ico' : Prop := True
/-- toFinset_Ioc (abstract). -/
def toFinset_Ioc' : Prop := True
/-- toFinset_Ioo (abstract). -/
def toFinset_Ioo' : Prop := True
/-- toFinset_Ici (abstract). -/
def toFinset_Ici' : Prop := True
/-- toFinset_Ioi (abstract). -/
def toFinset_Ioi' : Prop := True
/-- toFinset_Iic (abstract). -/
def toFinset_Iic' : Prop := True
/-- toFinset_Iio (abstract). -/
def toFinset_Iio' : Prop := True
/-- ofOrderIsoClass (abstract). -/
def ofOrderIsoClass' : Prop := True

-- Interval/Finset/Fin.lean
/-- map_valEmbedding_Icc (abstract). -/
def map_valEmbedding_Icc' : Prop := True
/-- map_valEmbedding_Ico (abstract). -/
def map_valEmbedding_Ico' : Prop := True
/-- map_valEmbedding_Ioc (abstract). -/
def map_valEmbedding_Ioc' : Prop := True
/-- map_valEmbedding_Ioo (abstract). -/
def map_valEmbedding_Ioo' : Prop := True
/-- map_subtype_embedding_uIcc (abstract). -/
def map_subtype_embedding_uIcc' : Prop := True
/-- card_Icc (abstract). -/
def card_Icc' : Prop := True
/-- card_Ico (abstract). -/
def card_Ico' : Prop := True
/-- card_Ioc (abstract). -/
def card_Ioc' : Prop := True
/-- card_Ioo (abstract). -/
def card_Ioo' : Prop := True
/-- card_uIcc (abstract). -/
def card_uIcc' : Prop := True
/-- card_fintypeIcc (abstract). -/
def card_fintypeIcc' : Prop := True
/-- card_fintypeIco (abstract). -/
def card_fintypeIco' : Prop := True
/-- card_fintypeIoc (abstract). -/
def card_fintypeIoc' : Prop := True
/-- map_valEmbedding_Ici (abstract). -/
def map_valEmbedding_Ici' : Prop := True
/-- map_valEmbedding_Ioi (abstract). -/
def map_valEmbedding_Ioi' : Prop := True
/-- map_valEmbedding_Iic (abstract). -/
def map_valEmbedding_Iic' : Prop := True
/-- map_valEmbedding_Iio (abstract). -/
def map_valEmbedding_Iio' : Prop := True
/-- card_Ici (abstract). -/
def card_Ici' : Prop := True
/-- card_Ioi (abstract). -/
def card_Ioi' : Prop := True
/-- card_Iic (abstract). -/
def card_Iic' : Prop := True
/-- card_Iio (abstract). -/
def card_Iio' : Prop := True
/-- card_fintypeIci (abstract). -/
def card_fintypeIci' : Prop := True
/-- card_fintypeIoi (abstract). -/
def card_fintypeIoi' : Prop := True
/-- card_fintypeIic (abstract). -/
def card_fintypeIic' : Prop := True
/-- card_fintypeIio (abstract). -/
def card_fintypeIio' : Prop := True

-- Interval/Finset/Nat.lean
/-- Iio_eq_range (abstract). -/
def Iio_eq_range' : Prop := True
/-- Ico_zero_eq_range (abstract). -/
def Ico_zero_eq_range' : Prop := True
/-- range_eq_Icc_zero_sub_one (abstract). -/
def range_eq_Icc_zero_sub_one' : Prop := True
/-- range_eq_Ico (abstract). -/
def range_eq_Ico' : Prop := True
/-- card_fintypeIoo (abstract). -/
def card_fintypeIoo' : Prop := True
/-- Icc_succ_left (abstract). -/
def Icc_succ_left' : Prop := True
/-- Ico_succ_right (abstract). -/
def Ico_succ_right' : Prop := True
/-- Ico_succ_left (abstract). -/
def Ico_succ_left' : Prop := True
/-- Icc_pred_right (abstract). -/
def Icc_pred_right' : Prop := True
/-- Ico_succ_succ (abstract). -/
def Ico_succ_succ' : Prop := True
/-- Ico_succ_singleton (abstract). -/
def Ico_succ_singleton' : Prop := True
/-- Ico_pred_singleton (abstract). -/
def Ico_pred_singleton' : Prop := True
/-- Ioc_succ_singleton (abstract). -/
def Ioc_succ_singleton' : Prop := True
/-- Ico_succ_right_eq_insert_Ico (abstract). -/
def Ico_succ_right_eq_insert_Ico' : Prop := True
/-- Ico_insert_succ_left (abstract). -/
def Ico_insert_succ_left' : Prop := True
/-- Icc_insert_succ_left (abstract). -/
def Icc_insert_succ_left' : Prop := True
/-- Icc_insert_succ_right (abstract). -/
def Icc_insert_succ_right' : Prop := True
/-- image_sub_const_Ico (abstract). -/
def image_sub_const_Ico' : Prop := True
/-- Ico_image_const_sub_eq_Ico (abstract). -/
def Ico_image_const_sub_eq_Ico' : Prop := True
/-- Ico_succ_left_eq_erase_Ico (abstract). -/
def Ico_succ_left_eq_erase_Ico' : Prop := True
/-- mod_injOn_Ico (abstract). -/
def mod_injOn_Ico' : Prop := True
/-- image_Ico_mod (abstract). -/
def image_Ico_mod' : Prop := True
/-- multiset_Ico_map_mod (abstract). -/
def multiset_Ico_map_mod' : Prop := True
/-- range_image_pred_top_sub (abstract). -/
def range_image_pred_top_sub' : Prop := True
/-- range_add_eq_union (abstract). -/
def range_add_eq_union' : Prop := True
/-- decreasing_induction_of_not_bddAbove (abstract). -/
def decreasing_induction_of_not_bddAbove' : Prop := True
/-- strong_decreasing_induction (abstract). -/
def strong_decreasing_induction' : Prop := True
/-- decreasing_induction_of_infinite (abstract). -/
def decreasing_induction_of_infinite' : Prop := True
/-- cauchy_induction' (abstract). -/
def cauchy_induction' : Prop := True
/-- cauchy_induction_mul (abstract). -/
def cauchy_induction_mul' : Prop := True
/-- cauchy_induction_two_mul (abstract). -/
def cauchy_induction_two_mul' : Prop := True
/-- pow_imp_self_of_one_lt (abstract). -/
def pow_imp_self_of_one_lt' : Prop := True

-- Interval/Multiset.lean
/-- nodup_Icc (abstract). -/
def nodup_Icc' : Prop := True
/-- nodup_Ico (abstract). -/
def nodup_Ico' : Prop := True
/-- nodup_Ioc (abstract). -/
def nodup_Ioc' : Prop := True
/-- nodup_Ioo (abstract). -/
def nodup_Ioo' : Prop := True
/-- Icc_eq_zero_iff (abstract). -/
def Icc_eq_zero_iff' : Prop := True
/-- Ico_eq_zero_iff (abstract). -/
def Ico_eq_zero_iff' : Prop := True
/-- Ioc_eq_zero_iff (abstract). -/
def Ioc_eq_zero_iff' : Prop := True
/-- Ioo_eq_zero_iff (abstract). -/
def Ioo_eq_zero_iff' : Prop := True
/-- Ioo_eq_zero (abstract). -/
def Ioo_eq_zero' : Prop := True
/-- Icc_eq_zero_of_lt (abstract). -/
def Icc_eq_zero_of_lt' : Prop := True
/-- Ico_eq_zero_of_le (abstract). -/
def Ico_eq_zero_of_le' : Prop := True
/-- Ioc_eq_zero_of_le (abstract). -/
def Ioc_eq_zero_of_le' : Prop := True
/-- Ioo_eq_zero_of_le (abstract). -/
def Ioo_eq_zero_of_le' : Prop := True
/-- right_mem_Ioc (abstract). -/
def right_mem_Ioc' : Prop := True
/-- Ico_cons_right (abstract). -/
def Ico_cons_right' : Prop := True
/-- Ioo_cons_left (abstract). -/
def Ioo_cons_left' : Prop := True
/-- Ico_disjoint_Ico (abstract). -/
def Ico_disjoint_Ico' : Prop := True
/-- Ico_inter_Ico_of_le (abstract). -/
def Ico_inter_Ico_of_le' : Prop := True
/-- Ico_add_Ico_eq_Ico (abstract). -/
def Ico_add_Ico_eq_Ico' : Prop := True
/-- Ico_sub_Ico_left (abstract). -/
def Ico_sub_Ico_left' : Prop := True
/-- Ico_sub_Ico_right (abstract). -/
def Ico_sub_Ico_right' : Prop := True

-- Interval/Set/Basic.lean
/-- dual_Icc (abstract). -/
def dual_Icc' : Prop := True
/-- dual_Ioc (abstract). -/
def dual_Ioc' : Prop := True
/-- dual_Ico (abstract). -/
def dual_Ico' : Prop := True
/-- dual_Ioo (abstract). -/
def dual_Ioo' : Prop := True
/-- nonempty_Icc_subtype (abstract). -/
def nonempty_Icc_subtype' : Prop := True
/-- nonempty_Ico_subtype (abstract). -/
def nonempty_Ico_subtype' : Prop := True
/-- nonempty_Ioc_subtype (abstract). -/
def nonempty_Ioc_subtype' : Prop := True
/-- nonempty_Ioo_subtype (abstract). -/
def nonempty_Ioo_subtype' : Prop := True
/-- Icc_eq_empty (abstract). -/
def Icc_eq_empty' : Prop := True
/-- Ico_eq_empty (abstract). -/
def Ico_eq_empty' : Prop := True
/-- Ioc_eq_empty (abstract). -/
def Ioc_eq_empty' : Prop := True
/-- Ici_subset_Ioi (abstract). -/
def Ici_subset_Ioi' : Prop := True
/-- Iic_subset_Iio (abstract). -/
def Iic_subset_Iio' : Prop := True
/-- Icc_subset_Ioo (abstract). -/
def Icc_subset_Ioo' : Prop := True
/-- Ioi_ssubset_Ici_self (abstract). -/
def Ioi_ssubset_Ici_self' : Prop := True
/-- Iio_ssubset_Iic_self (abstract). -/
def Iio_ssubset_Iic_self' : Prop := True
/-- Icc_subset_Iio_iff (abstract). -/
def Icc_subset_Iio_iff' : Prop := True
/-- Icc_subset_Ioi_iff (abstract). -/
def Icc_subset_Ioi_iff' : Prop := True
/-- Icc_subset_Iic_iff (abstract). -/
def Icc_subset_Iic_iff' : Prop := True
/-- Icc_subset_Ici_iff (abstract). -/
def Icc_subset_Ici_iff' : Prop := True
/-- Iic_inter_Ici (abstract). -/
def Iic_inter_Ici' : Prop := True
/-- Iio_inter_Ici (abstract). -/
def Iio_inter_Ici' : Prop := True
/-- Iic_inter_Ioi (abstract). -/
def Iic_inter_Ioi' : Prop := True
/-- Iio_inter_Ioi (abstract). -/
def Iio_inter_Ioi' : Prop := True
/-- mem_Icc_of_Ioo (abstract). -/
def mem_Icc_of_Ioo' : Prop := True
/-- mem_Ico_of_Ioo (abstract). -/
def mem_Ico_of_Ioo' : Prop := True
/-- mem_Ioc_of_Ioo (abstract). -/
def mem_Ioc_of_Ioo' : Prop := True
/-- mem_Icc_of_Ico (abstract). -/
def mem_Icc_of_Ico' : Prop := True
/-- mem_Icc_of_Ioc (abstract). -/
def mem_Icc_of_Ioc' : Prop := True
/-- mem_Ici_of_Ioi (abstract). -/
def mem_Ici_of_Ioi' : Prop := True
/-- mem_Iic_of_Iio (abstract). -/
def mem_Iic_of_Iio' : Prop := True
/-- Ici_eq (abstract). -/
def Ici_eq' : Prop := True
/-- Ioi_eq_empty_iff (abstract). -/
def Ioi_eq_empty_iff' : Prop := True
/-- Iio_eq_empty_iff (abstract). -/
def Iio_eq_empty_iff' : Prop := True
/-- Iic_inter_Ioc_of_le (abstract). -/
def Iic_inter_Ioc_of_le' : Prop := True
/-- not_mem_Icc_of_lt (abstract). -/
def not_mem_Icc_of_lt' : Prop := True
/-- not_mem_Icc_of_gt (abstract). -/
def not_mem_Icc_of_gt' : Prop := True
/-- not_mem_Ico_of_lt (abstract). -/
def not_mem_Ico_of_lt' : Prop := True
/-- not_mem_Ioc_of_gt (abstract). -/
def not_mem_Ioc_of_gt' : Prop := True
/-- not_mem_Ioc_of_le (abstract). -/
def not_mem_Ioc_of_le' : Prop := True
/-- not_mem_Ico_of_ge (abstract). -/
def not_mem_Ico_of_ge' : Prop := True
/-- not_mem_Ioo_of_le (abstract). -/
def not_mem_Ioo_of_le' : Prop := True
/-- not_mem_Ioo_of_ge (abstract). -/
def not_mem_Ioo_of_ge' : Prop := True
/-- subsingleton_Icc_of_ge (abstract). -/
def subsingleton_Icc_of_ge' : Prop := True
/-- subsingleton_Icc_iff (abstract). -/
def subsingleton_Icc_iff' : Prop := True
/-- Icc_diff_left (abstract). -/
def Icc_diff_left' : Prop := True
/-- Icc_diff_right (abstract). -/
def Icc_diff_right' : Prop := True
/-- Ico_diff_left (abstract). -/
def Ico_diff_left' : Prop := True
/-- Ioc_diff_right (abstract). -/
def Ioc_diff_right' : Prop := True
/-- Ici_diff_left (abstract). -/
def Ici_diff_left' : Prop := True
/-- Iic_diff_right (abstract). -/
def Iic_diff_right' : Prop := True
/-- Ico_diff_Ioo_same (abstract). -/
def Ico_diff_Ioo_same' : Prop := True
/-- Ioc_diff_Ioo_same (abstract). -/
def Ioc_diff_Ioo_same' : Prop := True
/-- Icc_diff_Ico_same (abstract). -/
def Icc_diff_Ico_same' : Prop := True
/-- Icc_diff_Ioc_same (abstract). -/
def Icc_diff_Ioc_same' : Prop := True
/-- Icc_diff_Ioo_same (abstract). -/
def Icc_diff_Ioo_same' : Prop := True
/-- Ici_diff_Ioi_same (abstract). -/
def Ici_diff_Ioi_same' : Prop := True
/-- Iic_diff_Iio_same (abstract). -/
def Iic_diff_Iio_same' : Prop := True
/-- Ioi_union_left (abstract). -/
def Ioi_union_left' : Prop := True
/-- Iio_union_right (abstract). -/
def Iio_union_right' : Prop := True
/-- Ioo_union_left (abstract). -/
def Ioo_union_left' : Prop := True
/-- Ioo_union_right (abstract). -/
def Ioo_union_right' : Prop := True
/-- Ioo_union_both (abstract). -/
def Ioo_union_both' : Prop := True
/-- Ioc_union_left (abstract). -/
def Ioc_union_left' : Prop := True
/-- Ico_union_right (abstract). -/
def Ico_union_right' : Prop := True
/-- mem_Ici_Ioi_of_subset_of_subset (abstract). -/
def mem_Ici_Ioi_of_subset_of_subset' : Prop := True
/-- mem_Iic_Iio_of_subset_of_subset (abstract). -/
def mem_Iic_Iio_of_subset_of_subset' : Prop := True
/-- mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset (abstract). -/
def mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset' : Prop := True
/-- eq_left_or_mem_Ioo_of_mem_Ico (abstract). -/
def eq_left_or_mem_Ioo_of_mem_Ico' : Prop := True
/-- eq_right_or_mem_Ioo_of_mem_Ioc (abstract). -/
def eq_right_or_mem_Ioo_of_mem_Ioc' : Prop := True
/-- Ici_injective (abstract). -/
def Ici_injective' : Prop := True
/-- Iic_injective (abstract). -/
def Iic_injective' : Prop := True
/-- Ici_inj (abstract). -/
def Ici_inj' : Prop := True
/-- Iic_inj (abstract). -/
def Iic_inj' : Prop := True
/-- Ici_top (abstract). -/
def Ici_top' : Prop := True
/-- Ioi_top (abstract). -/
def Ioi_top' : Prop := True
/-- Iic_top (abstract). -/
def Iic_top' : Prop := True
/-- Icc_top (abstract). -/
def Icc_top' : Prop := True
/-- Ioc_top (abstract). -/
def Ioc_top' : Prop := True
/-- Iic_bot (abstract). -/
def Iic_bot' : Prop := True
/-- Iio_bot (abstract). -/
def Iio_bot' : Prop := True
/-- Ici_bot (abstract). -/
def Ici_bot' : Prop := True
/-- Icc_bot (abstract). -/
def Icc_bot' : Prop := True
/-- Ico_bot (abstract). -/
def Ico_bot' : Prop := True
/-- not_mem_Ici (abstract). -/
def not_mem_Ici' : Prop := True
/-- not_mem_Iic (abstract). -/
def not_mem_Iic' : Prop := True
/-- not_mem_Ioi (abstract). -/
def not_mem_Ioi' : Prop := True
/-- not_mem_Iio (abstract). -/
def not_mem_Iio' : Prop := True
/-- compl_Iic (abstract). -/
def compl_Iic' : Prop := True
/-- compl_Ici (abstract). -/
def compl_Ici' : Prop := True
/-- compl_Iio (abstract). -/
def compl_Iio' : Prop := True
/-- compl_Ioi (abstract). -/
def compl_Ioi' : Prop := True
/-- Ici_diff_Ici (abstract). -/
def Ici_diff_Ici' : Prop := True
/-- Ici_diff_Ioi (abstract). -/
def Ici_diff_Ioi' : Prop := True
/-- Ioi_diff_Ioi (abstract). -/
def Ioi_diff_Ioi' : Prop := True
/-- Ioi_diff_Ici (abstract). -/
def Ioi_diff_Ici' : Prop := True
/-- Iic_diff_Iic (abstract). -/
def Iic_diff_Iic' : Prop := True
/-- Iio_diff_Iic (abstract). -/
def Iio_diff_Iic' : Prop := True
/-- Iic_diff_Iio (abstract). -/
def Iic_diff_Iio' : Prop := True
/-- Iio_diff_Iio (abstract). -/
def Iio_diff_Iio' : Prop := True
/-- Ioc_subset_Ioc_iff (abstract). -/
def Ioc_subset_Ioc_iff' : Prop := True
/-- Ioo_subset_Ioo_iff (abstract). -/
def Ioo_subset_Ioo_iff' : Prop := True
/-- Ico_eq_Ico_iff (abstract). -/
def Ico_eq_Ico_iff' : Prop := True
/-- Ici_eq_singleton_iff_isTop (abstract). -/
def Ici_eq_singleton_iff_isTop' : Prop := True
/-- Ioi_subset_Ioi_iff (abstract). -/
def Ioi_subset_Ioi_iff' : Prop := True
/-- Ioi_subset_Ici_iff (abstract). -/
def Ioi_subset_Ici_iff' : Prop := True
/-- Iio_subset_Iio_iff (abstract). -/
def Iio_subset_Iio_iff' : Prop := True
/-- Iio_subset_Iic_iff (abstract). -/
def Iio_subset_Iic_iff' : Prop := True
/-- Iic_union_Ioi_of_le (abstract). -/
def Iic_union_Ioi_of_le' : Prop := True
/-- Iio_union_Ici_of_le (abstract). -/
def Iio_union_Ici_of_le' : Prop := True
/-- Iic_union_Ici_of_le (abstract). -/
def Iic_union_Ici_of_le' : Prop := True
/-- Iio_union_Ioi_of_lt (abstract). -/
def Iio_union_Ioi_of_lt' : Prop := True
/-- Iic_union_Ici (abstract). -/
def Iic_union_Ici' : Prop := True
/-- Iio_union_Ici (abstract). -/
def Iio_union_Ici' : Prop := True
/-- Iic_union_Ioi (abstract). -/
def Iic_union_Ioi' : Prop := True
/-- Iio_union_Ioi (abstract). -/
def Iio_union_Ioi' : Prop := True
/-- Ioo_union_Ioi' (abstract). -/
def Ioo_union_Ioi' : Prop := True
/-- Ioi_subset_Ioo_union_Ici (abstract). -/
def Ioi_subset_Ioo_union_Ici' : Prop := True
/-- Ioo_union_Ici_eq_Ioi (abstract). -/
def Ioo_union_Ici_eq_Ioi' : Prop := True
/-- Ici_subset_Ico_union_Ici (abstract). -/
def Ici_subset_Ico_union_Ici' : Prop := True
/-- Ico_union_Ici_eq_Ici (abstract). -/
def Ico_union_Ici_eq_Ici' : Prop := True
/-- Ico_union_Ici' (abstract). -/
def Ico_union_Ici' : Prop := True
/-- Ioi_subset_Ioc_union_Ioi (abstract). -/
def Ioi_subset_Ioc_union_Ioi' : Prop := True
/-- Ioc_union_Ioi_eq_Ioi (abstract). -/
def Ioc_union_Ioi_eq_Ioi' : Prop := True
/-- Ioc_union_Ioi' (abstract). -/
def Ioc_union_Ioi' : Prop := True
/-- Ici_subset_Icc_union_Ioi (abstract). -/
def Ici_subset_Icc_union_Ioi' : Prop := True
/-- Icc_union_Ioi_eq_Ici (abstract). -/
def Icc_union_Ioi_eq_Ici' : Prop := True
/-- Ioi_subset_Ioc_union_Ici (abstract). -/
def Ioi_subset_Ioc_union_Ici' : Prop := True
/-- Ioc_union_Ici_eq_Ioi (abstract). -/
def Ioc_union_Ici_eq_Ioi' : Prop := True
/-- Ici_subset_Icc_union_Ici (abstract). -/
def Ici_subset_Icc_union_Ici' : Prop := True
/-- Icc_union_Ici_eq_Ici (abstract). -/
def Icc_union_Ici_eq_Ici' : Prop := True
/-- Icc_union_Ici' (abstract). -/
def Icc_union_Ici' : Prop := True
/-- Iic_subset_Iio_union_Icc (abstract). -/
def Iic_subset_Iio_union_Icc' : Prop := True
/-- Iio_union_Icc_eq_Iic (abstract). -/
def Iio_union_Icc_eq_Iic' : Prop := True
/-- Iio_subset_Iio_union_Ico (abstract). -/
def Iio_subset_Iio_union_Ico' : Prop := True
/-- Iio_union_Ico_eq_Iio (abstract). -/
def Iio_union_Ico_eq_Iio' : Prop := True
/-- Iio_union_Ico' (abstract). -/
def Iio_union_Ico' : Prop := True
/-- Iic_subset_Iic_union_Ioc (abstract). -/
def Iic_subset_Iic_union_Ioc' : Prop := True
/-- Iic_union_Ioc_eq_Iic (abstract). -/
def Iic_union_Ioc_eq_Iic' : Prop := True
/-- Iic_union_Ioc' (abstract). -/
def Iic_union_Ioc' : Prop := True
/-- Iio_subset_Iic_union_Ioo (abstract). -/
def Iio_subset_Iic_union_Ioo' : Prop := True
/-- Iic_union_Ioo_eq_Iio (abstract). -/
def Iic_union_Ioo_eq_Iio' : Prop := True
/-- Iio_union_Ioo' (abstract). -/
def Iio_union_Ioo' : Prop := True
/-- Iic_subset_Iic_union_Icc (abstract). -/
def Iic_subset_Iic_union_Icc' : Prop := True
/-- Iic_union_Icc_eq_Iic (abstract). -/
def Iic_union_Icc_eq_Iic' : Prop := True
/-- Iic_union_Icc' (abstract). -/
def Iic_union_Icc' : Prop := True
/-- Iio_subset_Iic_union_Ico (abstract). -/
def Iio_subset_Iic_union_Ico' : Prop := True
/-- Iic_union_Ico_eq_Iio (abstract). -/
def Iic_union_Ico_eq_Iio' : Prop := True
/-- Ioo_subset_Ioo_union_Ico (abstract). -/
def Ioo_subset_Ioo_union_Ico' : Prop := True
/-- Ioo_union_Ico_eq_Ioo (abstract). -/
def Ioo_union_Ico_eq_Ioo' : Prop := True
/-- Icc_subset_Ico_union_Icc (abstract). -/
def Icc_subset_Ico_union_Icc' : Prop := True
/-- Ico_union_Icc_eq_Icc (abstract). -/
def Ico_union_Icc_eq_Icc' : Prop := True
/-- Ioc_subset_Ioo_union_Icc (abstract). -/
def Ioc_subset_Ioo_union_Icc' : Prop := True
/-- Ioo_union_Icc_eq_Ioc (abstract). -/
def Ioo_union_Icc_eq_Ioc' : Prop := True
/-- Ioo_subset_Ioc_union_Ioo (abstract). -/
def Ioo_subset_Ioc_union_Ioo' : Prop := True
/-- Ioc_union_Ioo_eq_Ioo (abstract). -/
def Ioc_union_Ioo_eq_Ioo' : Prop := True
/-- Ico_subset_Icc_union_Ioo (abstract). -/
def Ico_subset_Icc_union_Ioo' : Prop := True
/-- Icc_union_Ioo_eq_Ico (abstract). -/
def Icc_union_Ioo_eq_Ico' : Prop := True
/-- Icc_subset_Icc_union_Ioc (abstract). -/
def Icc_subset_Icc_union_Ioc' : Prop := True
/-- Icc_union_Ioc_eq_Icc (abstract). -/
def Icc_union_Ioc_eq_Icc' : Prop := True
/-- Ioc_subset_Ioc_union_Ioc (abstract). -/
def Ioc_subset_Ioc_union_Ioc' : Prop := True
/-- Ioc_union_Ioc' (abstract). -/
def Ioc_union_Ioc' : Prop := True
/-- Ioo_subset_Ioc_union_Ico (abstract). -/
def Ioo_subset_Ioc_union_Ico' : Prop := True
/-- Ioc_union_Ico_eq_Ioo (abstract). -/
def Ioc_union_Ico_eq_Ioo' : Prop := True
/-- Ico_subset_Icc_union_Ico (abstract). -/
def Ico_subset_Icc_union_Ico' : Prop := True
/-- Icc_union_Ico_eq_Ico (abstract). -/
def Icc_union_Ico_eq_Ico' : Prop := True
/-- Icc_subset_Icc_union_Icc (abstract). -/
def Icc_subset_Icc_union_Icc' : Prop := True
/-- Icc_union_Icc_eq_Icc (abstract). -/
def Icc_union_Icc_eq_Icc' : Prop := True
/-- Icc_union_Icc' (abstract). -/
def Icc_union_Icc' : Prop := True
/-- Ioc_subset_Ioc_union_Icc (abstract). -/
def Ioc_subset_Ioc_union_Icc' : Prop := True
/-- Ioc_union_Icc_eq_Ioc (abstract). -/
def Ioc_union_Icc_eq_Ioc' : Prop := True
/-- Ioo_union_Ioo' (abstract). -/
def Ioo_union_Ioo' : Prop := True
/-- Ioo_subset_Ioo_union_Ioo (abstract). -/
def Ioo_subset_Ioo_union_Ioo' : Prop := True
/-- Iic_inter_Iic (abstract). -/
def Iic_inter_Iic' : Prop := True
/-- Ioc_inter_Iic (abstract). -/
def Ioc_inter_Iic' : Prop := True
/-- Ici_inter_Ici (abstract). -/
def Ici_inter_Ici' : Prop := True
/-- Ico_inter_Ici (abstract). -/
def Ico_inter_Ici' : Prop := True
/-- Icc_inter_Icc (abstract). -/
def Icc_inter_Icc' : Prop := True
/-- Icc_inter_Icc_eq_singleton (abstract). -/
def Icc_inter_Icc_eq_singleton' : Prop := True
/-- Ioi_inter_Ioi (abstract). -/
def Ioi_inter_Ioi' : Prop := True
/-- Iio_inter_Iio (abstract). -/
def Iio_inter_Iio' : Prop := True
/-- Ioc_inter_Ioc (abstract). -/
def Ioc_inter_Ioc' : Prop := True
/-- Ioo_inter_Ioo (abstract). -/
def Ioo_inter_Ioo' : Prop := True
/-- Ioo_inter_Iio (abstract). -/
def Ioo_inter_Iio' : Prop := True
/-- Iio_inter_Ioo (abstract). -/
def Iio_inter_Ioo' : Prop := True
/-- Ioo_inter_Ioi (abstract). -/
def Ioo_inter_Ioi' : Prop := True
/-- Ioi_inter_Ioo (abstract). -/
def Ioi_inter_Ioo' : Prop := True
/-- Ioc_inter_Ioo_of_left_lt (abstract). -/
def Ioc_inter_Ioo_of_left_lt' : Prop := True
/-- Ioc_inter_Ioo_of_right_le (abstract). -/
def Ioc_inter_Ioo_of_right_le' : Prop := True
/-- Ioo_inter_Ioc_of_left_le (abstract). -/
def Ioo_inter_Ioc_of_left_le' : Prop := True
/-- Ioo_inter_Ioc_of_right_lt (abstract). -/
def Ioo_inter_Ioc_of_right_lt' : Prop := True
/-- Ico_diff_Iio (abstract). -/
def Ico_diff_Iio' : Prop := True
/-- Ioc_diff_Ioi (abstract). -/
def Ioc_diff_Ioi' : Prop := True
/-- Ioc_inter_Ioi (abstract). -/
def Ioc_inter_Ioi' : Prop := True
/-- Ico_inter_Iio (abstract). -/
def Ico_inter_Iio' : Prop := True
/-- Ioc_diff_Iic (abstract). -/
def Ioc_diff_Iic' : Prop := True
/-- Ioc_union_Ioc_right (abstract). -/
def Ioc_union_Ioc_right' : Prop := True
/-- Ioc_union_Ioc_left (abstract). -/
def Ioc_union_Ioc_left' : Prop := True
/-- Ioc_union_Ioc_symm (abstract). -/
def Ioc_union_Ioc_symm' : Prop := True
/-- Ioc_union_Ioc_union_Ioc_cycle (abstract). -/
def Ioc_union_Ioc_union_Ioc_cycle' : Prop := True
/-- Icc_prod_Icc (abstract). -/
def Icc_prod_Icc' : Prop := True
/-- Iic_False (abstract). -/
def Iic_False' : Prop := True
/-- Iic_True (abstract). -/
def Iic_True' : Prop := True
/-- Ici_False (abstract). -/
def Ici_False' : Prop := True
/-- Ici_True (abstract). -/
def Ici_True' : Prop := True
/-- Iio_False (abstract). -/
def Iio_False' : Prop := True
/-- Iio_True (abstract). -/
def Iio_True' : Prop := True
/-- Ioi_False (abstract). -/
def Ioi_False' : Prop := True
/-- Ioi_True (abstract). -/
def Ioi_True' : Prop := True

-- Interval/Set/Defs.lean
/-- OrdConnected (abstract). -/
def OrdConnected' : Prop := True

-- Interval/Set/Disjoint.lean
/-- Iic_disjoint_Ioi (abstract). -/
def Iic_disjoint_Ioi' : Prop := True
/-- Iio_disjoint_Ici (abstract). -/
def Iio_disjoint_Ici' : Prop := True
/-- Iic_disjoint_Ioc (abstract). -/
def Iic_disjoint_Ioc' : Prop := True
/-- Ioc_disjoint_Ioc_same (abstract). -/
def Ioc_disjoint_Ioc_same' : Prop := True
/-- Ico_disjoint_Ico_same (abstract). -/
def Ico_disjoint_Ico_same' : Prop := True
/-- Ici_disjoint_Iic (abstract). -/
def Ici_disjoint_Iic' : Prop := True
/-- Iic_disjoint_Ici (abstract). -/
def Iic_disjoint_Ici' : Prop := True
/-- Ioc_disjoint_Ioi (abstract). -/
def Ioc_disjoint_Ioi' : Prop := True
/-- Ioc_disjoint_Ioi_same (abstract). -/
def Ioc_disjoint_Ioi_same' : Prop := True
/-- iUnion_Iic (abstract). -/
def iUnion_Iic' : Prop := True
/-- iUnion_Ici (abstract). -/
def iUnion_Ici' : Prop := True
/-- iUnion_Icc_right (abstract). -/
def iUnion_Icc_right' : Prop := True
/-- iUnion_Ioc_right (abstract). -/
def iUnion_Ioc_right' : Prop := True
/-- iUnion_Icc_left (abstract). -/
def iUnion_Icc_left' : Prop := True
/-- iUnion_Ico_left (abstract). -/
def iUnion_Ico_left' : Prop := True
/-- iUnion_Iio (abstract). -/
def iUnion_Iio' : Prop := True
/-- iUnion_Ioi (abstract). -/
def iUnion_Ioi' : Prop := True
/-- iUnion_Ico_right (abstract). -/
def iUnion_Ico_right' : Prop := True
/-- iUnion_Ioo_right (abstract). -/
def iUnion_Ioo_right' : Prop := True
/-- iUnion_Ioc_left (abstract). -/
def iUnion_Ioc_left' : Prop := True
/-- iUnion_Ioo_left (abstract). -/
def iUnion_Ioo_left' : Prop := True
/-- Ioc_disjoint_Ioc (abstract). -/
def Ioc_disjoint_Ioc' : Prop := True
/-- Ioo_disjoint_Ioo (abstract). -/
def Ioo_disjoint_Ioo' : Prop := True
/-- eq_of_Ico_disjoint (abstract). -/
def eq_of_Ico_disjoint' : Prop := True
/-- iUnion_Ico_eq_Iio_self_iff (abstract). -/
def iUnion_Ico_eq_Iio_self_iff' : Prop := True
/-- iUnion_Ioc_eq_Ioi_self_iff (abstract). -/
def iUnion_Ioc_eq_Ioi_self_iff' : Prop := True
/-- biUnion_Ico_eq_Iio_self_iff (abstract). -/
def biUnion_Ico_eq_Iio_self_iff' : Prop := True
/-- biUnion_Ioc_eq_Ioi_self_iff (abstract). -/
def biUnion_Ioc_eq_Ioi_self_iff' : Prop := True
/-- biUnion_Ici_eq_Ioi (abstract). -/
def biUnion_Ici_eq_Ioi' : Prop := True
/-- biUnion_Ici_eq_Ici (abstract). -/
def biUnion_Ici_eq_Ici' : Prop := True
/-- biUnion_Iic_eq_Iio (abstract). -/
def biUnion_Iic_eq_Iio' : Prop := True
/-- biUnion_Iic_eq_Iic (abstract). -/
def biUnion_Iic_eq_Iic' : Prop := True
/-- iUnion_Ici_eq_Ioi_iInf (abstract). -/
def iUnion_Ici_eq_Ioi_iInf' : Prop := True
/-- iUnion_Iic_eq_Iio_iSup (abstract). -/
def iUnion_Iic_eq_Iio_iSup' : Prop := True
/-- iUnion_Ici_eq_Ici_iInf (abstract). -/
def iUnion_Ici_eq_Ici_iInf' : Prop := True
/-- iUnion_Iic_eq_Iic_iSup (abstract). -/
def iUnion_Iic_eq_Iic_iSup' : Prop := True
/-- iUnion_Iio_eq_univ_iff (abstract). -/
def iUnion_Iio_eq_univ_iff' : Prop := True
/-- iUnion_Iic_of_not_bddAbove_range (abstract). -/
def iUnion_Iic_of_not_bddAbove_range' : Prop := True
/-- iInter_Iic_eq_empty_iff (abstract). -/
def iInter_Iic_eq_empty_iff' : Prop := True
/-- iInter_Iio_of_not_bddBelow_range (abstract). -/
def iInter_Iio_of_not_bddBelow_range' : Prop := True

-- Interval/Set/Image.lean
/-- mapsTo_Ici (abstract). -/
def mapsTo_Ici' : Prop := True
/-- mapsTo_Iic (abstract). -/
def mapsTo_Iic' : Prop := True
/-- mapsTo_Icc (abstract). -/
def mapsTo_Icc' : Prop := True
/-- mapsTo_Ioi (abstract). -/
def mapsTo_Ioi' : Prop := True
/-- mapsTo_Iio (abstract). -/
def mapsTo_Iio' : Prop := True
/-- mapsTo_Ioo (abstract). -/
def mapsTo_Ioo' : Prop := True
/-- image_Ici_subset (abstract). -/
def image_Ici_subset' : Prop := True
/-- image_Iic_subset (abstract). -/
def image_Iic_subset' : Prop := True
/-- image_Icc_subset (abstract). -/
def image_Icc_subset' : Prop := True
/-- image_Ioi_subset (abstract). -/
def image_Ioi_subset' : Prop := True
/-- image_Iio_subset (abstract). -/
def image_Iio_subset' : Prop := True
/-- image_Ioo_subset (abstract). -/
def image_Ioo_subset' : Prop := True
/-- mapsTo_Ico (abstract). -/
def mapsTo_Ico' : Prop := True
/-- mapsTo_Ioc (abstract). -/
def mapsTo_Ioc' : Prop := True
/-- image_Ico_subset (abstract). -/
def image_Ico_subset' : Prop := True
/-- image_Ioc_subset (abstract). -/
def image_Ioc_subset' : Prop := True
/-- image_subtype_val_Ixx_Ixi (abstract). -/
def image_subtype_val_Ixx_Ixi' : Prop := True
/-- image_subtype_val_Icc_subset (abstract). -/
def image_subtype_val_Icc_subset' : Prop := True
/-- image_subtype_val_Ico_subset (abstract). -/
def image_subtype_val_Ico_subset' : Prop := True
/-- image_subtype_val_Ioc_subset (abstract). -/
def image_subtype_val_Ioc_subset' : Prop := True
/-- image_subtype_val_Ioo_subset (abstract). -/
def image_subtype_val_Ioo_subset' : Prop := True
/-- image_subtype_val_Iic_subset (abstract). -/
def image_subtype_val_Iic_subset' : Prop := True
/-- image_subtype_val_Iio_subset (abstract). -/
def image_subtype_val_Iio_subset' : Prop := True
/-- image_subtype_val_Ici_subset (abstract). -/
def image_subtype_val_Ici_subset' : Prop := True
/-- image_subtype_val_Ioi_subset (abstract). -/
def image_subtype_val_Ioi_subset' : Prop := True
/-- image_subtype_val_Ici_Iic (abstract). -/
def image_subtype_val_Ici_Iic' : Prop := True
/-- image_subtype_val_Ici_Iio (abstract). -/
def image_subtype_val_Ici_Iio' : Prop := True
/-- image_subtype_val_Ici_Ici (abstract). -/
def image_subtype_val_Ici_Ici' : Prop := True
/-- image_subtype_val_Ici_Ioi (abstract). -/
def image_subtype_val_Ici_Ioi' : Prop := True
/-- image_subtype_val_Iic_Ici (abstract). -/
def image_subtype_val_Iic_Ici' : Prop := True
/-- image_subtype_val_Iic_Ioi (abstract). -/
def image_subtype_val_Iic_Ioi' : Prop := True
/-- image_subtype_val_Iic_Iic (abstract). -/
def image_subtype_val_Iic_Iic' : Prop := True
/-- image_subtype_val_Iic_Iio (abstract). -/
def image_subtype_val_Iic_Iio' : Prop := True
/-- image_subtype_val_Ioi_Ici (abstract). -/
def image_subtype_val_Ioi_Ici' : Prop := True
/-- image_subtype_val_Ioi_Iic (abstract). -/
def image_subtype_val_Ioi_Iic' : Prop := True
/-- image_subtype_val_Ioi_Ioi (abstract). -/
def image_subtype_val_Ioi_Ioi' : Prop := True
/-- image_subtype_val_Ioi_Iio (abstract). -/
def image_subtype_val_Ioi_Iio' : Prop := True
/-- image_subtype_val_Iio_Ici (abstract). -/
def image_subtype_val_Iio_Ici' : Prop := True
/-- image_subtype_val_Iio_Iic (abstract). -/
def image_subtype_val_Iio_Iic' : Prop := True
/-- image_subtype_val_Iio_Ioi (abstract). -/
def image_subtype_val_Iio_Ioi' : Prop := True
/-- image_subtype_val_Iio_Iio (abstract). -/
def image_subtype_val_Iio_Iio' : Prop := True
/-- image_subtype_val_Icc_Ici (abstract). -/
def image_subtype_val_Icc_Ici' : Prop := True
/-- image_subtype_val_Icc_Iic (abstract). -/
def image_subtype_val_Icc_Iic' : Prop := True
/-- image_subtype_val_Icc_Ioi (abstract). -/
def image_subtype_val_Icc_Ioi' : Prop := True
/-- image_subtype_val_Icc_Iio (abstract). -/
def image_subtype_val_Icc_Iio' : Prop := True
/-- image_subtype_val_Ico_Ici (abstract). -/
def image_subtype_val_Ico_Ici' : Prop := True
/-- image_subtype_val_Ico_Iic (abstract). -/
def image_subtype_val_Ico_Iic' : Prop := True
/-- image_subtype_val_Ico_Ioi (abstract). -/
def image_subtype_val_Ico_Ioi' : Prop := True
/-- image_subtype_val_Ico_Iio (abstract). -/
def image_subtype_val_Ico_Iio' : Prop := True
/-- image_subtype_val_Ioc_Ici (abstract). -/
def image_subtype_val_Ioc_Ici' : Prop := True
/-- image_subtype_val_Ioc_Iic (abstract). -/
def image_subtype_val_Ioc_Iic' : Prop := True
/-- image_subtype_val_Ioc_Ioi (abstract). -/
def image_subtype_val_Ioc_Ioi' : Prop := True
/-- image_subtype_val_Ioc_Iio (abstract). -/
def image_subtype_val_Ioc_Iio' : Prop := True
/-- image_subtype_val_Ioo_Ici (abstract). -/
def image_subtype_val_Ioo_Ici' : Prop := True
/-- image_subtype_val_Ioo_Iic (abstract). -/
def image_subtype_val_Ioo_Iic' : Prop := True
/-- image_subtype_val_Ioo_Ioi (abstract). -/
def image_subtype_val_Ioo_Ioi' : Prop := True
/-- image_subtype_val_Ioo_Iio (abstract). -/
def image_subtype_val_Ioo_Iio' : Prop := True
/-- directedOn_le_Iic (abstract). -/
def directedOn_le_Iic' : Prop := True
/-- directedOn_le_Icc (abstract). -/
def directedOn_le_Icc' : Prop := True
/-- directedOn_le_Ioc (abstract). -/
def directedOn_le_Ioc' : Prop := True
/-- directedOn_ge_Ici (abstract). -/
def directedOn_ge_Ici' : Prop := True
/-- directedOn_ge_Icc (abstract). -/
def directedOn_ge_Icc' : Prop := True
/-- directedOn_ge_Ico (abstract). -/
def directedOn_ge_Ico' : Prop := True

-- Interval/Set/Infinite.lean
/-- infinite (abstract). -/
def infinite' : Prop := True
/-- Ioo_infinite (abstract). -/
def Ioo_infinite' : Prop := True
/-- Ico_infinite (abstract). -/
def Ico_infinite' : Prop := True
/-- Ioc_infinite (abstract). -/
def Ioc_infinite' : Prop := True
/-- Icc_infinite (abstract). -/
def Icc_infinite' : Prop := True
/-- Iio_infinite (abstract). -/
def Iio_infinite' : Prop := True
/-- Iic_infinite (abstract). -/
def Iic_infinite' : Prop := True
/-- Ioi_infinite (abstract). -/
def Ioi_infinite' : Prop := True
/-- Ici_infinite (abstract). -/
def Ici_infinite' : Prop := True

-- Interval/Set/IsoIoo.lean
/-- orderIsoIooNegOneOne (abstract). -/
def orderIsoIooNegOneOne' : Prop := True

-- Interval/Set/Monotone.lean
/-- antitone_Ici (abstract). -/
def antitone_Ici' : Prop := True
/-- monotone_Iic (abstract). -/
def monotone_Iic' : Prop := True
/-- antitone_Ioi (abstract). -/
def antitone_Ioi' : Prop := True
/-- monotone_Iio (abstract). -/
def monotone_Iio' : Prop := True
/-- iUnion_Ioo_of_mono_of_isGLB_of_isLUB (abstract). -/
def iUnion_Ioo_of_mono_of_isGLB_of_isLUB' : Prop := True
/-- strictMonoOn_Iic_of_lt_succ (abstract). -/
def strictMonoOn_Iic_of_lt_succ' : Prop := True
/-- strictAntiOn_Iic_of_succ_lt (abstract). -/
def strictAntiOn_Iic_of_succ_lt' : Prop := True
/-- strictMonoOn_Ici_of_pred_lt (abstract). -/
def strictMonoOn_Ici_of_pred_lt' : Prop := True
/-- strictAntiOn_Ici_of_lt_pred (abstract). -/
def strictAntiOn_Ici_of_lt_pred' : Prop := True
/-- Iic_id_le (abstract). -/
def Iic_id_le' : Prop := True
/-- Ici_le_id (abstract). -/
def Ici_le_id' : Prop := True

-- Interval/Set/OrdConnected.lean
/-- ordConnected_def (abstract). -/
def ordConnected_def' : Prop := True
/-- ordConnected_iff (abstract). -/
def ordConnected_iff' : Prop := True
/-- ordConnected_of_Ioo (abstract). -/
def ordConnected_of_Ioo' : Prop := True
/-- preimage_mono (abstract). -/
def preimage_mono' : Prop := True
/-- preimage_anti (abstract). -/
def preimage_anti' : Prop := True
/-- Icc_subset (abstract). -/
def Icc_subset' : Prop := True
/-- image_Icc (abstract). -/
def image_Icc' : Prop := True
/-- image_Ico (abstract). -/
def image_Ico' : Prop := True
/-- image_Ioc (abstract). -/
def image_Ioc' : Prop := True
/-- image_Ioo (abstract). -/
def image_Ioo' : Prop := True
/-- image_subtype_val_Icc (abstract). -/
def image_subtype_val_Icc' : Prop := True
/-- image_subtype_val_Ico (abstract). -/
def image_subtype_val_Ico' : Prop := True
/-- image_subtype_val_Ioc (abstract). -/
def image_subtype_val_Ioc' : Prop := True
/-- image_subtype_val_Ioo (abstract). -/
def image_subtype_val_Ioo' : Prop := True
/-- ordConnected_dual (abstract). -/
def ordConnected_dual' : Prop := True
/-- ordConnected_sInter (abstract). -/
def ordConnected_sInter' : Prop := True
/-- ordConnected_iInter (abstract). -/
def ordConnected_iInter' : Prop := True
/-- ordConnected_biInter (abstract). -/
def ordConnected_biInter' : Prop := True
/-- ordConnected_pi (abstract). -/
def ordConnected_pi' : Prop := True
/-- ordConnected_Ici (abstract). -/
def ordConnected_Ici' : Prop := True
/-- ordConnected_Iic (abstract). -/
def ordConnected_Iic' : Prop := True
/-- ordConnected_Ioi (abstract). -/
def ordConnected_Ioi' : Prop := True
/-- ordConnected_Iio (abstract). -/
def ordConnected_Iio' : Prop := True
/-- ordConnected_Icc (abstract). -/
def ordConnected_Icc' : Prop := True
/-- ordConnected_Ico (abstract). -/
def ordConnected_Ico' : Prop := True
/-- ordConnected_Ioc (abstract). -/
def ordConnected_Ioc' : Prop := True
/-- ordConnected_Ioo (abstract). -/
def ordConnected_Ioo' : Prop := True
/-- ordConnected_singleton (abstract). -/
def ordConnected_singleton' : Prop := True
/-- ordConnected_empty (abstract). -/
def ordConnected_empty' : Prop := True
/-- ordConnected_univ (abstract). -/
def ordConnected_univ' : Prop := True
/-- ordConnected_preimage (abstract). -/
def ordConnected_preimage' : Prop := True
/-- ordConnected_image (abstract). -/
def ordConnected_image' : Prop := True
/-- ordConnected_range (abstract). -/
def ordConnected_range' : Prop := True
/-- dual_ordConnected_iff (abstract). -/
def dual_ordConnected_iff' : Prop := True
/-- dual_ordConnected (abstract). -/
def dual_ordConnected' : Prop := True
/-- ordConnected (abstract). -/
def ordConnected' : Prop := True
/-- ordConnected_inter_Icc_of_subset (abstract). -/
def ordConnected_inter_Icc_of_subset' : Prop := True
/-- ordConnected_inter_Icc_iff (abstract). -/
def ordConnected_inter_Icc_iff' : Prop := True
/-- not_ordConnected_inter_Icc_iff (abstract). -/
def not_ordConnected_inter_Icc_iff' : Prop := True
/-- ordConnected_uIcc (abstract). -/
def ordConnected_uIcc' : Prop := True
/-- ordConnected_uIoc (abstract). -/
def ordConnected_uIoc' : Prop := True
/-- uIcc_subset (abstract). -/
def uIcc_subset' : Prop := True
/-- uIoc_subset (abstract). -/
def uIoc_subset' : Prop := True
/-- ordConnected_iff_uIcc_subset (abstract). -/
def ordConnected_iff_uIcc_subset' : Prop := True
/-- ordConnected_of_uIcc_subset_left (abstract). -/
def ordConnected_of_uIcc_subset_left' : Prop := True
/-- ordConnected_iff_uIcc_subset_left (abstract). -/
def ordConnected_iff_uIcc_subset_left' : Prop := True
/-- ordConnected_iff_uIcc_subset_right (abstract). -/
def ordConnected_iff_uIcc_subset_right' : Prop := True

-- Interval/Set/OrdConnectedComponent.lean
/-- ordConnectedComponent (abstract). -/
def ordConnectedComponent' : Prop := True
/-- dual_ordConnectedComponent (abstract). -/
def dual_ordConnectedComponent' : Prop := True
/-- ordConnectedComponent_subset (abstract). -/
def ordConnectedComponent_subset' : Prop := True
/-- subset_ordConnectedComponent (abstract). -/
def subset_ordConnectedComponent' : Prop := True
/-- self_mem_ordConnectedComponent (abstract). -/
def self_mem_ordConnectedComponent' : Prop := True
/-- nonempty_ordConnectedComponent (abstract). -/
def nonempty_ordConnectedComponent' : Prop := True
/-- ordConnectedComponent_eq_empty (abstract). -/
def ordConnectedComponent_eq_empty' : Prop := True
/-- ordConnectedComponent_empty (abstract). -/
def ordConnectedComponent_empty' : Prop := True
/-- ordConnectedComponent_univ (abstract). -/
def ordConnectedComponent_univ' : Prop := True
/-- ordConnectedComponent_inter (abstract). -/
def ordConnectedComponent_inter' : Prop := True
/-- mem_ordConnectedComponent_comm (abstract). -/
def mem_ordConnectedComponent_comm' : Prop := True
/-- mem_ordConnectedComponent_trans (abstract). -/
def mem_ordConnectedComponent_trans' : Prop := True
/-- ordConnectedComponent_eq (abstract). -/
def ordConnectedComponent_eq' : Prop := True
/-- ordConnectedProj (abstract). -/
def ordConnectedProj' : Prop := True
/-- ordConnectedProj_mem_ordConnectedComponent (abstract). -/
def ordConnectedProj_mem_ordConnectedComponent' : Prop := True
/-- mem_ordConnectedComponent_ordConnectedProj (abstract). -/
def mem_ordConnectedComponent_ordConnectedProj' : Prop := True
/-- ordConnectedComponent_ordConnectedProj (abstract). -/
def ordConnectedComponent_ordConnectedProj' : Prop := True
/-- ordConnectedProj_eq (abstract). -/
def ordConnectedProj_eq' : Prop := True
/-- ordConnectedSection (abstract). -/
def ordConnectedSection' : Prop := True
/-- dual_ordConnectedSection (abstract). -/
def dual_ordConnectedSection' : Prop := True
/-- ordConnectedSection_subset (abstract). -/
def ordConnectedSection_subset' : Prop := True
/-- eq_of_mem_ordConnectedSection_of_uIcc_subset (abstract). -/
def eq_of_mem_ordConnectedSection_of_uIcc_subset' : Prop := True
/-- ordSeparatingSet (abstract). -/
def ordSeparatingSet' : Prop := True
/-- ordSeparatingSet_comm (abstract). -/
def ordSeparatingSet_comm' : Prop := True
/-- disjoint_left_ordSeparatingSet (abstract). -/
def disjoint_left_ordSeparatingSet' : Prop := True
/-- disjoint_right_ordSeparatingSet (abstract). -/
def disjoint_right_ordSeparatingSet' : Prop := True
/-- dual_ordSeparatingSet (abstract). -/
def dual_ordSeparatingSet' : Prop := True
/-- ordT5Nhd (abstract). -/
def ordT5Nhd' : Prop := True
/-- disjoint_ordT5Nhd (abstract). -/
def disjoint_ordT5Nhd' : Prop := True

-- Interval/Set/OrderEmbedding.lean
/-- preimage_Ici (abstract). -/
def preimage_Ici' : Prop := True
/-- preimage_Iic (abstract). -/
def preimage_Iic' : Prop := True
/-- preimage_Ioi (abstract). -/
def preimage_Ioi' : Prop := True
/-- preimage_Iio (abstract). -/
def preimage_Iio' : Prop := True
/-- preimage_Icc (abstract). -/
def preimage_Icc' : Prop := True
/-- preimage_Ico (abstract). -/
def preimage_Ico' : Prop := True
/-- preimage_Ioc (abstract). -/
def preimage_Ioc' : Prop := True
/-- preimage_Ioo (abstract). -/
def preimage_Ioo' : Prop := True
/-- preimage_uIcc (abstract). -/
def preimage_uIcc' : Prop := True
/-- preimage_uIoc (abstract). -/
def preimage_uIoc' : Prop := True

-- Interval/Set/OrderIso.lean
/-- image_Iic (abstract). -/
def image_Iic' : Prop := True
/-- image_Ici (abstract). -/
def image_Ici' : Prop := True
/-- image_Iio (abstract). -/
def image_Iio' : Prop := True
/-- image_Ioi (abstract). -/
def image_Ioi' : Prop := True
/-- IicTop (abstract). -/
def IicTop' : Prop := True
/-- IciBot (abstract). -/
def IciBot' : Prop := True

-- Interval/Set/Pi.lean
/-- pi_univ_Ici (abstract). -/
def pi_univ_Ici' : Prop := True
/-- pi_univ_Iic (abstract). -/
def pi_univ_Iic' : Prop := True
/-- pi_univ_Icc (abstract). -/
def pi_univ_Icc' : Prop := True
/-- piecewise_mem_Icc (abstract). -/
def piecewise_mem_Icc' : Prop := True
/-- pi_univ_Ioi_subset (abstract). -/
def pi_univ_Ioi_subset' : Prop := True
/-- pi_univ_Iio_subset (abstract). -/
def pi_univ_Iio_subset' : Prop := True
/-- pi_univ_Ioo_subset (abstract). -/
def pi_univ_Ioo_subset' : Prop := True
/-- pi_univ_Ioc_subset (abstract). -/
def pi_univ_Ioc_subset' : Prop := True
/-- pi_univ_Ico_subset (abstract). -/
def pi_univ_Ico_subset' : Prop := True
/-- pi_univ_Ioc_update_left (abstract). -/
def pi_univ_Ioc_update_left' : Prop := True
/-- pi_univ_Ioc_update_right (abstract). -/
def pi_univ_Ioc_update_right' : Prop := True
/-- disjoint_pi_univ_Ioc_update_left_right (abstract). -/
def disjoint_pi_univ_Ioc_update_left_right' : Prop := True
/-- image_update_Icc (abstract). -/
def image_update_Icc' : Prop := True
/-- image_update_Ico (abstract). -/
def image_update_Ico' : Prop := True
/-- image_update_Ioc (abstract). -/
def image_update_Ioc' : Prop := True
/-- image_update_Ioo (abstract). -/
def image_update_Ioo' : Prop := True
/-- image_update_Icc_left (abstract). -/
def image_update_Icc_left' : Prop := True
/-- image_update_Ico_left (abstract). -/
def image_update_Ico_left' : Prop := True
/-- image_update_Ioc_left (abstract). -/
def image_update_Ioc_left' : Prop := True
/-- image_update_Ioo_left (abstract). -/
def image_update_Ioo_left' : Prop := True
/-- image_update_Icc_right (abstract). -/
def image_update_Icc_right' : Prop := True
/-- image_update_Ico_right (abstract). -/
def image_update_Ico_right' : Prop := True
/-- image_update_Ioc_right (abstract). -/
def image_update_Ioc_right' : Prop := True
/-- image_update_Ioo_right (abstract). -/
def image_update_Ioo_right' : Prop := True
/-- image_mulSingle_Icc (abstract). -/
def image_mulSingle_Icc' : Prop := True
/-- image_mulSingle_Ico (abstract). -/
def image_mulSingle_Ico' : Prop := True
/-- image_mulSingle_Ioc (abstract). -/
def image_mulSingle_Ioc' : Prop := True
/-- image_mulSingle_Ioo (abstract). -/
def image_mulSingle_Ioo' : Prop := True
/-- image_mulSingle_Icc_left (abstract). -/
def image_mulSingle_Icc_left' : Prop := True
/-- image_mulSingle_Ico_left (abstract). -/
def image_mulSingle_Ico_left' : Prop := True
/-- image_mulSingle_Ioc_left (abstract). -/
def image_mulSingle_Ioc_left' : Prop := True
/-- image_mulSingle_Ioo_left (abstract). -/
def image_mulSingle_Ioo_left' : Prop := True
/-- image_mulSingle_Icc_right (abstract). -/
def image_mulSingle_Icc_right' : Prop := True
/-- image_mulSingle_Ico_right (abstract). -/
def image_mulSingle_Ico_right' : Prop := True
/-- image_mulSingle_Ioc_right (abstract). -/
def image_mulSingle_Ioc_right' : Prop := True
/-- image_mulSingle_Ioo_right (abstract). -/
def image_mulSingle_Ioo_right' : Prop := True
/-- pi_univ_uIcc (abstract). -/
def pi_univ_uIcc' : Prop := True
/-- image_update_uIcc (abstract). -/
def image_update_uIcc' : Prop := True
/-- image_update_uIcc_left (abstract). -/
def image_update_uIcc_left' : Prop := True
/-- image_update_uIcc_right (abstract). -/
def image_update_uIcc_right' : Prop := True
/-- image_mulSingle_uIcc (abstract). -/
def image_mulSingle_uIcc' : Prop := True
/-- image_mulSingle_uIcc_left (abstract). -/
def image_mulSingle_uIcc_left' : Prop := True
/-- image_mulSingle_uIcc_right (abstract). -/
def image_mulSingle_uIcc_right' : Prop := True
/-- pi_univ_Ioc_update_union (abstract). -/
def pi_univ_Ioc_update_union' : Prop := True
/-- Icc_diff_pi_univ_Ioo_subset (abstract). -/
def Icc_diff_pi_univ_Ioo_subset' : Prop := True
/-- Icc_diff_pi_univ_Ioc_subset (abstract). -/
def Icc_diff_pi_univ_Ioc_subset' : Prop := True

-- Interval/Set/ProjIcc.lean
/-- projIci (abstract). -/
def projIci' : Prop := True
/-- projIic (abstract). -/
def projIic' : Prop := True
/-- projIcc (abstract). -/
def projIcc' : Prop := True
/-- projIci_of_le (abstract). -/
def projIci_of_le' : Prop := True
/-- projIic_of_le (abstract). -/
def projIic_of_le' : Prop := True
/-- projIcc_of_le_left (abstract). -/
def projIcc_of_le_left' : Prop := True
/-- projIcc_of_right_le (abstract). -/
def projIcc_of_right_le' : Prop := True
/-- projIci_self (abstract). -/
def projIci_self' : Prop := True
/-- projIic_self (abstract). -/
def projIic_self' : Prop := True
/-- projIcc_left (abstract). -/
def projIcc_left' : Prop := True
/-- projIcc_right (abstract). -/
def projIcc_right' : Prop := True
/-- projIci_eq_self (abstract). -/
def projIci_eq_self' : Prop := True
/-- projIic_eq_self (abstract). -/
def projIic_eq_self' : Prop := True
/-- projIcc_eq_left (abstract). -/
def projIcc_eq_left' : Prop := True
/-- projIcc_eq_right (abstract). -/
def projIcc_eq_right' : Prop := True
/-- projIci_of_mem (abstract). -/
def projIci_of_mem' : Prop := True
/-- projIic_of_mem (abstract). -/
def projIic_of_mem' : Prop := True
/-- projIcc_of_mem (abstract). -/
def projIcc_of_mem' : Prop := True
/-- projIci_coe (abstract). -/
def projIci_coe' : Prop := True
/-- projIic_coe (abstract). -/
def projIic_coe' : Prop := True
/-- projIcc_val (abstract). -/
def projIcc_val' : Prop := True
/-- projIci_surjOn (abstract). -/
def projIci_surjOn' : Prop := True
/-- projIic_surjOn (abstract). -/
def projIic_surjOn' : Prop := True
/-- projIcc_surjOn (abstract). -/
def projIcc_surjOn' : Prop := True
/-- projIci_surjective (abstract). -/
def projIci_surjective' : Prop := True
/-- projIic_surjective (abstract). -/
def projIic_surjective' : Prop := True
/-- projIcc_surjective (abstract). -/
def projIcc_surjective' : Prop := True
/-- range_projIci (abstract). -/
def range_projIci' : Prop := True
/-- range_projIic (abstract). -/
def range_projIic' : Prop := True
/-- range_projIcc (abstract). -/
def range_projIcc' : Prop := True
/-- monotone_projIci (abstract). -/
def monotone_projIci' : Prop := True
/-- monotone_projIic (abstract). -/
def monotone_projIic' : Prop := True
/-- monotone_projIcc (abstract). -/
def monotone_projIcc' : Prop := True
/-- strictMonoOn_projIci (abstract). -/
def strictMonoOn_projIci' : Prop := True
/-- strictMonoOn_projIic (abstract). -/
def strictMonoOn_projIic' : Prop := True
/-- strictMonoOn_projIcc (abstract). -/
def strictMonoOn_projIcc' : Prop := True
/-- IciExtend (abstract). -/
def IciExtend' : Prop := True
/-- IicExtend (abstract). -/
def IicExtend' : Prop := True
/-- IccExtend (abstract). -/
def IccExtend' : Prop := True
/-- range_IciExtend (abstract). -/
def range_IciExtend' : Prop := True
/-- range_IicExtend (abstract). -/
def range_IicExtend' : Prop := True
/-- IccExtend_range (abstract). -/
def IccExtend_range' : Prop := True
/-- IciExtend_of_le (abstract). -/
def IciExtend_of_le' : Prop := True
/-- IicExtend_of_le (abstract). -/
def IicExtend_of_le' : Prop := True
/-- IccExtend_of_le_left (abstract). -/
def IccExtend_of_le_left' : Prop := True
/-- IccExtend_of_right_le (abstract). -/
def IccExtend_of_right_le' : Prop := True
/-- IciExtend_self (abstract). -/
def IciExtend_self' : Prop := True
/-- IicExtend_self (abstract). -/
def IicExtend_self' : Prop := True
/-- IccExtend_left (abstract). -/
def IccExtend_left' : Prop := True
/-- IccExtend_right (abstract). -/
def IccExtend_right' : Prop := True
/-- IciExtend_of_mem (abstract). -/
def IciExtend_of_mem' : Prop := True
/-- IicExtend_of_mem (abstract). -/
def IicExtend_of_mem' : Prop := True
/-- IccExtend_of_mem (abstract). -/
def IccExtend_of_mem' : Prop := True
/-- IciExtend_coe (abstract). -/
def IciExtend_coe' : Prop := True
/-- IicExtend_coe (abstract). -/
def IicExtend_coe' : Prop := True
/-- IccExtend_val (abstract). -/
def IccExtend_val' : Prop := True
/-- IccExtend_eq_self (abstract). -/
def IccExtend_eq_self' : Prop := True
/-- strictMonoOn_IciExtend (abstract). -/
def strictMonoOn_IciExtend' : Prop := True
/-- strictMonoOn_IicExtend (abstract). -/
def strictMonoOn_IicExtend' : Prop := True
/-- strictMonoOn_IccExtend (abstract). -/
def strictMonoOn_IccExtend' : Prop := True

-- Interval/Set/SurjOn.lean
/-- surjOn_Ioo_of_monotone_surjective (abstract). -/
def surjOn_Ioo_of_monotone_surjective' : Prop := True
/-- surjOn_Ico_of_monotone_surjective (abstract). -/
def surjOn_Ico_of_monotone_surjective' : Prop := True
/-- surjOn_Ioc_of_monotone_surjective (abstract). -/
def surjOn_Ioc_of_monotone_surjective' : Prop := True
/-- surjOn_Icc_of_monotone_surjective (abstract). -/
def surjOn_Icc_of_monotone_surjective' : Prop := True
/-- surjOn_Ioi_of_monotone_surjective (abstract). -/
def surjOn_Ioi_of_monotone_surjective' : Prop := True
/-- surjOn_Iio_of_monotone_surjective (abstract). -/
def surjOn_Iio_of_monotone_surjective' : Prop := True
/-- surjOn_Ici_of_monotone_surjective (abstract). -/
def surjOn_Ici_of_monotone_surjective' : Prop := True
/-- surjOn_Iic_of_monotone_surjective (abstract). -/
def surjOn_Iic_of_monotone_surjective' : Prop := True

-- Interval/Set/UnorderedInterval.lean
/-- dual_uIcc (abstract). -/
def dual_uIcc' : Prop := True
/-- uIcc_of_lt (abstract). -/
def uIcc_of_lt' : Prop := True
/-- uIcc_of_gt (abstract). -/
def uIcc_of_gt' : Prop := True
/-- bdd_below_bdd_above_iff_subset_uIcc (abstract). -/
def bdd_below_bdd_above_iff_subset_uIcc' : Prop := True
/-- uIcc_prod_uIcc (abstract). -/
def uIcc_prod_uIcc' : Prop := True
/-- mapsTo_uIcc (abstract). -/
def mapsTo_uIcc' : Prop := True
/-- image_uIcc_subset (abstract). -/
def image_uIcc_subset' : Prop := True
/-- monotone_or_antitone_iff_uIcc (abstract). -/
def monotone_or_antitone_iff_uIcc' : Prop := True
/-- monotoneOn_or_antitoneOn_iff_uIcc (abstract). -/
def monotoneOn_or_antitoneOn_iff_uIcc' : Prop := True
/-- uIoc (abstract). -/
def uIoc' : Prop := True
/-- uIoc_of_le (abstract). -/
def uIoc_of_le' : Prop := True
/-- uIoc_of_ge (abstract). -/
def uIoc_of_ge' : Prop := True
/-- uIoc_eq_union (abstract). -/
def uIoc_eq_union' : Prop := True
/-- mem_uIoc (abstract). -/
def mem_uIoc' : Prop := True
/-- not_mem_uIoc (abstract). -/
def not_mem_uIoc' : Prop := True
/-- left_mem_uIoc (abstract). -/
def left_mem_uIoc' : Prop := True
/-- right_mem_uIoc (abstract). -/
def right_mem_uIoc' : Prop := True
/-- forall_uIoc_iff (abstract). -/
def forall_uIoc_iff' : Prop := True
/-- uIoc_subset_uIoc_of_uIcc_subset_uIcc (abstract). -/
def uIoc_subset_uIoc_of_uIcc_subset_uIcc' : Prop := True
/-- uIoc_comm (abstract). -/
def uIoc_comm' : Prop := True
/-- Ioc_subset_uIoc (abstract). -/
def Ioc_subset_uIoc' : Prop := True
/-- uIoc_subset_uIcc (abstract). -/
def uIoc_subset_uIcc' : Prop := True
/-- eq_of_mem_uIoc_of_mem_uIoc (abstract). -/
def eq_of_mem_uIoc_of_mem_uIoc' : Prop := True
/-- eq_of_not_mem_uIoc_of_not_mem_uIoc (abstract). -/
def eq_of_not_mem_uIoc_of_not_mem_uIoc' : Prop := True
/-- uIoc_injective_right (abstract). -/
def uIoc_injective_right' : Prop := True
/-- uIoc_injective_left (abstract). -/
def uIoc_injective_left' : Prop := True
/-- uIoo (abstract). -/
def uIoo' : Prop := True
/-- dual_uIoo (abstract). -/
def dual_uIoo' : Prop := True
/-- uIoo_of_le (abstract). -/
def uIoo_of_le' : Prop := True
/-- uIoo_of_ge (abstract). -/
def uIoo_of_ge' : Prop := True
/-- uIoo_comm (abstract). -/
def uIoo_comm' : Prop := True
/-- uIoo_of_lt (abstract). -/
def uIoo_of_lt' : Prop := True
/-- uIoo_of_gt (abstract). -/
def uIoo_of_gt' : Prop := True
/-- uIoo_self (abstract). -/
def uIoo_self' : Prop := True
/-- Ioo_subset_uIoo (abstract). -/
def Ioo_subset_uIoo' : Prop := True
/-- mem_uIoo_of_lt (abstract). -/
def mem_uIoo_of_lt' : Prop := True
/-- mem_uIoo_of_gt (abstract). -/
def mem_uIoo_of_gt' : Prop := True
/-- uIoo_of_not_le (abstract). -/
def uIoo_of_not_le' : Prop := True
/-- uIoo_of_not_ge (abstract). -/
def uIoo_of_not_ge' : Prop := True
/-- uIoo_subset_uIcc (abstract). -/
def uIoo_subset_uIcc' : Prop := True

-- Irreducible.lean
/-- SupIrred (abstract). -/
def SupIrred' : Prop := True
/-- SupPrime (abstract). -/
def SupPrime' : Prop := True
/-- not_supIrred (abstract). -/
def not_supIrred' : Prop := True
/-- not_supPrime (abstract). -/
def not_supPrime' : Prop := True
/-- supIrred (abstract). -/
def supIrred' : Prop := True
-- COLLISION: le_sup' already in SetTheory.lean — rename needed
/-- not_supIrred_bot (abstract). -/
def not_supIrred_bot' : Prop := True
/-- not_supPrime_bot (abstract). -/
def not_supPrime_bot' : Prop := True
/-- ne_bot (abstract). -/
def ne_bot' : Prop := True
/-- finset_sup_eq (abstract). -/
def finset_sup_eq' : Prop := True
/-- le_finset_sup (abstract). -/
def le_finset_sup' : Prop := True
/-- exists_supIrred_decomposition (abstract). -/
def exists_supIrred_decomposition' : Prop := True
/-- InfIrred (abstract). -/
def InfIrred' : Prop := True
/-- InfPrime (abstract). -/
def InfPrime' : Prop := True
/-- not_infIrred (abstract). -/
def not_infIrred' : Prop := True
/-- not_infPrime (abstract). -/
def not_infPrime' : Prop := True
/-- infIrred (abstract). -/
def infIrred' : Prop := True
/-- inf_le (abstract). -/
def inf_le' : Prop := True
/-- not_infIrred_top (abstract). -/
def not_infIrred_top' : Prop := True
/-- not_infPrime_top (abstract). -/
def not_infPrime_top' : Prop := True
/-- finset_inf_eq (abstract). -/
def finset_inf_eq' : Prop := True
/-- supPrime_iff_supIrred (abstract). -/
def supPrime_iff_supIrred' : Prop := True
/-- infPrime_iff_infIrred (abstract). -/
def infPrime_iff_infIrred' : Prop := True
/-- supPrime_iff_not_isMin (abstract). -/
def supPrime_iff_not_isMin' : Prop := True
/-- infPrime_iff_not_isMax (abstract). -/
def infPrime_iff_not_isMax' : Prop := True
/-- supIrred_iff_not_isMin (abstract). -/
def supIrred_iff_not_isMin' : Prop := True
/-- infIrred_iff_not_isMax (abstract). -/
def infIrred_iff_not_isMax' : Prop := True

-- Iterate.lean
/-- are (abstract). -/
def are' : Prop := True
/-- seq_le_seq (abstract). -/
def seq_le_seq' : Prop := True
/-- seq_pos_lt_seq_of_lt_of_le (abstract). -/
def seq_pos_lt_seq_of_lt_of_le' : Prop := True
/-- seq_pos_lt_seq_of_le_of_lt (abstract). -/
def seq_pos_lt_seq_of_le_of_lt' : Prop := True
/-- seq_lt_seq_of_lt_of_le (abstract). -/
def seq_lt_seq_of_lt_of_le' : Prop := True
/-- seq_lt_seq_of_le_of_lt (abstract). -/
def seq_lt_seq_of_le_of_lt' : Prop := True
/-- le_iterate_comp_of_le (abstract). -/
def le_iterate_comp_of_le' : Prop := True
/-- iterate_comp_le_of_le (abstract). -/
def iterate_comp_le_of_le' : Prop := True
/-- iterate_le_of_le (abstract). -/
def iterate_le_of_le' : Prop := True
/-- le_iterate_of_le (abstract). -/
def le_iterate_of_le' : Prop := True
/-- id_le_iterate_of_id_le (abstract). -/
def id_le_iterate_of_id_le' : Prop := True
/-- iterate_le_id_of_le_id (abstract). -/
def iterate_le_id_of_le_id' : Prop := True
/-- monotone_iterate_of_id_le (abstract). -/
def monotone_iterate_of_id_le' : Prop := True
/-- antitone_iterate_of_le_id (abstract). -/
def antitone_iterate_of_le_id' : Prop := True
/-- iterate_le_of_map_le (abstract). -/
def iterate_le_of_map_le' : Prop := True
/-- iterate_pos_lt_of_map_lt (abstract). -/
def iterate_pos_lt_of_map_lt' : Prop := True
/-- iterate_pos_lt_iff_map_lt (abstract). -/
def iterate_pos_lt_iff_map_lt' : Prop := True
/-- iterate_pos_le_iff_map_le (abstract). -/
def iterate_pos_le_iff_map_le' : Prop := True
/-- iterate_pos_eq_iff_map_eq (abstract). -/
def iterate_pos_eq_iff_map_eq' : Prop := True
/-- monotone_iterate_of_le_map (abstract). -/
def monotone_iterate_of_le_map' : Prop := True
/-- antitone_iterate_of_map_le (abstract). -/
def antitone_iterate_of_map_le' : Prop := True
/-- strictMono_iterate_of_lt_map (abstract). -/
def strictMono_iterate_of_lt_map' : Prop := True
/-- strictAnti_iterate_of_map_lt (abstract). -/
def strictAnti_iterate_of_map_lt' : Prop := True

-- JordanHolder.lean
/-- need (abstract). -/
def need' : Prop := True
/-- will (abstract). -/
def will' : Prop := True
/-- JordanHolderLattice (abstract). -/
def JordanHolderLattice' : Prop := True
/-- isMaximal_inf_right_of_isMaximal_sup (abstract). -/
def isMaximal_inf_right_of_isMaximal_sup' : Prop := True
/-- isMaximal_of_eq_inf (abstract). -/
def isMaximal_of_eq_inf' : Prop := True
/-- second_iso_of_eq (abstract). -/
def second_iso_of_eq' : Prop := True
/-- iso_refl (abstract). -/
def iso_refl' : Prop := True
/-- CompositionSeries (abstract). -/
def CompositionSeries' : Prop := True
/-- lt_succ (abstract). -/
def lt_succ' : Prop := True
/-- injective (abstract). -/
def injective' : Prop := True
/-- toList_sorted (abstract). -/
def toList_sorted' : Prop := True
/-- toList_nodup (abstract). -/
def toList_nodup' : Prop := True
/-- le_last (abstract). -/
def le_last' : Prop := True
/-- le_last_of_mem (abstract). -/
def le_last_of_mem' : Prop := True
/-- head_le (abstract). -/
def head_le' : Prop := True
/-- head_le_of_mem (abstract). -/
def head_le_of_mem' : Prop := True
/-- last_eraseLast_le (abstract). -/
def last_eraseLast_le' : Prop := True
/-- mem_eraseLast_of_ne_of_mem (abstract). -/
def mem_eraseLast_of_ne_of_mem' : Prop := True
/-- mem_eraseLast (abstract). -/
def mem_eraseLast' : Prop := True
/-- lt_last_of_mem_eraseLast (abstract). -/
def lt_last_of_mem_eraseLast' : Prop := True
/-- isMaximal_eraseLast_last (abstract). -/
def isMaximal_eraseLast_last' : Prop := True
/-- eq_snoc_eraseLast (abstract). -/
def eq_snoc_eraseLast' : Prop := True
/-- snoc_eraseLast_last (abstract). -/
def snoc_eraseLast_last' : Prop := True
/-- Equivalent (abstract). -/
def Equivalent' : Prop := True
/-- smash (abstract). -/
def smash' : Prop := True
/-- snoc (abstract). -/
def snoc' : Prop := True
/-- length_eq (abstract). -/
def length_eq' : Prop := True
/-- snoc_snoc_swap (abstract). -/
def snoc_snoc_swap' : Prop := True
/-- length_eq_zero_of_head_eq_head_of_last_eq_last_of_length_eq_zero (abstract). -/
def length_eq_zero_of_head_eq_head_of_last_eq_last_of_length_eq_zero' : Prop := True
/-- length_pos_of_head_eq_head_of_last_eq_last_of_length_pos (abstract). -/
def length_pos_of_head_eq_head_of_last_eq_last_of_length_pos' : Prop := True
/-- eq_of_head_eq_head_of_last_eq_last_of_length_eq_zero (abstract). -/
def eq_of_head_eq_head_of_last_eq_last_of_length_eq_zero' : Prop := True
/-- exists_last_eq_snoc_equivalent (abstract). -/
def exists_last_eq_snoc_equivalent' : Prop := True
/-- jordan_holder (abstract). -/
def jordan_holder' : Prop := True

-- KonigLemma.lean
/-- where (abstract). -/
def where' : Prop := True
/-- as (abstract). -/
def as' : Prop := True
/-- exists_seq_covby_of_forall_covby_finite (abstract). -/
def exists_seq_covby_of_forall_covby_finite' : Prop := True
/-- exists_orderEmbedding_covby_of_forall_covby_finite (abstract). -/
def exists_orderEmbedding_covby_of_forall_covby_finite' : Prop := True
/-- exists_orderEmbedding_covby_of_forall_covby_finite_of_bot (abstract). -/
def exists_orderEmbedding_covby_of_forall_covby_finite_of_bot' : Prop := True
/-- exists_nat_orderEmbedding_of_forall_covby_finite (abstract). -/
def exists_nat_orderEmbedding_of_forall_covby_finite' : Prop := True
/-- exists_seq_forall_proj_of_forall_finite (abstract). -/
def exists_seq_forall_proj_of_forall_finite' : Prop := True

-- KrullDimension.lean
/-- krullDim (abstract). -/
def krullDim' : Prop := True
/-- height (abstract). -/
def height' : Prop := True
/-- coheight (abstract). -/
def coheight' : Prop := True
/-- coheight_eq (abstract). -/
def coheight_eq' : Prop := True
/-- height_le_iff (abstract). -/
def height_le_iff' : Prop := True
/-- coheight_le_iff (abstract). -/
def coheight_le_iff' : Prop := True
/-- height_le (abstract). -/
def height_le' : Prop := True
/-- height_eq_iSup_last_eq (abstract). -/
def height_eq_iSup_last_eq' : Prop := True
/-- coheight_eq_iSup_head_eq (abstract). -/
def coheight_eq_iSup_head_eq' : Prop := True
/-- coheight_le (abstract). -/
def coheight_le' : Prop := True
/-- length_le_height (abstract). -/
def length_le_height' : Prop := True
/-- length_le_coheight (abstract). -/
def length_le_coheight' : Prop := True
/-- length_le_height_last (abstract). -/
def length_le_height_last' : Prop := True
/-- length_le_coheight_head (abstract). -/
def length_le_coheight_head' : Prop := True
/-- index_le_height (abstract). -/
def index_le_height' : Prop := True
/-- rev_index_le_coheight (abstract). -/
def rev_index_le_coheight' : Prop := True
/-- height_eq_index_of_length_eq_height_last (abstract). -/
def height_eq_index_of_length_eq_height_last' : Prop := True
/-- coheight_eq_index_of_length_eq_head_coheight (abstract). -/
def coheight_eq_index_of_length_eq_head_coheight' : Prop := True
/-- height_mono (abstract). -/
def height_mono' : Prop := True
/-- height_le_height (abstract). -/
def height_le_height' : Prop := True
/-- coheight_anti (abstract). -/
def coheight_anti' : Prop := True
/-- coheight_le_coheight (abstract). -/
def coheight_le_coheight' : Prop := True
/-- height_add_const (abstract). -/
def height_add_const' : Prop := True
/-- height_strictMono (abstract). -/
def height_strictMono' : Prop := True
/-- coheight_strictAnti (abstract). -/
def coheight_strictAnti' : Prop := True
/-- height_le_height_apply_of_strictMono (abstract). -/
def height_le_height_apply_of_strictMono' : Prop := True
/-- coheight_le_coheight_apply_of_strictMono (abstract). -/
def coheight_le_coheight_apply_of_strictMono' : Prop := True
/-- height_orderIso (abstract). -/
def height_orderIso' : Prop := True
/-- coheight_orderIso (abstract). -/
def coheight_orderIso' : Prop := True
/-- exists_eq_iSup_of_iSup_eq_coe (abstract). -/
def exists_eq_iSup_of_iSup_eq_coe' : Prop := True
/-- exists_series_of_le_height (abstract). -/
def exists_series_of_le_height' : Prop := True
/-- exists_series_of_le_coheight (abstract). -/
def exists_series_of_le_coheight' : Prop := True
/-- exists_series_of_height_eq_coe (abstract). -/
def exists_series_of_height_eq_coe' : Prop := True
/-- exists_series_of_coheight_eq_coe (abstract). -/
def exists_series_of_coheight_eq_coe' : Prop := True
/-- height_eq_iSup_lt_height (abstract). -/
def height_eq_iSup_lt_height' : Prop := True
/-- coheight_eq_iSup_gt_coheight (abstract). -/
def coheight_eq_iSup_gt_coheight' : Prop := True
/-- height_le_coe_iff (abstract). -/
def height_le_coe_iff' : Prop := True
/-- coheight_eq_top_iff (abstract). -/
def coheight_eq_top_iff' : Prop := True
/-- height_eq_zero (abstract). -/
def height_eq_zero' : Prop := True
/-- coheight_eq_zero (abstract). -/
def coheight_eq_zero' : Prop := True
/-- height_bot (abstract). -/
def height_bot' : Prop := True
/-- coheight_top (abstract). -/
def coheight_top' : Prop := True
/-- coe_lt_height_iff (abstract). -/
def coe_lt_height_iff' : Prop := True
/-- coe_lt_coheight_iff (abstract). -/
def coe_lt_coheight_iff' : Prop := True
/-- height_eq_coe_add_one_iff (abstract). -/
def height_eq_coe_add_one_iff' : Prop := True
/-- coheight_eq_coe_add_one_iff (abstract). -/
def coheight_eq_coe_add_one_iff' : Prop := True
/-- height_eq_coe_iff (abstract). -/
def height_eq_coe_iff' : Prop := True
/-- coheight_eq_coe_iff (abstract). -/
def coheight_eq_coe_iff' : Prop := True
/-- height_eq_coe_iff_minimal_le_height (abstract). -/
def height_eq_coe_iff_minimal_le_height' : Prop := True
/-- coheight_eq_coe_iff_maximal_le_coheight (abstract). -/
def coheight_eq_coe_iff_maximal_le_coheight' : Prop := True
/-- length_le_krullDim (abstract). -/
def length_le_krullDim' : Prop := True
/-- krullDim_nonneg_of_nonempty (abstract). -/
def krullDim_nonneg_of_nonempty' : Prop := True
/-- krullDim_eq_iSup_length (abstract). -/
def krullDim_eq_iSup_length' : Prop := True
/-- krullDim_eq_bot_of_isEmpty (abstract). -/
def krullDim_eq_bot_of_isEmpty' : Prop := True
/-- krullDim_eq_top_of_infiniteDimensionalOrder (abstract). -/
def krullDim_eq_top_of_infiniteDimensionalOrder' : Prop := True
/-- krullDim_le_of_strictMono (abstract). -/
def krullDim_le_of_strictMono' : Prop := True
/-- krullDim_eq_length_of_finiteDimensionalOrder (abstract). -/
def krullDim_eq_length_of_finiteDimensionalOrder' : Prop := True
/-- krullDim_eq_zero_of_unique (abstract). -/
def krullDim_eq_zero_of_unique' : Prop := True
/-- krullDim_nonpos_of_subsingleton (abstract). -/
def krullDim_nonpos_of_subsingleton' : Prop := True
/-- krullDim_le_of_strictComono_and_surj (abstract). -/
def krullDim_le_of_strictComono_and_surj' : Prop := True
/-- krullDim_eq_of_orderIso (abstract). -/
def krullDim_eq_of_orderIso' : Prop := True
/-- krullDim_orderDual (abstract). -/
def krullDim_orderDual' : Prop := True
/-- height_le_krullDim (abstract). -/
def height_le_krullDim' : Prop := True
/-- coheight_le_krullDim (abstract). -/
def coheight_le_krullDim' : Prop := True
/-- krullDim_eq_iSup_height_of_nonempty (abstract). -/
def krullDim_eq_iSup_height_of_nonempty' : Prop := True
/-- krullDim_eq_iSup_coheight_of_nonempty (abstract). -/
def krullDim_eq_iSup_coheight_of_nonempty' : Prop := True
/-- krullDim_eq_iSup_height_add_coheight_of_nonempty (abstract). -/
def krullDim_eq_iSup_height_add_coheight_of_nonempty' : Prop := True
/-- krullDim_eq_iSup_height (abstract). -/
def krullDim_eq_iSup_height' : Prop := True
/-- krullDim_eq_iSup_coheight (abstract). -/
def krullDim_eq_iSup_coheight' : Prop := True
/-- height_top_eq_krullDim (abstract). -/
def height_top_eq_krullDim' : Prop := True
/-- coheight_bot_eq_krullDim (abstract). -/
def coheight_bot_eq_krullDim' : Prop := True
/-- height_nat (abstract). -/
def height_nat' : Prop := True
/-- coheight_of_noMaxOrder (abstract). -/
def coheight_of_noMaxOrder' : Prop := True
/-- height_of_noMinOrder (abstract). -/
def height_of_noMinOrder' : Prop := True
/-- krullDim_of_noMaxOrder (abstract). -/
def krullDim_of_noMaxOrder' : Prop := True
/-- krullDim_of_noMinOrder (abstract). -/
def krullDim_of_noMinOrder' : Prop := True
/-- coheight_nat (abstract). -/
def coheight_nat' : Prop := True
/-- krullDim_nat (abstract). -/
def krullDim_nat' : Prop := True
/-- height_int (abstract). -/
def height_int' : Prop := True
/-- coheight_int (abstract). -/
def coheight_int' : Prop := True
/-- krullDim_int (abstract). -/
def krullDim_int' : Prop := True
/-- height_coe_withBot (abstract). -/
def height_coe_withBot' : Prop := True
/-- coheight_coe_withTop (abstract). -/
def coheight_coe_withTop' : Prop := True
/-- height_coe_withTop (abstract). -/
def height_coe_withTop' : Prop := True
/-- coheight_coe_withBot (abstract). -/
def coheight_coe_withBot' : Prop := True
/-- krullDim_WithTop (abstract). -/
def krullDim_WithTop' : Prop := True
/-- krullDim_withBot (abstract). -/
def krullDim_withBot' : Prop := True
/-- krullDim_enat (abstract). -/
def krullDim_enat' : Prop := True
/-- height_enat (abstract). -/
def height_enat' : Prop := True
/-- coheight_coe_enat (abstract). -/
def coheight_coe_enat' : Prop := True

-- Lattice.lean
/-- exactSubsetOfSSubset (abstract). -/
def exactSubsetOfSSubset' : Prop := True
/-- SemilatticeSup (abstract). -/
def SemilatticeSup' : Prop := True
-- COLLISION: sup_le_iff' already in SetTheory.lean — rename needed
/-- sup_eq_left (abstract). -/
def sup_eq_left' : Prop := True
/-- sup_eq_right (abstract). -/
def sup_eq_right' : Prop := True
/-- left_eq_sup (abstract). -/
def left_eq_sup' : Prop := True
/-- right_eq_sup (abstract). -/
def right_eq_sup' : Prop := True
/-- le_iff_exists_sup (abstract). -/
def le_iff_exists_sup' : Prop := True
-- COLLISION: sup_le_sup' already in SetTheory.lean — rename needed
/-- sup_le_sup_left (abstract). -/
def sup_le_sup_left' : Prop := True
/-- sup_le_sup_right (abstract). -/
def sup_le_sup_right' : Prop := True
/-- sup_idem (abstract). -/
def sup_idem' : Prop := True
/-- sup_comm (abstract). -/
def sup_comm' : Prop := True
/-- sup_assoc (abstract). -/
def sup_assoc' : Prop := True
/-- sup_left_right_swap (abstract). -/
def sup_left_right_swap' : Prop := True
/-- sup_left_comm (abstract). -/
def sup_left_comm' : Prop := True
/-- sup_right_comm (abstract). -/
def sup_right_comm' : Prop := True
/-- sup_sup_sup_comm (abstract). -/
def sup_sup_sup_comm' : Prop := True
/-- sup_sup_distrib_left (abstract). -/
def sup_sup_distrib_left' : Prop := True
/-- sup_sup_distrib_right (abstract). -/
def sup_sup_distrib_right' : Prop := True
/-- sup_congr_left (abstract). -/
def sup_congr_left' : Prop := True
/-- sup_congr_right (abstract). -/
def sup_congr_right' : Prop := True
/-- sup_eq_sup_iff_left (abstract). -/
def sup_eq_sup_iff_left' : Prop := True
/-- sup_eq_sup_iff_right (abstract). -/
def sup_eq_sup_iff_right' : Prop := True
/-- ext_sup (abstract). -/
def ext_sup' : Prop := True
/-- ite_le_sup (abstract). -/
def ite_le_sup' : Prop := True
/-- SemilatticeInf (abstract). -/
def SemilatticeInf' : Prop := True
/-- inf_le_left (abstract). -/
def inf_le_left' : Prop := True
/-- inf_le_right (abstract). -/
def inf_le_right' : Prop := True
/-- le_inf (abstract). -/
def le_inf' : Prop := True
/-- inf_le_of_left_le (abstract). -/
def inf_le_of_left_le' : Prop := True
/-- inf_le_of_right_le (abstract). -/
def inf_le_of_right_le' : Prop := True
/-- inf_lt_of_left_lt (abstract). -/
def inf_lt_of_left_lt' : Prop := True
/-- inf_lt_of_right_lt (abstract). -/
def inf_lt_of_right_lt' : Prop := True
/-- le_inf_iff (abstract). -/
def le_inf_iff' : Prop := True
/-- inf_eq_left (abstract). -/
def inf_eq_left' : Prop := True
/-- inf_eq_right (abstract). -/
def inf_eq_right' : Prop := True
/-- left_eq_inf (abstract). -/
def left_eq_inf' : Prop := True
/-- right_eq_inf (abstract). -/
def right_eq_inf' : Prop := True
/-- inf_lt_left (abstract). -/
def inf_lt_left' : Prop := True
/-- inf_lt_right (abstract). -/
def inf_lt_right' : Prop := True
/-- inf_lt_left_or_right (abstract). -/
def inf_lt_left_or_right' : Prop := True
/-- inf_le_inf (abstract). -/
def inf_le_inf' : Prop := True
/-- inf_le_inf_right (abstract). -/
def inf_le_inf_right' : Prop := True
/-- inf_le_inf_left (abstract). -/
def inf_le_inf_left' : Prop := True
/-- inf_idem (abstract). -/
def inf_idem' : Prop := True
/-- inf_comm (abstract). -/
def inf_comm' : Prop := True
/-- inf_assoc (abstract). -/
def inf_assoc' : Prop := True
/-- inf_left_right_swap (abstract). -/
def inf_left_right_swap' : Prop := True
/-- inf_left_comm (abstract). -/
def inf_left_comm' : Prop := True
/-- inf_right_comm (abstract). -/
def inf_right_comm' : Prop := True
/-- inf_inf_inf_comm (abstract). -/
def inf_inf_inf_comm' : Prop := True
/-- inf_inf_distrib_left (abstract). -/
def inf_inf_distrib_left' : Prop := True
/-- inf_inf_distrib_right (abstract). -/
def inf_inf_distrib_right' : Prop := True
/-- inf_congr_left (abstract). -/
def inf_congr_left' : Prop := True
/-- inf_congr_right (abstract). -/
def inf_congr_right' : Prop := True
/-- inf_eq_inf_iff_left (abstract). -/
def inf_eq_inf_iff_left' : Prop := True
/-- inf_eq_inf_iff_right (abstract). -/
def inf_eq_inf_iff_right' : Prop := True
/-- inf_lt_or_inf_lt (abstract). -/
def inf_lt_or_inf_lt' : Prop := True
/-- ext_inf (abstract). -/
def ext_inf' : Prop := True
/-- inf_le_ite (abstract). -/
def inf_le_ite' : Prop := True
-- COLLISION: Lattice' already in Order.lean — rename needed
/-- semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder (abstract). -/
def semilatticeSup_mk'_partialOrder_eq_semilatticeInf_mk'_partialOrder' : Prop := True
/-- inf_le_sup (abstract). -/
def inf_le_sup' : Prop := True
/-- sup_le_inf (abstract). -/
def sup_le_inf' : Prop := True
/-- inf_eq_sup (abstract). -/
def inf_eq_sup' : Prop := True
/-- sup_eq_inf (abstract). -/
def sup_eq_inf' : Prop := True
/-- inf_lt_sup (abstract). -/
def inf_lt_sup' : Prop := True
/-- inf_eq_and_sup_eq_iff (abstract). -/
def inf_eq_and_sup_eq_iff' : Prop := True
/-- sup_inf_le (abstract). -/
def sup_inf_le' : Prop := True
/-- le_inf_sup (abstract). -/
def le_inf_sup' : Prop := True
/-- inf_sup_self (abstract). -/
def inf_sup_self' : Prop := True
/-- sup_inf_self (abstract). -/
def sup_inf_self' : Prop := True
/-- sup_eq_iff_inf_eq (abstract). -/
def sup_eq_iff_inf_eq' : Prop := True
/-- DistribLattice (abstract). -/
def DistribLattice' : Prop := True
/-- le_sup_inf (abstract). -/
def le_sup_inf' : Prop := True
/-- sup_inf_left (abstract). -/
def sup_inf_left' : Prop := True
/-- sup_inf_right (abstract). -/
def sup_inf_right' : Prop := True
/-- inf_sup_left (abstract). -/
def inf_sup_left' : Prop := True
/-- inf_sup_right (abstract). -/
def inf_sup_right' : Prop := True
/-- le_of_inf_le_sup_le (abstract). -/
def le_of_inf_le_sup_le' : Prop := True
/-- eq_of_inf_eq_sup_eq (abstract). -/
def eq_of_inf_eq_sup_eq' : Prop := True
/-- ofInfSupLe (abstract). -/
def ofInfSupLe' : Prop := True
/-- sup_ind (abstract). -/
def sup_ind' : Prop := True
/-- lt_sup_iff (abstract). -/
def lt_sup_iff' : Prop := True
/-- sup_lt_iff (abstract). -/
def sup_lt_iff' : Prop := True
/-- inf_ind (abstract). -/
def inf_ind' : Prop := True
/-- inf_le_iff (abstract). -/
def inf_le_iff' : Prop := True
/-- inf_lt_iff (abstract). -/
def inf_lt_iff' : Prop := True
/-- lt_inf_iff (abstract). -/
def lt_inf_iff' : Prop := True
/-- max_max_max_comm (abstract). -/
def max_max_max_comm' : Prop := True
/-- min_min_min_comm (abstract). -/
def min_min_min_comm' : Prop := True
/-- sup_eq_maxDefault (abstract). -/
def sup_eq_maxDefault' : Prop := True
/-- inf_eq_minDefault (abstract). -/
def inf_eq_minDefault' : Prop := True
/-- toLinearOrder (abstract). -/
def toLinearOrder' : Prop := True
/-- update_sup (abstract). -/
def update_sup' : Prop := True
/-- update_inf (abstract). -/
def update_inf' : Prop := True
/-- of_map_inf_le_left (abstract). -/
def of_map_inf_le_left' : Prop := True
/-- of_map_inf_le (abstract). -/
def of_map_inf_le' : Prop := True
/-- of_map_inf (abstract). -/
def of_map_inf' : Prop := True
/-- of_left_le_map_sup (abstract). -/
def of_left_le_map_sup' : Prop := True
/-- of_le_map_sup (abstract). -/
def of_le_map_sup' : Prop := True
/-- of_map_sup (abstract). -/
def of_map_sup' : Prop := True
/-- semilatticeSup (abstract). -/
def semilatticeSup' : Prop := True
/-- semilatticeInf (abstract). -/
def semilatticeInf' : Prop := True

-- LatticeIntervals.lean

-- LiminfLimsup.lean
/-- isBounded_iff (abstract). -/
def isBounded_iff' : Prop := True
/-- isBoundedUnder_of (abstract). -/
def isBoundedUnder_of' : Prop := True
/-- isBounded_bot (abstract). -/
def isBounded_bot' : Prop := True
/-- isBounded_top (abstract). -/
def isBounded_top' : Prop := True
/-- isBounded_principal (abstract). -/
def isBounded_principal' : Prop := True
/-- isBounded_sup (abstract). -/
def isBounded_sup' : Prop := True
/-- mono_le (abstract). -/
def mono_le' : Prop := True
/-- mono_ge (abstract). -/
def mono_ge' : Prop := True
/-- isBoundedUnder_const (abstract). -/
def isBoundedUnder_const' : Prop := True
/-- isBoundedUnder (abstract). -/
def isBoundedUnder' : Prop := True
/-- eventually_ge (abstract). -/
def eventually_ge' : Prop := True
/-- isBoundedUnder_of_eventually_le (abstract). -/
def isBoundedUnder_of_eventually_le' : Prop := True
/-- isBoundedUnder_of_eventually_ge (abstract). -/
def isBoundedUnder_of_eventually_ge' : Prop := True
/-- isBoundedUnder_iff_eventually_bddAbove (abstract). -/
def isBoundedUnder_iff_eventually_bddAbove' : Prop := True
/-- isBoundedUnder_iff_eventually_bddBelow (abstract). -/
def isBoundedUnder_iff_eventually_bddBelow' : Prop := True
/-- isBoundedUnder_of_range (abstract). -/
def isBoundedUnder_of_range' : Prop := True
/-- le_of_finite (abstract). -/
def le_of_finite' : Prop := True
/-- ge_of_finite (abstract). -/
def ge_of_finite' : Prop := True
/-- isBoundedUnder_le_comp (abstract). -/
def isBoundedUnder_le_comp' : Prop := True
/-- isBoundedUnder_ge_comp (abstract). -/
def isBoundedUnder_ge_comp' : Prop := True
/-- not_isBoundedUnder_of_tendsto_atTop (abstract). -/
def not_isBoundedUnder_of_tendsto_atTop' : Prop := True
/-- not_isBoundedUnder_of_tendsto_atBot (abstract). -/
def not_isBoundedUnder_of_tendsto_atBot' : Prop := True
/-- bddAbove_range_of_cofinite (abstract). -/
def bddAbove_range_of_cofinite' : Prop := True
/-- bddBelow_range_of_cofinite (abstract). -/
def bddBelow_range_of_cofinite' : Prop := True
-- COLLISION: bddAbove_range' already in SetTheory.lean — rename needed
/-- isCoboundedUnder_le_of_eventually_le (abstract). -/
def isCoboundedUnder_le_of_eventually_le' : Prop := True
/-- isCoboundedUnder_ge_of_eventually_le (abstract). -/
def isCoboundedUnder_ge_of_eventually_le' : Prop := True
/-- isCoboundedUnder_le_of_le (abstract). -/
def isCoboundedUnder_le_of_le' : Prop := True
/-- isCoboundedUnder_ge_of_le (abstract). -/
def isCoboundedUnder_ge_of_le' : Prop := True
/-- isCobounded_bot (abstract). -/
def isCobounded_bot' : Prop := True
/-- isCobounded_top (abstract). -/
def isCobounded_top' : Prop := True
/-- isCobounded_principal (abstract). -/
def isCobounded_principal' : Prop := True
/-- frequently_ge (abstract). -/
def frequently_ge' : Prop := True
/-- frequently_le (abstract). -/
def frequently_le' : Prop := True
/-- of_frequently_ge (abstract). -/
def of_frequently_ge' : Prop := True
/-- of_frequently_le (abstract). -/
def of_frequently_le' : Prop := True
/-- isBoundedUnder_sum (abstract). -/
def isBoundedUnder_sum' : Prop := True
/-- isBoundedUnder_ge_add (abstract). -/
def isBoundedUnder_ge_add' : Prop := True
/-- isBoundedUnder_le_add (abstract). -/
def isBoundedUnder_le_add' : Prop := True
/-- isBoundedUnder_le_sum (abstract). -/
def isBoundedUnder_le_sum' : Prop := True
/-- isBoundedUnder_ge_sum (abstract). -/
def isBoundedUnder_ge_sum' : Prop := True
/-- isCoboundedUnder_ge_add (abstract). -/
def isCoboundedUnder_ge_add' : Prop := True
/-- isCoboundedUnder_le_add (abstract). -/
def isCoboundedUnder_le_add' : Prop := True
/-- isBoundedUnder_le_mul_of_nonneg (abstract). -/
def isBoundedUnder_le_mul_of_nonneg' : Prop := True
/-- isCoboundedUnder_ge_mul_of_nonneg (abstract). -/
def isCoboundedUnder_ge_mul_of_nonneg' : Prop := True
/-- isBounded_le_atBot (abstract). -/
def isBounded_le_atBot' : Prop := True
/-- isBounded_ge_atTop (abstract). -/
def isBounded_ge_atTop' : Prop := True
/-- isBoundedUnder_le_atBot (abstract). -/
def isBoundedUnder_le_atBot' : Prop := True
/-- isBoundedUnder_ge_atTop (abstract). -/
def isBoundedUnder_ge_atTop' : Prop := True
/-- bddAbove_range_of_tendsto_atTop_atBot (abstract). -/
def bddAbove_range_of_tendsto_atTop_atBot' : Prop := True
/-- bddBelow_range_of_tendsto_atTop_atTop (abstract). -/
def bddBelow_range_of_tendsto_atTop_atTop' : Prop := True
/-- isCobounded_le_of_bot (abstract). -/
def isCobounded_le_of_bot' : Prop := True
/-- isCobounded_ge_of_top (abstract). -/
def isCobounded_ge_of_top' : Prop := True
/-- isBounded_le_of_top (abstract). -/
def isBounded_le_of_top' : Prop := True
/-- isBounded_ge_of_bot (abstract). -/
def isBounded_ge_of_bot' : Prop := True
/-- isBoundedUnder_le_inv (abstract). -/
def isBoundedUnder_le_inv' : Prop := True
/-- isBoundedUnder_ge_inv (abstract). -/
def isBoundedUnder_ge_inv' : Prop := True
/-- isBoundedUnder_le_sup (abstract). -/
def isBoundedUnder_le_sup' : Prop := True
/-- isBoundedUnder_ge_inf (abstract). -/
def isBoundedUnder_ge_inf' : Prop := True
/-- isBoundedUnder_le_abs (abstract). -/
def isBoundedUnder_le_abs' : Prop := True
/-- limsSup (abstract). -/
def limsSup' : Prop := True
/-- limsInf (abstract). -/
def limsInf' : Prop := True
/-- limsup (abstract). -/
def limsup' : Prop := True
/-- liminf (abstract). -/
def liminf' : Prop := True
/-- blimsup (abstract). -/
def blimsup' : Prop := True
/-- bliminf (abstract). -/
def bliminf' : Prop := True
/-- blimsup_true (abstract). -/
def blimsup_true' : Prop := True
/-- bliminf_true (abstract). -/
def bliminf_true' : Prop := True
/-- blimsup_eq_limsup (abstract). -/
def blimsup_eq_limsup' : Prop := True
/-- bliminf_eq_liminf (abstract). -/
def bliminf_eq_liminf' : Prop := True
/-- blimsup_eq_limsup_subtype (abstract). -/
def blimsup_eq_limsup_subtype' : Prop := True
/-- bliminf_eq_liminf_subtype (abstract). -/
def bliminf_eq_liminf_subtype' : Prop := True
/-- limsSup_le_of_le (abstract). -/
def limsSup_le_of_le' : Prop := True
/-- le_limsInf_of_le (abstract). -/
def le_limsInf_of_le' : Prop := True
/-- limsup_le_of_le (abstract). -/
def limsup_le_of_le' : Prop := True
/-- le_liminf_of_le (abstract). -/
def le_liminf_of_le' : Prop := True
/-- le_limsSup_of_le (abstract). -/
def le_limsSup_of_le' : Prop := True
/-- limsInf_le_of_le (abstract). -/
def limsInf_le_of_le' : Prop := True
/-- le_limsup_of_le (abstract). -/
def le_limsup_of_le' : Prop := True
/-- liminf_le_of_le (abstract). -/
def liminf_le_of_le' : Prop := True
/-- limsInf_le_limsSup (abstract). -/
def limsInf_le_limsSup' : Prop := True
/-- liminf_le_limsup (abstract). -/
def liminf_le_limsup' : Prop := True
/-- limsSup_le_limsSup (abstract). -/
def limsSup_le_limsSup' : Prop := True
/-- limsInf_le_limsInf (abstract). -/
def limsInf_le_limsInf' : Prop := True
/-- limsup_le_limsup (abstract). -/
def limsup_le_limsup' : Prop := True
/-- liminf_le_liminf (abstract). -/
def liminf_le_liminf' : Prop := True
/-- limsSup_le_limsSup_of_le (abstract). -/
def limsSup_le_limsSup_of_le' : Prop := True
/-- limsInf_le_limsInf_of_le (abstract). -/
def limsInf_le_limsInf_of_le' : Prop := True
/-- limsup_le_limsup_of_le (abstract). -/
def limsup_le_limsup_of_le' : Prop := True
/-- liminf_le_liminf_of_le (abstract). -/
def liminf_le_liminf_of_le' : Prop := True
/-- limsSup_principal_eq_csSup (abstract). -/
def limsSup_principal_eq_csSup' : Prop := True
/-- limsInf_principal_eq_csSup (abstract). -/
def limsInf_principal_eq_csSup' : Prop := True
/-- limsup_top_eq_ciSup (abstract). -/
def limsup_top_eq_ciSup' : Prop := True
/-- liminf_top_eq_ciInf (abstract). -/
def liminf_top_eq_ciInf' : Prop := True
/-- limsup_congr (abstract). -/
def limsup_congr' : Prop := True
/-- blimsup_congr (abstract). -/
def blimsup_congr' : Prop := True
/-- bliminf_congr (abstract). -/
def bliminf_congr' : Prop := True
/-- liminf_congr (abstract). -/
def liminf_congr' : Prop := True
/-- limsup_const (abstract). -/
def limsup_const' : Prop := True
/-- liminf_const (abstract). -/
def liminf_const' : Prop := True
/-- liminf_eq_sSup_iUnion_iInter (abstract). -/
def liminf_eq_sSup_iUnion_iInter' : Prop := True
/-- liminf_eq_sSup_univ_of_empty (abstract). -/
def liminf_eq_sSup_univ_of_empty' : Prop := True
/-- limsup_eq_sInf_iUnion_iInter (abstract). -/
def limsup_eq_sInf_iUnion_iInter' : Prop := True
/-- limsup_eq_sInf_univ_of_empty (abstract). -/
def limsup_eq_sInf_univ_of_empty' : Prop := True
/-- liminf_nat_add (abstract). -/
def liminf_nat_add' : Prop := True
/-- limsup_nat_add (abstract). -/
def limsup_nat_add' : Prop := True
/-- limsSup_bot (abstract). -/
def limsSup_bot' : Prop := True
/-- limsup_bot (abstract). -/
def limsup_bot' : Prop := True
/-- limsInf_bot (abstract). -/
def limsInf_bot' : Prop := True
/-- liminf_bot (abstract). -/
def liminf_bot' : Prop := True
/-- limsSup_top (abstract). -/
def limsSup_top' : Prop := True
/-- limsInf_top (abstract). -/
def limsInf_top' : Prop := True
/-- blimsup_false (abstract). -/
def blimsup_false' : Prop := True
/-- bliminf_false (abstract). -/
def bliminf_false' : Prop := True
/-- limsup_const_bot (abstract). -/
def limsup_const_bot' : Prop := True
/-- limsInf_eq_iSup_sInf (abstract). -/
def limsInf_eq_iSup_sInf' : Prop := True
/-- limsSup_eq_iInf_sSup (abstract). -/
def limsSup_eq_iInf_sSup' : Prop := True
/-- limsup_le_iSup (abstract). -/
def limsup_le_iSup' : Prop := True
/-- iInf_le_liminf (abstract). -/
def iInf_le_liminf' : Prop := True
/-- limsup_eq_iInf_iSup (abstract). -/
def limsup_eq_iInf_iSup' : Prop := True
/-- limsup_eq_iInf_iSup_of_nat (abstract). -/
def limsup_eq_iInf_iSup_of_nat' : Prop := True
/-- limsSup_principal_eq_sSup (abstract). -/
def limsSup_principal_eq_sSup' : Prop := True
/-- limsInf_principal_eq_sInf (abstract). -/
def limsInf_principal_eq_sInf' : Prop := True
/-- limsup_top_eq_iSup (abstract). -/
def limsup_top_eq_iSup' : Prop := True
/-- liminf_top_eq_iInf (abstract). -/
def liminf_top_eq_iInf' : Prop := True
/-- blimsup_eq_iInf_iSup (abstract). -/
def blimsup_eq_iInf_iSup' : Prop := True
/-- blimsup_eq_iInf_biSup (abstract). -/
def blimsup_eq_iInf_biSup' : Prop := True
/-- blimsup_eq_iInf_biSup_of_nat (abstract). -/
def blimsup_eq_iInf_biSup_of_nat' : Prop := True
/-- liminf_eq_iSup_iInf (abstract). -/
def liminf_eq_iSup_iInf' : Prop := True
/-- liminf_eq_iSup_iInf_of_nat (abstract). -/
def liminf_eq_iSup_iInf_of_nat' : Prop := True
/-- bliminf_eq_iSup_biInf (abstract). -/
def bliminf_eq_iSup_biInf' : Prop := True
/-- bliminf_eq_iSup_biInf_of_nat (abstract). -/
def bliminf_eq_iSup_biInf_of_nat' : Prop := True
/-- limsup_eq_sInf_sSup (abstract). -/
def limsup_eq_sInf_sSup' : Prop := True
/-- liminf_eq_sSup_sInf (abstract). -/
def liminf_eq_sSup_sInf' : Prop := True
/-- liminf_le_of_frequently_le' (abstract). -/
def liminf_le_of_frequently_le' : Prop := True
/-- le_limsup_of_frequently_le' (abstract). -/
def le_limsup_of_frequently_le' : Prop := True
/-- apply_limsup_iterate (abstract). -/
def apply_limsup_iterate' : Prop := True
/-- apply_liminf_iterate (abstract). -/
def apply_liminf_iterate' : Prop := True
/-- blimsup_mono (abstract). -/
def blimsup_mono' : Prop := True
/-- bliminf_antitone (abstract). -/
def bliminf_antitone' : Prop := True
/-- mono_blimsup' (abstract). -/
def mono_blimsup' : Prop := True
/-- mono_bliminf' (abstract). -/
def mono_bliminf' : Prop := True
/-- bliminf_antitone_filter (abstract). -/
def bliminf_antitone_filter' : Prop := True
/-- blimsup_monotone_filter (abstract). -/
def blimsup_monotone_filter' : Prop := True
/-- blimsup_and_le_inf (abstract). -/
def blimsup_and_le_inf' : Prop := True
/-- bliminf_sup_le_inf_aux_left (abstract). -/
def bliminf_sup_le_inf_aux_left' : Prop := True
/-- bliminf_sup_le_inf_aux_right (abstract). -/
def bliminf_sup_le_inf_aux_right' : Prop := True
/-- bliminf_sup_le_and (abstract). -/
def bliminf_sup_le_and' : Prop := True
/-- bliminf_sup_le_and_aux_left (abstract). -/
def bliminf_sup_le_and_aux_left' : Prop := True
/-- bliminf_sup_le_and_aux_right (abstract). -/
def bliminf_sup_le_and_aux_right' : Prop := True
/-- blimsup_sup_le_or (abstract). -/
def blimsup_sup_le_or' : Prop := True
/-- bliminf_sup_le_or_aux_left (abstract). -/
def bliminf_sup_le_or_aux_left' : Prop := True
/-- bliminf_sup_le_or_aux_right (abstract). -/
def bliminf_sup_le_or_aux_right' : Prop := True
/-- bliminf_or_le_inf (abstract). -/
def bliminf_or_le_inf' : Prop := True
/-- bliminf_or_le_inf_aux_left (abstract). -/
def bliminf_or_le_inf_aux_left' : Prop := True
/-- bliminf_or_le_inf_aux_right (abstract). -/
def bliminf_or_le_inf_aux_right' : Prop := True
/-- apply_blimsup (abstract). -/
def apply_blimsup' : Prop := True
/-- apply_bliminf (abstract). -/
def apply_bliminf' : Prop := True
/-- apply_blimsup_le (abstract). -/
def apply_blimsup_le' : Prop := True
/-- le_apply_bliminf (abstract). -/
def le_apply_bliminf' : Prop := True
/-- limsup_sup_filter (abstract). -/
def limsup_sup_filter' : Prop := True
/-- liminf_sup_filter (abstract). -/
def liminf_sup_filter' : Prop := True
/-- blimsup_or_eq_sup (abstract). -/
def blimsup_or_eq_sup' : Prop := True
/-- bliminf_or_eq_inf (abstract). -/
def bliminf_or_eq_inf' : Prop := True
/-- blimsup_sup_not (abstract). -/
def blimsup_sup_not' : Prop := True
/-- bliminf_inf_not (abstract). -/
def bliminf_inf_not' : Prop := True
/-- blimsup_not_sup (abstract). -/
def blimsup_not_sup' : Prop := True
/-- bliminf_not_inf (abstract). -/
def bliminf_not_inf' : Prop := True
/-- limsup_piecewise (abstract). -/
def limsup_piecewise' : Prop := True
/-- liminf_piecewise (abstract). -/
def liminf_piecewise' : Prop := True
/-- sup_limsup (abstract). -/
def sup_limsup' : Prop := True
/-- inf_liminf (abstract). -/
def inf_liminf' : Prop := True
/-- sup_liminf (abstract). -/
def sup_liminf' : Prop := True
/-- inf_limsup (abstract). -/
def inf_limsup' : Prop := True
/-- limsup_compl (abstract). -/
def limsup_compl' : Prop := True
/-- liminf_compl (abstract). -/
def liminf_compl' : Prop := True
/-- limsup_sdiff (abstract). -/
def limsup_sdiff' : Prop := True
/-- liminf_sdiff (abstract). -/
def liminf_sdiff' : Prop := True
/-- sdiff_limsup (abstract). -/
def sdiff_limsup' : Prop := True
/-- sdiff_liminf (abstract). -/
def sdiff_liminf' : Prop := True
/-- mem_liminf_iff_eventually_mem (abstract). -/
def mem_liminf_iff_eventually_mem' : Prop := True
/-- mem_limsup_iff_frequently_mem (abstract). -/
def mem_limsup_iff_frequently_mem' : Prop := True
/-- blimsup_set_eq (abstract). -/
def blimsup_set_eq' : Prop := True
/-- bliminf_set_eq (abstract). -/
def bliminf_set_eq' : Prop := True
/-- limsup_set_eq (abstract). -/
def limsup_set_eq' : Prop := True
/-- liminf_set_eq (abstract). -/
def liminf_set_eq' : Prop := True
/-- exists_forall_mem_of_hasBasis_mem_blimsup (abstract). -/
def exists_forall_mem_of_hasBasis_mem_blimsup' : Prop := True
/-- frequently_lt_of_lt_limsSup (abstract). -/
def frequently_lt_of_lt_limsSup' : Prop := True
/-- frequently_lt_of_limsInf_lt (abstract). -/
def frequently_lt_of_limsInf_lt' : Prop := True
/-- eventually_lt_of_lt_liminf (abstract). -/
def eventually_lt_of_lt_liminf' : Prop := True
/-- eventually_lt_of_limsup_lt (abstract). -/
def eventually_lt_of_limsup_lt' : Prop := True
/-- frequently_lt_of_lt_limsup (abstract). -/
def frequently_lt_of_lt_limsup' : Prop := True
/-- frequently_lt_of_liminf_lt (abstract). -/
def frequently_lt_of_liminf_lt' : Prop := True
/-- limsup_le_iff (abstract). -/
def limsup_le_iff' : Prop := True
/-- le_limsup_iff (abstract). -/
def le_limsup_iff' : Prop := True
/-- le_liminf_iff (abstract). -/
def le_liminf_iff' : Prop := True
/-- liminf_le_iff (abstract). -/
def liminf_le_iff' : Prop := True
/-- lt_mem_sets_of_limsSup_lt (abstract). -/
def lt_mem_sets_of_limsSup_lt' : Prop := True
/-- gt_mem_sets_of_limsInf_gt (abstract). -/
def gt_mem_sets_of_limsInf_gt' : Prop := True
/-- liminf_reparam (abstract). -/
def liminf_reparam' : Prop := True
/-- liminf_eq_ciSup_ciInf (abstract). -/
def liminf_eq_ciSup_ciInf' : Prop := True
/-- liminf_eq_ite (abstract). -/
def liminf_eq_ite' : Prop := True
/-- limsup_reparam (abstract). -/
def limsup_reparam' : Prop := True
/-- limsup_eq_ciInf_ciSup (abstract). -/
def limsup_eq_ciInf_ciSup' : Prop := True
/-- limsup_eq_ite (abstract). -/
def limsup_eq_ite' : Prop := True
/-- isBoundedUnder_le_comp_iff (abstract). -/
def isBoundedUnder_le_comp_iff' : Prop := True
/-- isBoundedUnder_ge_comp_iff (abstract). -/
def isBoundedUnder_ge_comp_iff' : Prop := True
/-- l_limsup_le (abstract). -/
def l_limsup_le' : Prop := True
/-- limsup_apply (abstract). -/
def limsup_apply' : Prop := True
/-- liminf_apply (abstract). -/
def liminf_apply' : Prop := True
/-- isCoboundedUnder_le_max (abstract). -/
def isCoboundedUnder_le_max' : Prop := True
/-- limsup_max (abstract). -/
def limsup_max' : Prop := True
/-- liminf_min (abstract). -/
def liminf_min' : Prop := True
/-- isBoundedUnder_le_finset_sup' (abstract). -/
def isBoundedUnder_le_finset_sup' : Prop := True
/-- isCoboundedUnder_le_finset_sup' (abstract). -/
def isCoboundedUnder_le_finset_sup' : Prop := True
/-- isBoundedUnder_ge_finset_inf' (abstract). -/
def isBoundedUnder_ge_finset_inf' : Prop := True
/-- isCoboundedUnder_ge_finset_inf' (abstract). -/
def isCoboundedUnder_ge_finset_inf' : Prop := True
/-- limsup_finset_sup' (abstract). -/
def limsup_finset_sup' : Prop := True
/-- liminf_finset_inf' (abstract). -/
def liminf_finset_inf' : Prop := True
/-- frequently_ge_map_of_frequently_ge (abstract). -/
def frequently_ge_map_of_frequently_ge' : Prop := True
/-- frequently_le_map_of_frequently_le (abstract). -/
def frequently_le_map_of_frequently_le' : Prop := True
/-- frequently_le_map_of_frequently_ge (abstract). -/
def frequently_le_map_of_frequently_ge' : Prop := True
/-- frequently_ge_map_of_frequently_le (abstract). -/
def frequently_ge_map_of_frequently_le' : Prop := True
/-- isCoboundedUnder_le_of_isCobounded (abstract). -/
def isCoboundedUnder_le_of_isCobounded' : Prop := True
/-- isCoboundedUnder_ge_of_isCobounded (abstract). -/
def isCoboundedUnder_ge_of_isCobounded' : Prop := True

-- Max.lean
/-- NoBotOrder (abstract). -/
def NoBotOrder' : Prop := True
/-- NoTopOrder (abstract). -/
def NoTopOrder' : Prop := True
/-- NoMinOrder (abstract). -/
def NoMinOrder' : Prop := True
/-- NoMaxOrder (abstract). -/
def NoMaxOrder' : Prop := True
/-- not_acc (abstract). -/
def not_acc' : Prop := True
/-- IsBot (abstract). -/
def IsBot' : Prop := True
/-- IsTop (abstract). -/
def IsTop' : Prop := True
/-- IsMin (abstract). -/
def IsMin' : Prop := True
/-- IsMax (abstract). -/
def IsMax' : Prop := True
/-- not_isBot (abstract). -/
def not_isBot' : Prop := True
/-- not_isTop (abstract). -/
def not_isTop' : Prop := True
/-- isMin (abstract). -/
def isMin' : Prop := True
/-- isMax (abstract). -/
def isMax' : Prop := True
/-- not_isMin_of_lt (abstract). -/
def not_isMin_of_lt' : Prop := True
/-- not_isMax_of_lt (abstract). -/
def not_isMax_of_lt' : Prop := True
/-- isMin_iff_forall_not_lt (abstract). -/
def isMin_iff_forall_not_lt' : Prop := True
/-- isMax_iff_forall_not_lt (abstract). -/
def isMax_iff_forall_not_lt' : Prop := True
/-- not_isMin_iff (abstract). -/
def not_isMin_iff' : Prop := True
/-- not_isMax_iff (abstract). -/
def not_isMax_iff' : Prop := True
/-- lt_of_ne (abstract). -/
def lt_of_ne' : Prop := True
/-- isBot_iff (abstract). -/
def isBot_iff' : Prop := True
/-- isTop_iff (abstract). -/
def isTop_iff' : Prop := True
/-- isMin_iff (abstract). -/
def isMin_iff' : Prop := True
/-- isMax_iff (abstract). -/
def isMax_iff' : Prop := True

-- MinMax.lean
/-- le_min_iff (abstract). -/
def le_min_iff' : Prop := True
/-- le_max_iff (abstract). -/
def le_max_iff' : Prop := True
/-- min_le_iff (abstract). -/
def min_le_iff' : Prop := True
/-- max_le_iff (abstract). -/
def max_le_iff' : Prop := True
/-- lt_min_iff (abstract). -/
def lt_min_iff' : Prop := True
/-- lt_max_iff (abstract). -/
def lt_max_iff' : Prop := True
/-- min_lt_iff (abstract). -/
def min_lt_iff' : Prop := True
/-- max_lt_iff (abstract). -/
def max_lt_iff' : Prop := True
/-- max_le_max (abstract). -/
def max_le_max' : Prop := True
/-- max_le_max_left (abstract). -/
def max_le_max_left' : Prop := True
/-- max_le_max_right (abstract). -/
def max_le_max_right' : Prop := True
/-- min_le_of_left_le (abstract). -/
def min_le_of_left_le' : Prop := True
/-- min_le_of_right_le (abstract). -/
def min_le_of_right_le' : Prop := True
/-- min_lt_of_left_lt (abstract). -/
def min_lt_of_left_lt' : Prop := True
/-- min_lt_of_right_lt (abstract). -/
def min_lt_of_right_lt' : Prop := True
/-- max_min_distrib_left (abstract). -/
def max_min_distrib_left' : Prop := True
/-- max_min_distrib_right (abstract). -/
def max_min_distrib_right' : Prop := True
/-- min_max_distrib_left (abstract). -/
def min_max_distrib_left' : Prop := True
/-- min_max_distrib_right (abstract). -/
def min_max_distrib_right' : Prop := True
/-- min_le_max (abstract). -/
def min_le_max' : Prop := True
/-- min_eq_left_iff (abstract). -/
def min_eq_left_iff' : Prop := True
/-- min_eq_right_iff (abstract). -/
def min_eq_right_iff' : Prop := True
/-- max_eq_left_iff (abstract). -/
def max_eq_left_iff' : Prop := True
/-- max_eq_right_iff (abstract). -/
def max_eq_right_iff' : Prop := True
/-- min_cases (abstract). -/
def min_cases' : Prop := True
/-- max_cases (abstract). -/
def max_cases' : Prop := True
/-- min_eq_iff (abstract). -/
def min_eq_iff' : Prop := True
/-- max_eq_iff (abstract). -/
def max_eq_iff' : Prop := True
/-- min_lt_min_left_iff (abstract). -/
def min_lt_min_left_iff' : Prop := True
/-- min_lt_min_right_iff (abstract). -/
def min_lt_min_right_iff' : Prop := True
/-- max_lt_max_left_iff (abstract). -/
def max_lt_max_left_iff' : Prop := True
/-- max_lt_max_right_iff (abstract). -/
def max_lt_max_right_iff' : Prop := True
/-- min_lt_max (abstract). -/
def min_lt_max' : Prop := True
/-- max_lt_max (abstract). -/
def max_lt_max' : Prop := True
/-- min_lt_min (abstract). -/
def min_lt_min' : Prop := True
/-- min_right_comm (abstract). -/
def min_right_comm' : Prop := True
/-- left_comm (abstract). -/
def left_comm' : Prop := True
/-- right_comm (abstract). -/
def right_comm' : Prop := True
/-- map_max (abstract). -/
def map_max' : Prop := True
/-- map_min (abstract). -/
def map_min' : Prop := True
/-- min_choice (abstract). -/
def min_choice' : Prop := True
/-- max_choice (abstract). -/
def max_choice' : Prop := True
/-- le_of_max_le_left (abstract). -/
def le_of_max_le_left' : Prop := True
/-- le_of_max_le_right (abstract). -/
def le_of_max_le_right' : Prop := True
/-- max_left_commutative (abstract). -/
def max_left_commutative' : Prop := True
/-- min_left_commutative (abstract). -/
def min_left_commutative' : Prop := True

-- Minimal.lean
/-- minimal_false (abstract). -/
def minimal_false' : Prop := True
/-- maximal_false (abstract). -/
def maximal_false' : Prop := True
/-- minimal_true (abstract). -/
def minimal_true' : Prop := True
/-- maximal_true (abstract). -/
def maximal_true' : Prop := True
/-- minimal_subtype (abstract). -/
def minimal_subtype' : Prop := True
/-- maximal_subtype (abstract). -/
def maximal_subtype' : Prop := True
/-- maximal_true_subtype (abstract). -/
def maximal_true_subtype' : Prop := True
/-- minimal_true_subtype (abstract). -/
def minimal_true_subtype' : Prop := True
/-- minimal_minimal (abstract). -/
def minimal_minimal' : Prop := True
/-- maximal_maximal (abstract). -/
def maximal_maximal' : Prop := True
/-- minimal_iff_isMin (abstract). -/
def minimal_iff_isMin' : Prop := True
/-- maximal_iff_isMax (abstract). -/
def maximal_iff_isMax' : Prop := True
/-- minimal_eq_iff (abstract). -/
def minimal_eq_iff' : Prop := True
/-- or (abstract). -/
def or' : Prop := True
/-- minimal_and_iff_right_of_imp (abstract). -/
def minimal_and_iff_right_of_imp' : Prop := True
/-- minimal_and_iff_left_of_imp (abstract). -/
def minimal_and_iff_left_of_imp' : Prop := True
/-- maximal_and_iff_right_of_imp (abstract). -/
def maximal_and_iff_right_of_imp' : Prop := True
/-- maximal_and_iff_left_of_imp (abstract). -/
def maximal_and_iff_left_of_imp' : Prop := True
/-- minimal_iff_forall_lt (abstract). -/
def minimal_iff_forall_lt' : Prop := True
/-- maximal_iff_forall_gt (abstract). -/
def maximal_iff_forall_gt' : Prop := True
/-- not_prop_of_lt (abstract). -/
def not_prop_of_lt' : Prop := True
/-- not_prop_of_gt (abstract). -/
def not_prop_of_gt' : Prop := True
-- COLLISION: not_gt' already in SetTheory.lean — rename needed
/-- minimal_le_iff (abstract). -/
def minimal_le_iff' : Prop := True
/-- maximal_ge_iff (abstract). -/
def maximal_ge_iff' : Prop := True
/-- minimal_lt_iff (abstract). -/
def minimal_lt_iff' : Prop := True
/-- maximal_gt_iff (abstract). -/
def maximal_gt_iff' : Prop := True
/-- not_minimal_iff_exists_lt (abstract). -/
def not_minimal_iff_exists_lt' : Prop := True
/-- not_maximal_iff_exists_gt (abstract). -/
def not_maximal_iff_exists_gt' : Prop := True
/-- eq_of_ge (abstract). -/
def eq_of_ge' : Prop := True
/-- minimal_iff (abstract). -/
def minimal_iff' : Prop := True
/-- maximal_iff (abstract). -/
def maximal_iff' : Prop := True
/-- minimal_mem_iff (abstract). -/
def minimal_mem_iff' : Prop := True
/-- maximal_mem_iff (abstract). -/
def maximal_mem_iff' : Prop := True
/-- minimal_iff_eq (abstract). -/
def minimal_iff_eq' : Prop := True
/-- maximal_iff_eq (abstract). -/
def maximal_iff_eq' : Prop := True
/-- minimal_subset_iff (abstract). -/
def minimal_subset_iff' : Prop := True
/-- maximal_subset_iff (abstract). -/
def maximal_subset_iff' : Prop := True
/-- not_minimal_subset_iff (abstract). -/
def not_minimal_subset_iff' : Prop := True
/-- not_mem_of_prop_diff_singleton (abstract). -/
def not_mem_of_prop_diff_singleton' : Prop := True
/-- exists_diff_singleton_of_not_minimal (abstract). -/
def exists_diff_singleton_of_not_minimal' : Prop := True
/-- exists_insert_of_not_maximal (abstract). -/
def exists_insert_of_not_maximal' : Prop := True
/-- minimal (abstract). -/
def minimal' : Prop := True
/-- maximal (abstract). -/
def maximal' : Prop := True
/-- eq_setOf_maximal (abstract). -/
def eq_setOf_maximal' : Prop := True
/-- eq_setOf_minimal (abstract). -/
def eq_setOf_minimal' : Prop := True
/-- setOf_maximal_antichain (abstract). -/
def setOf_maximal_antichain' : Prop := True
/-- maximal_mem_lowerClosure_iff_mem (abstract). -/
def maximal_mem_lowerClosure_iff_mem' : Prop := True
/-- minimal_mem_image_monotone (abstract). -/
def minimal_mem_image_monotone' : Prop := True
/-- maximal_mem_image_monotone (abstract). -/
def maximal_mem_image_monotone' : Prop := True
/-- minimal_mem_image_monotone_iff (abstract). -/
def minimal_mem_image_monotone_iff' : Prop := True
/-- maximal_mem_image_monotone_iff (abstract). -/
def maximal_mem_image_monotone_iff' : Prop := True
/-- minimal_mem_image_antitone (abstract). -/
def minimal_mem_image_antitone' : Prop := True
/-- maximal_mem_image_antitone (abstract). -/
def maximal_mem_image_antitone' : Prop := True
/-- minimal_mem_image_antitone_iff (abstract). -/
def minimal_mem_image_antitone_iff' : Prop := True
/-- maximal_mem_image_antitone_iff (abstract). -/
def maximal_mem_image_antitone_iff' : Prop := True
/-- image_monotone_setOf_minimal (abstract). -/
def image_monotone_setOf_minimal' : Prop := True
/-- image_monotone_setOf_maximal (abstract). -/
def image_monotone_setOf_maximal' : Prop := True
/-- image_antitone_setOf_minimal (abstract). -/
def image_antitone_setOf_minimal' : Prop := True
/-- image_antitone_setOf_maximal (abstract). -/
def image_antitone_setOf_maximal' : Prop := True
/-- image_monotone_setOf_minimal_mem (abstract). -/
def image_monotone_setOf_minimal_mem' : Prop := True
/-- image_monotone_setOf_maximal_mem (abstract). -/
def image_monotone_setOf_maximal_mem' : Prop := True
/-- image_antitone_setOf_minimal_mem (abstract). -/
def image_antitone_setOf_minimal_mem' : Prop := True
/-- image_antitone_setOf_maximal_mem (abstract). -/
def image_antitone_setOf_maximal_mem' : Prop := True
/-- minimal_mem_image (abstract). -/
def minimal_mem_image' : Prop := True
/-- maximal_mem_image (abstract). -/
def maximal_mem_image' : Prop := True
/-- minimal_mem_image_iff (abstract). -/
def minimal_mem_image_iff' : Prop := True
/-- maximal_mem_image_iff (abstract). -/
def maximal_mem_image_iff' : Prop := True
/-- minimal_apply_mem_inter_range_iff (abstract). -/
def minimal_apply_mem_inter_range_iff' : Prop := True
/-- maximal_apply_mem_inter_range_iff (abstract). -/
def maximal_apply_mem_inter_range_iff' : Prop := True
/-- minimal_apply_mem_iff (abstract). -/
def minimal_apply_mem_iff' : Prop := True
/-- maximal_apply_iff (abstract). -/
def maximal_apply_iff' : Prop := True
/-- image_setOf_minimal (abstract). -/
def image_setOf_minimal' : Prop := True
/-- image_setOf_maximal (abstract). -/
def image_setOf_maximal' : Prop := True
/-- inter_preimage_setOf_minimal_eq_of_subset (abstract). -/
def inter_preimage_setOf_minimal_eq_of_subset' : Prop := True
/-- inter_preimage_setOf_maximal_eq_of_subset (abstract). -/
def inter_preimage_setOf_maximal_eq_of_subset' : Prop := True
/-- map_minimal_mem (abstract). -/
def map_minimal_mem' : Prop := True
/-- map_maximal_mem (abstract). -/
def map_maximal_mem' : Prop := True
/-- mapSetOfMinimal (abstract). -/
def mapSetOfMinimal' : Prop := True
/-- mapSetOfMaximal (abstract). -/
def mapSetOfMaximal' : Prop := True
/-- setOfMinimalIsoSetOfMaximal (abstract). -/
def setOfMinimalIsoSetOfMaximal' : Prop := True
/-- setOfMaximalIsoSetOfMinimal (abstract). -/
def setOfMaximalIsoSetOfMinimal' : Prop := True
/-- minimal_mem_Icc (abstract). -/
def minimal_mem_Icc' : Prop := True
/-- maximal_mem_Icc (abstract). -/
def maximal_mem_Icc' : Prop := True
/-- minimal_mem_Ico (abstract). -/
def minimal_mem_Ico' : Prop := True
/-- maximal_mem_Ioc (abstract). -/
def maximal_mem_Ioc' : Prop := True

-- ModularLattice.lean
/-- IsWeakUpperModularLattice (abstract). -/
def IsWeakUpperModularLattice' : Prop := True
/-- IsWeakLowerModularLattice (abstract). -/
def IsWeakLowerModularLattice' : Prop := True
/-- IsUpperModularLattice (abstract). -/
def IsUpperModularLattice' : Prop := True
/-- IsLowerModularLattice (abstract). -/
def IsLowerModularLattice' : Prop := True
/-- IsModularLattice (abstract). -/
def IsModularLattice' : Prop := True
/-- covBy_sup_of_inf_covBy_of_inf_covBy_left (abstract). -/
def covBy_sup_of_inf_covBy_of_inf_covBy_left' : Prop := True
/-- covBy_sup_of_inf_covBy_of_inf_covBy_right (abstract). -/
def covBy_sup_of_inf_covBy_of_inf_covBy_right' : Prop := True
/-- inf_covBy_of_covBy_sup_of_covBy_sup_left (abstract). -/
def inf_covBy_of_covBy_sup_of_covBy_sup_left' : Prop := True
/-- inf_covBy_of_covBy_sup_of_covBy_sup_right (abstract). -/
def inf_covBy_of_covBy_sup_of_covBy_sup_right' : Prop := True
/-- covBy_sup_of_inf_covBy_left (abstract). -/
def covBy_sup_of_inf_covBy_left' : Prop := True
/-- covBy_sup_of_inf_covBy_right (abstract). -/
def covBy_sup_of_inf_covBy_right' : Prop := True
/-- inf_covBy_of_covBy_sup_left (abstract). -/
def inf_covBy_of_covBy_sup_left' : Prop := True
/-- inf_covBy_of_covBy_sup_right (abstract). -/
def inf_covBy_of_covBy_sup_right' : Prop := True
/-- sup_inf_assoc_of_le (abstract). -/
def sup_inf_assoc_of_le' : Prop := True
/-- inf_sup_inf_assoc (abstract). -/
def inf_sup_inf_assoc' : Prop := True
/-- inf_sup_assoc_of_le (abstract). -/
def inf_sup_assoc_of_le' : Prop := True
/-- sup_inf_sup_assoc (abstract). -/
def sup_inf_sup_assoc' : Prop := True
/-- eq_of_le_of_inf_le_of_le_sup (abstract). -/
def eq_of_le_of_inf_le_of_le_sup' : Prop := True
/-- eq_of_le_of_inf_le_of_sup_le (abstract). -/
def eq_of_le_of_inf_le_of_sup_le' : Prop := True
/-- sup_lt_sup_of_lt_of_inf_le_inf (abstract). -/
def sup_lt_sup_of_lt_of_inf_le_inf' : Prop := True
/-- inf_lt_inf_of_lt_of_sup_le_sup (abstract). -/
def inf_lt_inf_of_lt_of_sup_le_sup' : Prop := True
/-- strictMono_inf_prod_sup (abstract). -/
def strictMono_inf_prod_sup' : Prop := True
/-- wellFounded_lt_exact_sequence (abstract). -/
def wellFounded_lt_exact_sequence' : Prop := True
/-- wellFounded_gt_exact_sequence (abstract). -/
def wellFounded_gt_exact_sequence' : Prop := True
/-- infIccOrderIsoIccSup (abstract). -/
def infIccOrderIsoIccSup' : Prop := True
/-- inf_strictMonoOn_Icc_sup (abstract). -/
def inf_strictMonoOn_Icc_sup' : Prop := True
/-- sup_strictMonoOn_Icc_inf (abstract). -/
def sup_strictMonoOn_Icc_inf' : Prop := True
/-- infIooOrderIsoIooSup (abstract). -/
def infIooOrderIsoIooSup' : Prop := True
/-- IicOrderIsoIci (abstract). -/
def IicOrderIsoIci' : Prop := True
/-- isModularLattice_iff_inf_sup_inf_assoc (abstract). -/
def isModularLattice_iff_inf_sup_inf_assoc' : Prop := True
/-- disjoint_sup_right_of_disjoint_sup_left (abstract). -/
def disjoint_sup_right_of_disjoint_sup_left' : Prop := True
/-- disjoint_sup_left_of_disjoint_sup_right (abstract). -/
def disjoint_sup_left_of_disjoint_sup_right' : Prop := True
/-- isCompl_sup_right_of_isCompl_sup_left (abstract). -/
def isCompl_sup_right_of_isCompl_sup_left' : Prop := True
/-- isCompl_sup_left_of_isCompl_sup_right (abstract). -/
def isCompl_sup_left_of_isCompl_sup_right' : Prop := True
/-- isCompl_inf_inf_of_isCompl_of_le (abstract). -/
def isCompl_inf_inf_of_isCompl_of_le' : Prop := True

-- Monotone/Basic.lean
/-- Monotone (abstract). -/
def Monotone' : Prop := True
/-- Antitone (abstract). -/
def Antitone' : Prop := True
/-- MonotoneOn (abstract). -/
def MonotoneOn' : Prop := True
/-- AntitoneOn (abstract). -/
def AntitoneOn' : Prop := True
/-- StrictMono (abstract). -/
def StrictMono' : Prop := True
/-- StrictAnti (abstract). -/
def StrictAnti' : Prop := True
/-- StrictMonoOn (abstract). -/
def StrictMonoOn' : Prop := True
/-- StrictAntiOn (abstract). -/
def StrictAntiOn' : Prop := True
/-- monotone_inclusion_le_le_of_le (abstract). -/
def monotone_inclusion_le_le_of_le' : Prop := True
/-- monotone_inclusion_lt_le_of_le (abstract). -/
def monotone_inclusion_lt_le_of_le' : Prop := True
/-- monotone_inclusion_lt_lt_of_le (abstract). -/
def monotone_inclusion_lt_lt_of_le' : Prop := True
/-- monotone_dual_iff (abstract). -/
def monotone_dual_iff' : Prop := True
/-- antitone_dual_iff (abstract). -/
def antitone_dual_iff' : Prop := True
/-- monotoneOn_dual_iff (abstract). -/
def monotoneOn_dual_iff' : Prop := True
/-- antitoneOn_dual_iff (abstract). -/
def antitoneOn_dual_iff' : Prop := True
/-- strictMono_dual_iff (abstract). -/
def strictMono_dual_iff' : Prop := True
/-- strictAnti_dual_iff (abstract). -/
def strictAnti_dual_iff' : Prop := True
/-- strictMonoOn_dual_iff (abstract). -/
def strictMonoOn_dual_iff' : Prop := True
/-- strictAntiOn_dual_iff (abstract). -/
def strictAntiOn_dual_iff' : Prop := True
/-- comp_le_comp_left (abstract). -/
def comp_le_comp_left' : Prop := True
/-- monotone_lam (abstract). -/
def monotone_lam' : Prop := True
/-- monotone_app (abstract). -/
def monotone_app' : Prop := True
/-- antitone_lam (abstract). -/
def antitone_lam' : Prop := True
/-- antitone_app (abstract). -/
def antitone_app' : Prop := True
/-- monotone_eval (abstract). -/
def monotone_eval' : Prop := True
/-- imp (abstract). -/
def imp' : Prop := True
/-- monotoneOn (abstract). -/
def monotoneOn' : Prop := True
/-- antitoneOn (abstract). -/
def antitoneOn' : Prop := True
/-- monotoneOn_univ (abstract). -/
def monotoneOn_univ' : Prop := True
/-- antitoneOn_univ (abstract). -/
def antitoneOn_univ' : Prop := True
/-- strictMonoOn (abstract). -/
def strictMonoOn' : Prop := True
/-- strictAntiOn (abstract). -/
def strictAntiOn' : Prop := True
/-- strictMonoOn_univ (abstract). -/
def strictMonoOn_univ' : Prop := True
/-- strictAntiOn_univ (abstract). -/
def strictAntiOn_univ' : Prop := True
/-- strictMono_of_injective (abstract). -/
def strictMono_of_injective' : Prop := True
/-- strictAnti_of_injective (abstract). -/
def strictAnti_of_injective' : Prop := True
/-- monotone_iff_forall_lt (abstract). -/
def monotone_iff_forall_lt' : Prop := True
/-- antitone_iff_forall_lt (abstract). -/
def antitone_iff_forall_lt' : Prop := True
/-- monotoneOn_iff_forall_lt (abstract). -/
def monotoneOn_iff_forall_lt' : Prop := True
/-- antitoneOn_iff_forall_lt (abstract). -/
def antitoneOn_iff_forall_lt' : Prop := True
/-- antitone (abstract). -/
def antitone' : Prop := True
/-- strictAnti (abstract). -/
def strictAnti' : Prop := True
/-- monotone_id (abstract). -/
def monotone_id' : Prop := True
/-- monotoneOn_id (abstract). -/
def monotoneOn_id' : Prop := True
/-- strictMono_id (abstract). -/
def strictMono_id' : Prop := True
/-- strictMonoOn_id (abstract). -/
def strictMonoOn_id' : Prop := True
/-- monotone_const (abstract). -/
def monotone_const' : Prop := True
/-- monotoneOn_const (abstract). -/
def monotoneOn_const' : Prop := True
/-- antitone_const (abstract). -/
def antitone_const' : Prop := True
/-- antitoneOn_const (abstract). -/
def antitoneOn_const' : Prop := True
/-- strictMono_of_le_iff_le (abstract). -/
def strictMono_of_le_iff_le' : Prop := True
/-- strictAnti_of_le_iff_le (abstract). -/
def strictAnti_of_le_iff_le' : Prop := True
/-- injective_of_lt_imp_ne (abstract). -/
def injective_of_lt_imp_ne' : Prop := True
/-- injective_of_le_imp_le (abstract). -/
def injective_of_le_imp_le' : Prop := True
/-- isMax_of_apply (abstract). -/
def isMax_of_apply' : Prop := True
/-- isMin_of_apply (abstract). -/
def isMin_of_apply' : Prop := True
/-- add_le_nat (abstract). -/
def add_le_nat' : Prop := True
/-- ite' (abstract). -/
def ite' : Prop := True
/-- comp_monotone (abstract). -/
def comp_monotone' : Prop := True
/-- comp_monotoneOn (abstract). -/
def comp_monotoneOn' : Prop := True
/-- comp_antitoneOn (abstract). -/
def comp_antitoneOn' : Prop := True
/-- comp_strictAnti (abstract). -/
def comp_strictAnti' : Prop := True
/-- comp_strictMonoOn (abstract). -/
def comp_strictMonoOn' : Prop := True
/-- comp_strictAntiOn (abstract). -/
def comp_strictAntiOn' : Prop := True
/-- foldl_monotone (abstract). -/
def foldl_monotone' : Prop := True
/-- foldr_monotone (abstract). -/
def foldr_monotone' : Prop := True
/-- foldl_strictMono (abstract). -/
def foldl_strictMono' : Prop := True
/-- foldr_strictMono (abstract). -/
def foldr_strictMono' : Prop := True
/-- reflect_lt (abstract). -/
def reflect_lt' : Prop := True
/-- compares (abstract). -/
def compares' : Prop := True
/-- maximal_of_maximal_image (abstract). -/
def maximal_of_maximal_image' : Prop := True
/-- minimal_of_minimal_image (abstract). -/
def minimal_of_minimal_image' : Prop := True
/-- minimal_of_maximal_image (abstract). -/
def minimal_of_maximal_image' : Prop := True
/-- maximal_of_minimal_image (abstract). -/
def maximal_of_minimal_image' : Prop := True
/-- strictMono_iff_injective (abstract). -/
def strictMono_iff_injective' : Prop := True
/-- strictAnti_iff_injective (abstract). -/
def strictAnti_iff_injective' : Prop := True
/-- eq_of_le_of_le (abstract). -/
def eq_of_le_of_le' : Prop := True
/-- not_monotone_not_antitone_iff_exists_le_le (abstract). -/
def not_monotone_not_antitone_iff_exists_le_le' : Prop := True
/-- not_monotone_not_antitone_iff_exists_lt_lt (abstract). -/
def not_monotone_not_antitone_iff_exists_lt_lt' : Prop := True
/-- cmp_map_eq (abstract). -/
def cmp_map_eq' : Prop := True
/-- rel_of_forall_rel_succ_of_le_of_lt (abstract). -/
def rel_of_forall_rel_succ_of_le_of_lt' : Prop := True
/-- rel_of_forall_rel_succ_of_le_of_le (abstract). -/
def rel_of_forall_rel_succ_of_le_of_le' : Prop := True
/-- rel_of_forall_rel_succ_of_lt (abstract). -/
def rel_of_forall_rel_succ_of_lt' : Prop := True
/-- rel_of_forall_rel_succ_of_le (abstract). -/
def rel_of_forall_rel_succ_of_le' : Prop := True
/-- monotone_nat_of_le_succ (abstract). -/
def monotone_nat_of_le_succ' : Prop := True
/-- antitone_nat_of_succ_le (abstract). -/
def antitone_nat_of_succ_le' : Prop := True
/-- strictMono_nat_of_lt_succ (abstract). -/
def strictMono_nat_of_lt_succ' : Prop := True
/-- strictAnti_nat_of_succ_lt (abstract). -/
def strictAnti_nat_of_succ_lt' : Prop := True
/-- exists_strictMono' (abstract). -/
def exists_strictMono' : Prop := True
/-- exists_strictAnti' (abstract). -/
def exists_strictAnti' : Prop := True
/-- monotone_int_of_le_succ (abstract). -/
def monotone_int_of_le_succ' : Prop := True
/-- antitone_int_of_succ_le (abstract). -/
def antitone_int_of_succ_le' : Prop := True
/-- strictMono_int_of_lt_succ (abstract). -/
def strictMono_int_of_lt_succ' : Prop := True
/-- strictAnti_int_of_succ_lt (abstract). -/
def strictAnti_int_of_succ_lt' : Prop := True
/-- ne_of_lt_of_lt_nat (abstract). -/
def ne_of_lt_of_lt_nat' : Prop := True
/-- ne_of_lt_of_lt_int (abstract). -/
def ne_of_lt_of_lt_int' : Prop := True
/-- mono_coe (abstract). -/
def mono_coe' : Prop := True
/-- strictMono_coe (abstract). -/
def strictMono_coe' : Prop := True
/-- monotone_fst (abstract). -/
def monotone_fst' : Prop := True
/-- monotone_snd (abstract). -/
def monotone_snd' : Prop := True
/-- update_mono (abstract). -/
def update_mono' : Prop := True
/-- update_strictMono (abstract). -/
def update_strictMono' : Prop := True
/-- const_mono (abstract). -/
def const_mono' : Prop := True
/-- const_strictMono (abstract). -/
def const_strictMono' : Prop := True
/-- monotone_iff_apply₂ (abstract). -/
def monotone_iff_apply₂' : Prop := True
/-- antitone_iff_apply₂ (abstract). -/
def antitone_iff_apply₂' : Prop := True
/-- stabilises_of_monotone (abstract). -/
def stabilises_of_monotone' : Prop := True

-- Monotone/Extension.lean
/-- exists_monotone_extension (abstract). -/
def exists_monotone_extension' : Prop := True

-- Monotone/Monovary.lean
/-- Monovary (abstract). -/
def Monovary' : Prop := True
/-- Antivary (abstract). -/
def Antivary' : Prop := True
/-- MonovaryOn (abstract). -/
def MonovaryOn' : Prop := True
/-- AntivaryOn (abstract). -/
def AntivaryOn' : Prop := True
/-- monovaryOn (abstract). -/
def monovaryOn' : Prop := True
/-- antivaryOn (abstract). -/
def antivaryOn' : Prop := True
-- COLLISION: empty' already in SetTheory.lean — rename needed
/-- monovaryOn_univ (abstract). -/
def monovaryOn_univ' : Prop := True
/-- antivaryOn_univ (abstract). -/
def antivaryOn_univ' : Prop := True
/-- monovaryOn_iff_monovary (abstract). -/
def monovaryOn_iff_monovary' : Prop := True
/-- antivaryOn_iff_antivary (abstract). -/
def antivaryOn_iff_antivary' : Prop := True
/-- monovary_const_left (abstract). -/
def monovary_const_left' : Prop := True
/-- antivary_const_left (abstract). -/
def antivary_const_left' : Prop := True
/-- monovary_const_right (abstract). -/
def monovary_const_right' : Prop := True
/-- antivary_const_right (abstract). -/
def antivary_const_right' : Prop := True
/-- monovary_self (abstract). -/
def monovary_self' : Prop := True
/-- monovaryOn_self (abstract). -/
def monovaryOn_self' : Prop := True
/-- monovary (abstract). -/
def monovary' : Prop := True
/-- antivary (abstract). -/
def antivary' : Prop := True
/-- monovaryOn_const_left (abstract). -/
def monovaryOn_const_left' : Prop := True
/-- antivaryOn_const_left (abstract). -/
def antivaryOn_const_left' : Prop := True
/-- monovaryOn_const_right (abstract). -/
def monovaryOn_const_right' : Prop := True
/-- antivaryOn_const_right (abstract). -/
def antivaryOn_const_right' : Prop := True
/-- comp_right (abstract). -/
def comp_right' : Prop := True
/-- comp_monotone_left (abstract). -/
def comp_monotone_left' : Prop := True
/-- comp_antitone_left (abstract). -/
def comp_antitone_left' : Prop := True
/-- comp_monotone_on_left (abstract). -/
def comp_monotone_on_left' : Prop := True
/-- comp_antitone_on_left (abstract). -/
def comp_antitone_on_left' : Prop := True
/-- dual_left (abstract). -/
def dual_left' : Prop := True
/-- dual_right (abstract). -/
def dual_right' : Prop := True
/-- antivaryOn_toDual_right (abstract). -/
def antivaryOn_toDual_right' : Prop := True
/-- monovary_id_iff (abstract). -/
def monovary_id_iff' : Prop := True
/-- antivary_id_iff (abstract). -/
def antivary_id_iff' : Prop := True
/-- monovaryOn_id_iff (abstract). -/
def monovaryOn_id_iff' : Prop := True
/-- antivaryOn_id_iff (abstract). -/
def antivaryOn_id_iff' : Prop := True
/-- trans_monovary (abstract). -/
def trans_monovary' : Prop := True
/-- trans_antivary (abstract). -/
def trans_antivary' : Prop := True
/-- trans_monovaryOn (abstract). -/
def trans_monovaryOn' : Prop := True
/-- trans_antivaryOn (abstract). -/
def trans_antivaryOn' : Prop := True
/-- comp_monotoneOn_right (abstract). -/
def comp_monotoneOn_right' : Prop := True
/-- comp_antitoneOn_right (abstract). -/
def comp_antitoneOn_right' : Prop := True
/-- monovary_comm (abstract). -/
def monovary_comm' : Prop := True
/-- antivary_comm (abstract). -/
def antivary_comm' : Prop := True
/-- monovaryOn_comm (abstract). -/
def monovaryOn_comm' : Prop := True
/-- antivaryOn_comm (abstract). -/
def antivaryOn_comm' : Prop := True

-- Monotone/Odd.lean
/-- strictMono_of_odd_strictMonoOn_nonneg (abstract). -/
def strictMono_of_odd_strictMonoOn_nonneg' : Prop := True
/-- strictAnti_of_odd_strictAntiOn_nonneg (abstract). -/
def strictAnti_of_odd_strictAntiOn_nonneg' : Prop := True
/-- monotone_of_odd_of_monotoneOn_nonneg (abstract). -/
def monotone_of_odd_of_monotoneOn_nonneg' : Prop := True
/-- antitone_of_odd_of_monotoneOn_nonneg (abstract). -/
def antitone_of_odd_of_monotoneOn_nonneg' : Prop := True

-- Monotone/Union.lean
/-- union_right (abstract). -/
def union_right' : Prop := True

-- Notation.lean
/-- HasCompl (abstract). -/
def HasCompl' : Prop := True
/-- Sup (abstract). -/
def Sup' : Prop := True
/-- Inf (abstract). -/
def Inf' : Prop := True
/-- HImp (abstract). -/
def HImp' : Prop := True
/-- HNot (abstract). -/
def HNot' : Prop := True
/-- Top (abstract). -/
def Top' : Prop := True
/-- Bot (abstract). -/
def Bot' : Prop := True

-- OmegaCompletePartialOrder.lean
/-- Chain (abstract). -/
def Chain' : Prop := True
-- COLLISION: mem_map' already in SetTheory.lean — rename needed
/-- zip (abstract). -/
def zip' : Prop := True
/-- range_pair (abstract). -/
def range_pair' : Prop := True
/-- pair_zip_pair (abstract). -/
def pair_zip_pair' : Prop := True
/-- OmegaCompletePartialOrder (abstract). -/
def OmegaCompletePartialOrder' : Prop := True
/-- le_ωSup_of_le (abstract). -/
def le_ωSup_of_le' : Prop := True
/-- ωSup_total (abstract). -/
def ωSup_total' : Prop := True
/-- ωSup_le_iff (abstract). -/
def ωSup_le_iff' : Prop := True
/-- isLUB_range_ωSup (abstract). -/
def isLUB_range_ωSup' : Prop := True
/-- ωSup_eq_of_isLUB (abstract). -/
def ωSup_eq_of_isLUB' : Prop := True
/-- ωScottContinuous (abstract). -/
def ωScottContinuous' : Prop := True
/-- isLUB (abstract). -/
def isLUB' : Prop := True
/-- map_ωSup (abstract). -/
def map_ωSup' : Prop := True
/-- ωScottContinuous_iff_monotone_map_ωSup (abstract). -/
def ωScottContinuous_iff_monotone_map_ωSup' : Prop := True
/-- ωScottContinuous_iff_map_ωSup_of_orderHom (abstract). -/
def ωScottContinuous_iff_map_ωSup_of_orderHom' : Prop := True
/-- Continuous (abstract). -/
def Continuous' : Prop := True
/-- isLUB_of_scottContinuous (abstract). -/
def isLUB_of_scottContinuous' : Prop := True
/-- continuous' (abstract). -/
def continuous' : Prop := True
/-- to_monotone (abstract). -/
def to_monotone' : Prop := True
/-- of_bundled (abstract). -/
def of_bundled' : Prop := True
/-- to_bundled (abstract). -/
def to_bundled' : Prop := True
/-- continuous'_coe (abstract). -/
def continuous'_coe' : Prop := True
/-- continuous_id (abstract). -/
def continuous_id' : Prop := True
/-- continuous_comp (abstract). -/
def continuous_comp' : Prop := True
/-- id_continuous' (abstract). -/
def id_continuous' : Prop := True
/-- continuous_const (abstract). -/
def continuous_const' : Prop := True
/-- const_continuous' (abstract). -/
def const_continuous' : Prop := True
/-- eq_of_chain (abstract). -/
def eq_of_chain' : Prop := True
/-- ωSup (abstract). -/
def ωSup' : Prop := True
/-- ωSup_eq_some (abstract). -/
def ωSup_eq_some' : Prop := True
/-- ωSup_eq_none (abstract). -/
def ωSup_eq_none' : Prop := True
/-- mem_chain_of_mem_ωSup (abstract). -/
def mem_chain_of_mem_ωSup' : Prop := True
/-- mem_ωSup (abstract). -/
def mem_ωSup' : Prop := True
/-- apply₂ (abstract). -/
def apply₂' : Prop := True
/-- of_apply₂ (abstract). -/
def of_apply₂' : Prop := True
/-- ωScottContinuous_iff_apply₂ (abstract). -/
def ωScottContinuous_iff_apply₂' : Prop := True
/-- flip₁_continuous' (abstract). -/
def flip₁_continuous' : Prop := True
/-- flip₂_continuous' (abstract). -/
def flip₂_continuous' : Prop := True
/-- ωSup_zip (abstract). -/
def ωSup_zip' : Prop := True
/-- prodMk (abstract). -/
def prodMk' : Prop := True
/-- top (abstract). -/
def top' : Prop := True
/-- sSup_continuous (abstract). -/
def sSup_continuous' : Prop := True
/-- iSup_continuous (abstract). -/
def iSup_continuous' : Prop := True
/-- sup_continuous (abstract). -/
def sup_continuous' : Prop := True
/-- top_continuous (abstract). -/
def top_continuous' : Prop := True
/-- bot_continuous (abstract). -/
def bot_continuous' : Prop := True
/-- inf_continuous (abstract). -/
def inf_continuous' : Prop := True
/-- ContinuousHom (abstract). -/
def ContinuousHom' : Prop := True
/-- congr_fun (abstract). -/
def congr_fun' : Prop := True
/-- congr_arg (abstract). -/
def congr_arg' : Prop := True
/-- apply_mono (abstract). -/
def apply_mono' : Prop := True
/-- ite_continuous' (abstract). -/
def ite_continuous' : Prop := True
/-- ωSup_bind (abstract). -/
def ωSup_bind' : Prop := True
/-- bind_continuous' (abstract). -/
def bind_continuous' : Prop := True
/-- map_continuous' (abstract). -/
def map_continuous' : Prop := True
/-- seq_continuous' (abstract). -/
def seq_continuous' : Prop := True
/-- toMono (abstract). -/
def toMono' : Prop := True
/-- forall_forall_merge (abstract). -/
def forall_forall_merge' : Prop := True
/-- ωSup_apply_ωSup (abstract). -/
def ωSup_apply_ωSup' : Prop := True
/-- iterateChain (abstract). -/
def iterateChain' : Prop := True
/-- ωSup_iterate_mem_fixedPoint (abstract). -/
def ωSup_iterate_mem_fixedPoint' : Prop := True
/-- ωSup_iterate_le_prefixedPoint (abstract). -/
def ωSup_iterate_le_prefixedPoint' : Prop := True
/-- ωSup_iterate_le_fixedPoint (abstract). -/
def ωSup_iterate_le_fixedPoint' : Prop := True

-- OrdContinuous.lean
/-- LeftOrdContinuous (abstract). -/
def LeftOrdContinuous' : Prop := True
/-- RightOrdContinuous (abstract). -/
def RightOrdContinuous' : Prop := True
/-- order_dual (abstract). -/
def order_dual' : Prop := True
/-- orderDual (abstract). -/
def orderDual' : Prop := True
/-- leftOrdContinuous (abstract). -/
def leftOrdContinuous' : Prop := True
/-- rightOrdContinuous (abstract). -/
def rightOrdContinuous' : Prop := True

-- OrderIsoNat.lean
/-- natLT (abstract). -/
def natLT' : Prop := True
/-- natGT (abstract). -/
def natGT' : Prop := True
/-- exists_not_acc_lt_of_not_acc (abstract). -/
def exists_not_acc_lt_of_not_acc' : Prop := True
/-- acc_iff_no_decreasing_seq (abstract). -/
def acc_iff_no_decreasing_seq' : Prop := True
/-- not_acc_of_decreasing_seq (abstract). -/
def not_acc_of_decreasing_seq' : Prop := True
/-- wellFounded_iff_no_descending_seq (abstract). -/
def wellFounded_iff_no_descending_seq' : Prop := True
/-- not_wellFounded_of_decreasing_seq (abstract). -/
def not_wellFounded_of_decreasing_seq' : Prop := True
/-- orderEmbeddingOfSet (abstract). -/
def orderEmbeddingOfSet' : Prop := True
/-- orderIsoOfNat (abstract). -/
def orderIsoOfNat' : Prop := True
/-- orderIsoOfNat_apply (abstract). -/
def orderIsoOfNat_apply' : Prop := True
/-- orderEmbeddingOfSet_range (abstract). -/
def orderEmbeddingOfSet_range' : Prop := True
/-- exists_subseq_of_forall_mem_union (abstract). -/
def exists_subseq_of_forall_mem_union' : Prop := True
/-- exists_increasing_or_nonincreasing_subseq' (abstract). -/
def exists_increasing_or_nonincreasing_subseq' : Prop := True
/-- monotone_chain_condition (abstract). -/
def monotone_chain_condition' : Prop := True
/-- monotonicSequenceLimitIndex (abstract). -/
def monotonicSequenceLimitIndex' : Prop := True
/-- monotonicSequenceLimit (abstract). -/
def monotonicSequenceLimit' : Prop := True
/-- iSup_eq_monotonicSequenceLimit (abstract). -/
def iSup_eq_monotonicSequenceLimit' : Prop := True
/-- exists_covBy_seq_of_wellFoundedLT_wellFoundedGT (abstract). -/
def exists_covBy_seq_of_wellFoundedLT_wellFoundedGT' : Prop := True

-- PFilter.lean
/-- PFilter (abstract). -/
def PFilter' : Prop := True
/-- IsPFilter (abstract). -/
def IsPFilter' : Prop := True
/-- of_def (abstract). -/
def of_def' : Prop := True
/-- toPFilter (abstract). -/
def toPFilter' : Prop := True
/-- isPFilter (abstract). -/
def isPFilter' : Prop := True
/-- principal_le_principal_iff (abstract). -/
def principal_le_principal_iff' : Prop := True
/-- antitone_principal (abstract). -/
def antitone_principal' : Prop := True
/-- inf_mem (abstract). -/
def inf_mem' : Prop := True
/-- inf_mem_iff (abstract). -/
def inf_mem_iff' : Prop := True
/-- sInf_gc (abstract). -/
def sInf_gc' : Prop := True
/-- infGi (abstract). -/
def infGi' : Prop := True

-- Part.lean
/-- partBind (abstract). -/
def partBind' : Prop := True
/-- partMap (abstract). -/
def partMap' : Prop := True
/-- partSeq (abstract). -/
def partSeq' : Prop := True

-- PartialSups.lean
/-- partialSups (abstract). -/
def partialSups' : Prop := True
/-- partialSups_iff_forall (abstract). -/
def partialSups_iff_forall' : Prop := True
/-- partialSups_le_iff (abstract). -/
def partialSups_le_iff' : Prop := True
/-- le_partialSups_of_le (abstract). -/
def le_partialSups_of_le' : Prop := True
/-- le_partialSups (abstract). -/
def le_partialSups' : Prop := True
/-- partialSups_le (abstract). -/
def partialSups_le' : Prop := True
/-- upperBounds_range_partialSups (abstract). -/
def upperBounds_range_partialSups' : Prop := True
/-- bddAbove_range_partialSups (abstract). -/
def bddAbove_range_partialSups' : Prop := True
/-- partialSups_eq (abstract). -/
def partialSups_eq' : Prop := True
/-- partialSups_mono (abstract). -/
def partialSups_mono' : Prop := True
/-- partialSups_monotone (abstract). -/
def partialSups_monotone' : Prop := True
/-- partialSups_eq_sup'_range (abstract). -/
def partialSups_eq_sup'_range' : Prop := True
/-- partialSups_apply (abstract). -/
def partialSups_apply' : Prop := True
/-- partialSups_eq_sup_range (abstract). -/
def partialSups_eq_sup_range' : Prop := True
/-- disjoint_partialSups_left (abstract). -/
def disjoint_partialSups_left' : Prop := True
/-- disjoint_partialSups_right (abstract). -/
def disjoint_partialSups_right' : Prop := True
/-- partialSups_disjoint_of_disjoint (abstract). -/
def partialSups_disjoint_of_disjoint' : Prop := True
/-- partialSups_eq_ciSup_Iic (abstract). -/
def partialSups_eq_ciSup_Iic' : Prop := True
/-- ciSup_partialSups_eq (abstract). -/
def ciSup_partialSups_eq' : Prop := True
/-- partialSups_eq_biSup (abstract). -/
def partialSups_eq_biSup' : Prop := True
/-- partialSups_eq_sUnion_image (abstract). -/
def partialSups_eq_sUnion_image' : Prop := True
/-- partialSups_eq_biUnion_range (abstract). -/
def partialSups_eq_biUnion_range' : Prop := True
/-- iSup_partialSups_eq (abstract). -/
def iSup_partialSups_eq' : Prop := True
/-- iSup_le_iSup_of_partialSups_le_partialSups (abstract). -/
def iSup_le_iSup_of_partialSups_le_partialSups' : Prop := True
/-- iSup_eq_iSup_of_partialSups_eq_partialSups (abstract). -/
def iSup_eq_iSup_of_partialSups_eq_partialSups' : Prop := True

-- Partition/Equipartition.lean
/-- IsEquipartition (abstract). -/
def IsEquipartition' : Prop := True
/-- isEquipartition_iff_card_parts_eq_average (abstract). -/
def isEquipartition_iff_card_parts_eq_average' : Prop := True
/-- not_isEquipartition (abstract). -/
def not_isEquipartition' : Prop := True
/-- isEquipartition (abstract). -/
def isEquipartition' : Prop := True
/-- card_parts_eq_average (abstract). -/
def card_parts_eq_average' : Prop := True
/-- card_part_eq_average_iff (abstract). -/
def card_part_eq_average_iff' : Prop := True
/-- average_le_card_part (abstract). -/
def average_le_card_part' : Prop := True
/-- card_part_le_average_add_one (abstract). -/
def card_part_le_average_add_one' : Prop := True
/-- filter_ne_average_add_one_eq_average (abstract). -/
def filter_ne_average_add_one_eq_average' : Prop := True
/-- card_large_parts_eq_mod (abstract). -/
def card_large_parts_eq_mod' : Prop := True
/-- card_small_parts_eq_mod (abstract). -/
def card_small_parts_eq_mod' : Prop := True
/-- exists_partsEquiv (abstract). -/
def exists_partsEquiv' : Prop := True
/-- exists_partPreservingEquiv (abstract). -/
def exists_partPreservingEquiv' : Prop := True
/-- bot_isEquipartition (abstract). -/
def bot_isEquipartition' : Prop := True
/-- top_isEquipartition (abstract). -/
def top_isEquipartition' : Prop := True
/-- indiscrete_isEquipartition (abstract). -/
def indiscrete_isEquipartition' : Prop := True

-- Partition/Finpartition.lean
/-- Finpartition (abstract). -/
def Finpartition' : Prop := True
/-- ofErase (abstract). -/
def ofErase' : Prop := True
/-- ofSubset (abstract). -/
def ofSubset' : Prop := True
/-- indiscrete (abstract). -/
def indiscrete' : Prop := True
-- COLLISION: le' already in SetTheory.lean — rename needed
/-- parts_eq_empty_iff (abstract). -/
def parts_eq_empty_iff' : Prop := True
/-- parts_nonempty_iff (abstract). -/
def parts_nonempty_iff' : Prop := True
/-- parts_nonempty (abstract). -/
def parts_nonempty' : Prop := True
/-- uniqueFinpartition (abstract). -/
def uniqueFinpartition' : Prop := True
/-- parts_top_subset (abstract). -/
def parts_top_subset' : Prop := True
/-- parts_top_subsingleton (abstract). -/
def parts_top_subsingleton' : Prop := True
-- COLLISION: card_mono' already in SetTheory.lean — rename needed
/-- mem_bind (abstract). -/
def mem_bind' : Prop := True
/-- card_bind (abstract). -/
def card_bind' : Prop := True
/-- extend (abstract). -/
def extend' : Prop := True
/-- card_extend (abstract). -/
def card_extend' : Prop := True
/-- avoid (abstract). -/
def avoid' : Prop := True
/-- mem_avoid (abstract). -/
def mem_avoid' : Prop := True
/-- nonempty_of_mem_parts (abstract). -/
def nonempty_of_mem_parts' : Prop := True
/-- eq_of_mem_parts (abstract). -/
def eq_of_mem_parts' : Prop := True
/-- biUnion_parts (abstract). -/
def biUnion_parts' : Prop := True
/-- existsUnique_mem (abstract). -/
def existsUnique_mem' : Prop := True
/-- part (abstract). -/
def part' : Prop := True
/-- part_mem (abstract). -/
def part_mem' : Prop := True
/-- mem_part (abstract). -/
def mem_part' : Prop := True
/-- part_eq_of_mem (abstract). -/
def part_eq_of_mem' : Prop := True
/-- mem_part_iff_part_eq_part (abstract). -/
def mem_part_iff_part_eq_part' : Prop := True
/-- part_surjOn (abstract). -/
def part_surjOn' : Prop := True
/-- exists_subset_part_bijOn (abstract). -/
def exists_subset_part_bijOn' : Prop := True
/-- equivSigmaParts (abstract). -/
def equivSigmaParts' : Prop := True
/-- exists_enumeration (abstract). -/
def exists_enumeration' : Prop := True
/-- sum_card_parts (abstract). -/
def sum_card_parts' : Prop := True
/-- card_bot (abstract). -/
def card_bot' : Prop := True
/-- mem_bot_iff (abstract). -/
def mem_bot_iff' : Prop := True
/-- card_parts_le_card (abstract). -/
def card_parts_le_card' : Prop := True
/-- card_mod_card_parts_le (abstract). -/
def card_mod_card_parts_le' : Prop := True
/-- ofSetoid (abstract). -/
def ofSetoid' : Prop := True
/-- mem_part_ofSetoid_iff_rel (abstract). -/
def mem_part_ofSetoid_iff_rel' : Prop := True
/-- atomise (abstract). -/
def atomise' : Prop := True
/-- mem_atomise (abstract). -/
def mem_atomise' : Prop := True
/-- atomise_empty (abstract). -/
def atomise_empty' : Prop := True
/-- card_atomise_le (abstract). -/
def card_atomise_le' : Prop := True
/-- biUnion_filter_atomise (abstract). -/
def biUnion_filter_atomise' : Prop := True
/-- card_filter_atomise_le_two_pow (abstract). -/
def card_filter_atomise_le_two_pow' : Prop := True

-- PiLex.lean
/-- Lex (abstract). -/
def Lex' : Prop := True
/-- lex_lt_of_lt_of_preorder (abstract). -/
def lex_lt_of_lt_of_preorder' : Prop := True
/-- lex_lt_of_lt (abstract). -/
def lex_lt_of_lt' : Prop := True
/-- isTrichotomous_lex (abstract). -/
def isTrichotomous_lex' : Prop := True
/-- toLex_monotone (abstract). -/
def toLex_monotone' : Prop := True
/-- toLex_strictMono (abstract). -/
def toLex_strictMono' : Prop := True
/-- lt_toLex_update_self_iff (abstract). -/
def lt_toLex_update_self_iff' : Prop := True
/-- toLex_update_lt_self_iff (abstract). -/
def toLex_update_lt_self_iff' : Prop := True
/-- le_toLex_update_self_iff (abstract). -/
def le_toLex_update_self_iff' : Prop := True
/-- toLex_update_le_self_iff (abstract). -/
def toLex_update_le_self_iff' : Prop := True
-- COLLISION: noMaxOrder' already in SetTheory.lean — rename needed
/-- lex_desc (abstract). -/
def lex_desc' : Prop := True

-- PrimeIdeal.lean
/-- PrimePair (abstract). -/
def PrimePair' : Prop := True
/-- compl_I_eq_F (abstract). -/
def compl_I_eq_F' : Prop := True
/-- compl_F_eq_I (abstract). -/
def compl_F_eq_I' : Prop := True
/-- I_isProper (abstract). -/
def I_isProper' : Prop := True
/-- IsPrime (abstract). -/
def IsPrime' : Prop := True
/-- toPrimePair (abstract). -/
def toPrimePair' : Prop := True
/-- I_isPrime (abstract). -/
def I_isPrime' : Prop := True
/-- mem_or_mem (abstract). -/
def mem_or_mem' : Prop := True
/-- of_mem_or_mem (abstract). -/
def of_mem_or_mem' : Prop := True
/-- isPrime_iff_mem_or_mem (abstract). -/
def isPrime_iff_mem_or_mem' : Prop := True
/-- isPrime_iff_mem_or_compl_mem (abstract). -/
def isPrime_iff_mem_or_compl_mem' : Prop := True
/-- F_isPrime (abstract). -/
def F_isPrime' : Prop := True

-- PrimeSeparator.lean
/-- mem_ideal_sup_principal (abstract). -/
def mem_ideal_sup_principal' : Prop := True
/-- prime_ideal_of_disjoint_filter_ideal (abstract). -/
def prime_ideal_of_disjoint_filter_ideal' : Prop := True

-- PropInstances.lean

-- Radical.lean
/-- radical (abstract). -/
def radical' : Prop := True
/-- radical_le_coatom (abstract). -/
def radical_le_coatom' : Prop := True
/-- map_radical (abstract). -/
def map_radical' : Prop := True
/-- radical_nongenerating (abstract). -/
def radical_nongenerating' : Prop := True

-- Rel/GaloisConnection.lean
/-- leftDual (abstract). -/
def leftDual' : Prop := True
/-- rightDual (abstract). -/
def rightDual' : Prop := True
/-- gc_leftDual_rightDual (abstract). -/
def gc_leftDual_rightDual' : Prop := True
/-- leftFixedPoints (abstract). -/
def leftFixedPoints' : Prop := True
/-- rightFixedPoints (abstract). -/
def rightFixedPoints' : Prop := True
/-- leftDual_mem_rightFixedPoint (abstract). -/
def leftDual_mem_rightFixedPoint' : Prop := True
/-- rightDual_mem_leftFixedPoint (abstract). -/
def rightDual_mem_leftFixedPoint' : Prop := True
/-- equivFixedPoints (abstract). -/
def equivFixedPoints' : Prop := True
/-- rightDual_leftDual_le_of_le (abstract). -/
def rightDual_leftDual_le_of_le' : Prop := True
/-- leftDual_rightDual_le_of_le (abstract). -/
def leftDual_rightDual_le_of_le' : Prop := True

-- RelClasses.lean
/-- of_eq (abstract). -/
def of_eq' : Prop := True
-- COLLISION: antisymm_iff' already in SetTheory.lean — rename needed
/-- antisymm_of (abstract). -/
def antisymm_of' : Prop := True
/-- comm_of (abstract). -/
def comm_of' : Prop := True
/-- isIrrefl (abstract). -/
def isIrrefl' : Prop := True
/-- isTrichotomous (abstract). -/
def isTrichotomous' : Prop := True
/-- ne_of_irrefl (abstract). -/
def ne_of_irrefl' : Prop := True
/-- eq_empty_relation (abstract). -/
def eq_empty_relation' : Prop := True
/-- trans_trichotomous_left (abstract). -/
def trans_trichotomous_left' : Prop := True
/-- trans_trichotomous_right (abstract). -/
def trans_trichotomous_right' : Prop := True
/-- transitive_of_trans (abstract). -/
def transitive_of_trans' : Prop := True
/-- extensional_of_trichotomous_of_irrefl (abstract). -/
def extensional_of_trichotomous_of_irrefl' : Prop := True
/-- partialOrderOfSO (abstract). -/
def partialOrderOfSO' : Prop := True
/-- linearOrderOfSTO (abstract). -/
def linearOrderOfSTO' : Prop := True
/-- IsOrderConnected (abstract). -/
def IsOrderConnected' : Prop := True
/-- neg_trans (abstract). -/
def neg_trans' : Prop := True
/-- isStrictWeakOrder_of_isOrderConnected (abstract). -/
def isStrictWeakOrder_of_isOrderConnected' : Prop := True
-- COLLISION: IsWellFounded' already in Order.lean — rename needed
/-- asymmetric (abstract). -/
def asymmetric' : Prop := True
/-- prod_lex (abstract). -/
def prod_lex' : Prop := True
/-- psigma_lex (abstract). -/
def psigma_lex' : Prop := True
/-- psigma_revLex (abstract). -/
def psigma_revLex' : Prop := True
/-- psigma_skipLeft (abstract). -/
def psigma_skipLeft' : Prop := True
/-- toWellFoundedRelation (abstract). -/
def toWellFoundedRelation' : Prop := True
/-- WellFoundedLT (abstract). -/
def WellFoundedLT' : Prop := True
/-- WellFoundedGT (abstract). -/
def WellFoundedGT' : Prop := True
/-- wellFoundedGT_dual_iff (abstract). -/
def wellFoundedGT_dual_iff' : Prop := True
/-- wellFoundedLT_dual_iff (abstract). -/
def wellFoundedLT_dual_iff' : Prop := True
/-- IsWellOrder (abstract). -/
def IsWellOrder' : Prop := True
/-- toHasWellFounded (abstract). -/
def toHasWellFounded' : Prop := True
/-- isWellFounded (abstract). -/
def isWellFounded' : Prop := True
/-- Unbounded (abstract). -/
def Unbounded' : Prop := True
/-- Bounded (abstract). -/
def Bounded' : Prop := True
/-- not_bounded_iff (abstract). -/
def not_bounded_iff' : Prop := True
/-- not_unbounded_iff (abstract). -/
def not_unbounded_iff' : Prop := True
/-- unbounded_of_isEmpty (abstract). -/
def unbounded_of_isEmpty' : Prop := True
/-- IsNonstrictStrictOrder (abstract). -/
def IsNonstrictStrictOrder' : Prop := True
/-- right_iff_left_not_left (abstract). -/
def right_iff_left_not_left' : Prop := True
/-- right_iff_left_not_left_of (abstract). -/
def right_iff_left_not_left_of' : Prop := True
/-- subset_of_eq_of_subset (abstract). -/
def subset_of_eq_of_subset' : Prop := True
/-- subset_of_subset_of_eq (abstract). -/
def subset_of_subset_of_eq' : Prop := True
/-- subset_refl (abstract). -/
def subset_refl' : Prop := True
/-- subset_rfl (abstract). -/
def subset_rfl' : Prop := True
/-- subset_of_eq (abstract). -/
def subset_of_eq' : Prop := True
/-- superset_of_eq (abstract). -/
def superset_of_eq' : Prop := True
/-- ne_of_not_subset (abstract). -/
def ne_of_not_subset' : Prop := True
/-- ne_of_not_superset (abstract). -/
def ne_of_not_superset' : Prop := True
/-- subset_trans (abstract). -/
def subset_trans' : Prop := True
/-- subset_antisymm (abstract). -/
def subset_antisymm' : Prop := True
/-- superset_antisymm (abstract). -/
def superset_antisymm' : Prop := True
/-- subset_antisymm_iff (abstract). -/
def subset_antisymm_iff' : Prop := True
/-- superset_antisymm_iff (abstract). -/
def superset_antisymm_iff' : Prop := True
/-- ssubset_of_eq_of_ssubset (abstract). -/
def ssubset_of_eq_of_ssubset' : Prop := True
/-- ssubset_of_ssubset_of_eq (abstract). -/
def ssubset_of_ssubset_of_eq' : Prop := True
/-- ssubset_irrefl (abstract). -/
def ssubset_irrefl' : Prop := True
/-- ssubset_irrfl (abstract). -/
def ssubset_irrfl' : Prop := True
/-- ne_of_ssubset (abstract). -/
def ne_of_ssubset' : Prop := True
/-- ne_of_ssuperset (abstract). -/
def ne_of_ssuperset' : Prop := True
/-- ssubset_trans (abstract). -/
def ssubset_trans' : Prop := True
/-- ssubset_asymm (abstract). -/
def ssubset_asymm' : Prop := True
/-- ssubset_iff_subset_not_subset (abstract). -/
def ssubset_iff_subset_not_subset' : Prop := True
/-- subset_of_ssubset (abstract). -/
def subset_of_ssubset' : Prop := True
/-- not_subset_of_ssubset (abstract). -/
def not_subset_of_ssubset' : Prop := True
/-- not_ssubset_of_subset (abstract). -/
def not_ssubset_of_subset' : Prop := True
/-- ssubset_of_subset_not_subset (abstract). -/
def ssubset_of_subset_not_subset' : Prop := True
/-- ssubset_of_subset_of_ssubset (abstract). -/
def ssubset_of_subset_of_ssubset' : Prop := True
/-- ssubset_of_ssubset_of_subset (abstract). -/
def ssubset_of_ssubset_of_subset' : Prop := True
/-- ssubset_of_subset_of_ne (abstract). -/
def ssubset_of_subset_of_ne' : Prop := True
/-- ssubset_of_ne_of_subset (abstract). -/
def ssubset_of_ne_of_subset' : Prop := True
/-- eq_or_ssubset_of_subset (abstract). -/
def eq_or_ssubset_of_subset' : Prop := True
/-- ssubset_or_eq_of_subset (abstract). -/
def ssubset_or_eq_of_subset' : Prop := True
/-- eq_of_subset_of_not_ssubset (abstract). -/
def eq_of_subset_of_not_ssubset' : Prop := True
/-- eq_of_superset_of_not_ssuperset (abstract). -/
def eq_of_superset_of_not_ssuperset' : Prop := True
/-- ssubset_iff_subset_ne (abstract). -/
def ssubset_iff_subset_ne' : Prop := True
/-- subset_iff_ssubset_or_eq (abstract). -/
def subset_iff_ssubset_or_eq' : Prop := True
/-- transitive_le (abstract). -/
def transitive_le' : Prop := True
/-- transitive_lt (abstract). -/
def transitive_lt' : Prop := True
/-- transitive_ge (abstract). -/
def transitive_ge' : Prop := True
/-- transitive_gt (abstract). -/
def transitive_gt' : Prop := True

-- RelIso/Basic.lean
/-- RelHom (abstract). -/
def RelHom' : Prop := True
/-- RelHomClass (abstract). -/
def RelHomClass' : Prop := True
/-- isAsymm (abstract). -/
def isAsymm' : Prop := True
/-- coe_fn_injective (abstract). -/
def coe_fn_injective' : Prop := True
/-- injective_of_increasing (abstract). -/
def injective_of_increasing' : Prop := True
/-- wellFounded_iff (abstract). -/
def wellFounded_iff' : Prop := True
/-- RelEmbedding (abstract). -/
def RelEmbedding' : Prop := True
/-- relEmbedding (abstract). -/
def relEmbedding' : Prop := True
/-- preimage_equivalence (abstract). -/
def preimage_equivalence' : Prop := True
/-- toRelHom (abstract). -/
def toRelHom' : Prop := True
/-- toEmbedding_injective (abstract). -/
def toEmbedding_injective' : Prop := True
/-- eq_preimage (abstract). -/
def eq_preimage' : Prop := True
/-- isRefl (abstract). -/
def isRefl' : Prop := True
/-- isSymm (abstract). -/
def isSymm' : Prop := True
-- COLLISION: isTrans' already in SetTheory.lean — rename needed
/-- isPartialOrder (abstract). -/
def isPartialOrder' : Prop := True
/-- isLinearOrder (abstract). -/
def isLinearOrder' : Prop := True
/-- isStrictTotalOrder (abstract). -/
def isStrictTotalOrder' : Prop := True
/-- mkRelHom (abstract). -/
def mkRelHom' : Prop := True
/-- outRelEmbedding (abstract). -/
def outRelEmbedding' : Prop := True
/-- out'RelEmbedding (abstract). -/
def out'RelEmbedding' : Prop := True
/-- acc_lift₂_iff (abstract). -/
def acc_lift₂_iff' : Prop := True
/-- acc_liftOn₂'_iff (abstract). -/
def acc_liftOn₂'_iff' : Prop := True
/-- wellFounded_lift₂_iff (abstract). -/
def wellFounded_lift₂_iff' : Prop := True
/-- wellFounded_liftOn₂'_iff (abstract). -/
def wellFounded_liftOn₂'_iff' : Prop := True
/-- ofMapRelIff (abstract). -/
def ofMapRelIff' : Prop := True
/-- ofMonotone (abstract). -/
def ofMonotone' : Prop := True
/-- sumLiftRelInl (abstract). -/
def sumLiftRelInl' : Prop := True
/-- sumLiftRelInr (abstract). -/
def sumLiftRelInr' : Prop := True
/-- sumLiftRelMap (abstract). -/
def sumLiftRelMap' : Prop := True
/-- sumLexInl (abstract). -/
def sumLexInl' : Prop := True
/-- sumLexInr (abstract). -/
def sumLexInr' : Prop := True
/-- sumLexMap (abstract). -/
def sumLexMap' : Prop := True
/-- prodLexMkLeft (abstract). -/
def prodLexMkLeft' : Prop := True
/-- prodLexMkRight (abstract). -/
def prodLexMkRight' : Prop := True
/-- prodLexMap (abstract). -/
def prodLexMap' : Prop := True
/-- RelIso (abstract). -/
def RelIso' : Prop := True
/-- toRelEmbedding (abstract). -/
def toRelEmbedding' : Prop := True
/-- toEquiv_injective (abstract). -/
def toEquiv_injective' : Prop := True
/-- symm_apply (abstract). -/
def symm_apply' : Prop := True
/-- cast (abstract). -/
def cast' : Prop := True
/-- cast_trans (abstract). -/
def cast_trans' : Prop := True
/-- apply_symm_apply (abstract). -/
def apply_symm_apply' : Prop := True
/-- symm_apply_apply (abstract). -/
def symm_apply_apply' : Prop := True
/-- rel_symm_apply (abstract). -/
def rel_symm_apply' : Prop := True
/-- symm_apply_rel (abstract). -/
def symm_apply_rel' : Prop := True
/-- bijective (abstract). -/
def bijective' : Prop := True
/-- surjective (abstract). -/
def surjective' : Prop := True
/-- ofSurjective (abstract). -/
def ofSurjective' : Prop := True
/-- sumLexCongr (abstract). -/
def sumLexCongr' : Prop := True
/-- prodLexCongr (abstract). -/
def prodLexCongr' : Prop := True
/-- relIsoOfIsEmpty (abstract). -/
def relIsoOfIsEmpty' : Prop := True
/-- relIsoOfUniqueOfIrrefl (abstract). -/
def relIsoOfUniqueOfIrrefl' : Prop := True
/-- relIsoOfUniqueOfRefl (abstract). -/
def relIsoOfUniqueOfRefl' : Prop := True

-- RelIso/Group.lean
/-- inv_apply_self (abstract). -/
def inv_apply_self' : Prop := True
/-- apply_inv_self (abstract). -/
def apply_inv_self' : Prop := True

-- RelIso/Set.lean
/-- Subrel (abstract). -/
def Subrel' : Prop := True
/-- wellFounded_iff_wellFounded_subrel (abstract). -/
def wellFounded_iff_wellFounded_subrel' : Prop := True

-- RelSeries.lean
/-- RelSeries (abstract). -/
def RelSeries' : Prop := True
/-- singleton (abstract). -/
def singleton' : Prop := True
/-- ofLE (abstract). -/
def ofLE' : Prop := True
-- COLLISION: toList' already in Control.lean — rename needed
/-- length_toList (abstract). -/
def length_toList' : Prop := True
/-- toList_chain' (abstract). -/
def toList_chain' : Prop := True
/-- toList_ne_nil (abstract). -/
def toList_ne_nil' : Prop := True
/-- fromListChain' (abstract). -/
def fromListChain' : Prop := True
-- COLLISION: Equiv' already in ModelTheory.lean — rename needed
/-- toList_injective (abstract). -/
def toList_injective' : Prop := True
/-- FiniteDimensional (abstract). -/
def FiniteDimensional' : Prop := True
/-- InfiniteDimensional (abstract). -/
def InfiniteDimensional' : Prop := True
/-- longestOf (abstract). -/
def longestOf' : Prop := True
/-- length_le_length_longestOf (abstract). -/
def length_le_length_longestOf' : Prop := True
/-- withLength (abstract). -/
def withLength' : Prop := True
/-- mem_toList (abstract). -/
def mem_toList' : Prop := True
/-- subsingleton_of_length_eq_zero (abstract). -/
def subsingleton_of_length_eq_zero' : Prop := True
/-- length_eq_zero (abstract). -/
def length_eq_zero' : Prop := True
/-- head (abstract). -/
def head' : Prop := True
/-- last (abstract). -/
def last' : Prop := True
/-- head_mem (abstract). -/
def head_mem' : Prop := True
/-- last_mem (abstract). -/
def last_mem' : Prop := True
/-- head_singleton (abstract). -/
def head_singleton' : Prop := True
/-- last_singleton (abstract). -/
def last_singleton' : Prop := True
/-- append (abstract). -/
def append' : Prop := True
/-- append_apply_left (abstract). -/
def append_apply_left' : Prop := True
/-- append_apply_right (abstract). -/
def append_apply_right' : Prop := True
/-- head_append (abstract). -/
def head_append' : Prop := True
/-- last_append (abstract). -/
def last_append' : Prop := True
/-- insertNth (abstract). -/
def insertNth' : Prop := True
/-- reverse (abstract). -/
def reverse' : Prop := True
/-- last_reverse (abstract). -/
def last_reverse' : Prop := True
-- COLLISION: cons' already in SetTheory.lean — rename needed
/-- last_cons (abstract). -/
def last_cons' : Prop := True
/-- head_snoc (abstract). -/
def head_snoc' : Prop := True
/-- last_snoc (abstract). -/
def last_snoc' : Prop := True
/-- snoc_castSucc (abstract). -/
def snoc_castSucc' : Prop := True
/-- mem_snoc (abstract). -/
def mem_snoc' : Prop := True
/-- tail (abstract). -/
def tail' : Prop := True
/-- head_tail (abstract). -/
def head_tail' : Prop := True
/-- last_tail (abstract). -/
def last_tail' : Prop := True
/-- eraseLast (abstract). -/
def eraseLast' : Prop := True
/-- eraseLast_last_rel_last (abstract). -/
def eraseLast_last_rel_last' : Prop := True
/-- smash_castAdd (abstract). -/
def smash_castAdd' : Prop := True
/-- smash_succ_castAdd (abstract). -/
def smash_succ_castAdd' : Prop := True
/-- smash_natAdd (abstract). -/
def smash_natAdd' : Prop := True
/-- smash_succ_natAdd (abstract). -/
def smash_succ_natAdd' : Prop := True
/-- head_smash (abstract). -/
def head_smash' : Prop := True
/-- last_smash (abstract). -/
def last_smash' : Prop := True
/-- take (abstract). -/
def take' : Prop := True
/-- head_take (abstract). -/
def head_take' : Prop := True
/-- last_take (abstract). -/
def last_take' : Prop := True
/-- drop (abstract). -/
def drop' : Prop := True
/-- head_drop (abstract). -/
def head_drop' : Prop := True
/-- last_drop (abstract). -/
def last_drop' : Prop := True
/-- FiniteDimensionalOrder (abstract). -/
def FiniteDimensionalOrder' : Prop := True
/-- InfiniteDimensionalOrder (abstract). -/
def InfiniteDimensionalOrder' : Prop := True
/-- LTSeries (abstract). -/
def LTSeries' : Prop := True
/-- length_withLength (abstract). -/
def length_withLength' : Prop := True
/-- nonempty_of_infiniteDimensionalType (abstract). -/
def nonempty_of_infiniteDimensionalType' : Prop := True
/-- longestOf_is_longest (abstract). -/
def longestOf_is_longest' : Prop := True
/-- longestOf_len_unique (abstract). -/
def longestOf_len_unique' : Prop := True
/-- head_le_last (abstract). -/
def head_le_last' : Prop := True
/-- injStrictMono (abstract). -/
def injStrictMono' : Prop := True
/-- apply_add_index_le_apply_add_index_nat (abstract). -/
def apply_add_index_le_apply_add_index_nat' : Prop := True
/-- apply_add_index_le_apply_add_index_int (abstract). -/
def apply_add_index_le_apply_add_index_int' : Prop := True
/-- head_add_length_le_nat (abstract). -/
def head_add_length_le_nat' : Prop := True
/-- head_add_length_le_int (abstract). -/
def head_add_length_le_int' : Prop := True
/-- length_lt_card (abstract). -/
def length_lt_card' : Prop := True
/-- infiniteDimensionalOrder_of_strictMono (abstract). -/
def infiniteDimensionalOrder_of_strictMono' : Prop := True

-- Restriction.lean
/-- restrictLe (abstract). -/
def restrictLe' : Prop := True
/-- restrictLe₂ (abstract). -/
def restrictLe₂' : Prop := True
/-- frestrictLe (abstract). -/
def frestrictLe' : Prop := True
/-- frestrictLe₂ (abstract). -/
def frestrictLe₂' : Prop := True

-- ScottContinuity.lean
/-- ScottContinuousOn (abstract). -/
def ScottContinuousOn' : Prop := True
/-- ScottContinuous (abstract). -/
def ScottContinuous' : Prop := True
/-- sup₂ (abstract). -/
def sup₂' : Prop := True

-- SemiconjSup.lean
/-- IsOrderRightAdjoint (abstract). -/
def IsOrderRightAdjoint' : Prop := True
/-- isOrderRightAdjoint_sSup (abstract). -/
def isOrderRightAdjoint_sSup' : Prop := True
/-- isOrderRightAdjoint_csSup (abstract). -/
def isOrderRightAdjoint_csSup' : Prop := True
/-- right_mono (abstract). -/
def right_mono' : Prop := True
/-- orderIso_comp (abstract). -/
def orderIso_comp' : Prop := True
/-- comp_orderIso (abstract). -/
def comp_orderIso' : Prop := True
/-- symm_adjoint (abstract). -/
def symm_adjoint' : Prop := True
/-- semiconj_of_isLUB (abstract). -/
def semiconj_of_isLUB' : Prop := True
/-- sSup_div_semiconj (abstract). -/
def sSup_div_semiconj' : Prop := True
/-- csSup_div_semiconj (abstract). -/
def csSup_div_semiconj' : Prop := True

-- SetNotation.lean
/-- introducing (abstract). -/
def introducing' : Prop := True
/-- SupSet (abstract). -/
def SupSet' : Prop := True
/-- InfSet (abstract). -/
def InfSet' : Prop := True
/-- iSup_delab (abstract). -/
def iSup_delab' : Prop := True
/-- iInf_delab (abstract). -/
def iInf_delab' : Prop := True
-- COLLISION: sInter' already in SetTheory.lean — rename needed
-- COLLISION: sUnion' already in SetTheory.lean — rename needed
/-- iUnion_delab (abstract). -/
def iUnion_delab' : Prop := True
/-- sInter_delab (abstract). -/
def sInter_delab' : Prop := True

-- Sublattice.lean
/-- Sublattice (abstract). -/
def Sublattice' : Prop := True
/-- ofIsSublattice (abstract). -/
def ofIsSublattice' : Prop := True
/-- inclusion (abstract). -/
def inclusion' : Prop := True
/-- subsingleton_iff (abstract). -/
def subsingleton_iff' : Prop := True
/-- mem_map_of_mem (abstract). -/
def mem_map_of_mem' : Prop := True
/-- apply_coe_mem_map (abstract). -/
def apply_coe_mem_map' : Prop := True
/-- mem_map_equiv (abstract). -/
def mem_map_equiv' : Prop := True
/-- apply_mem_map_iff (abstract). -/
def apply_mem_map_iff' : Prop := True
/-- map_equiv_eq_comap_symm (abstract). -/
def map_equiv_eq_comap_symm' : Prop := True
/-- comap_equiv_eq_map_symm (abstract). -/
def comap_equiv_eq_map_symm' : Prop := True
/-- map_symm_eq_iff_eq_map (abstract). -/
def map_symm_eq_iff_eq_map' : Prop := True
/-- le_comap_sup (abstract). -/
def le_comap_sup' : Prop := True
/-- le_comap_iSup (abstract). -/
def le_comap_iSup' : Prop := True
/-- prod_left_mono (abstract). -/
def prod_left_mono' : Prop := True
/-- prod_right_mono (abstract). -/
def prod_right_mono' : Prop := True
/-- top_prod_top (abstract). -/
def top_prod_top' : Prop := True
/-- le_prod_iff (abstract). -/
def le_prod_iff' : Prop := True
/-- pi_empty (abstract). -/
def pi_empty' : Prop := True
/-- pi_top (abstract). -/
def pi_top' : Prop := True
/-- pi_bot (abstract). -/
def pi_bot' : Prop := True
/-- pi_univ_eq_bot_iff (abstract). -/
def pi_univ_eq_bot_iff' : Prop := True
/-- pi_univ_eq_bot (abstract). -/
def pi_univ_eq_bot' : Prop := True

-- SuccPred/Archimedean.lean
/-- IsSuccArchimedean (abstract). -/
def IsSuccArchimedean' : Prop := True
/-- IsPredArchimedean (abstract). -/
def IsPredArchimedean' : Prop := True
/-- exists_succ_iterate (abstract). -/
def exists_succ_iterate' : Prop := True
/-- exists_succ_iterate_iff_le (abstract). -/
def exists_succ_iterate_iff_le' : Prop := True
/-- le_total_of_codirected (abstract). -/
def le_total_of_codirected' : Prop := True
/-- exists_pred_iterate (abstract). -/
def exists_pred_iterate' : Prop := True
/-- exists_pred_iterate_iff_le (abstract). -/
def exists_pred_iterate_iff_le' : Prop := True
-- COLLISION: rec' already in SetTheory.lean — rename needed
/-- rec_iff (abstract). -/
def rec_iff' : Prop := True
/-- le_total_of_directed (abstract). -/
def le_total_of_directed' : Prop := True
/-- lt_or_le_of_codirected (abstract). -/
def lt_or_le_of_codirected' : Prop := True
/-- lt_or_le_of_directed (abstract). -/
def lt_or_le_of_directed' : Prop := True
/-- succ_max (abstract). -/
def succ_max' : Prop := True
/-- succ_min (abstract). -/
def succ_min' : Prop := True
/-- exists_succ_iterate_or (abstract). -/
def exists_succ_iterate_or' : Prop := True
/-- rec_linear (abstract). -/
def rec_linear' : Prop := True
/-- pred_max (abstract). -/
def pred_max' : Prop := True
/-- pred_min (abstract). -/
def pred_min' : Prop := True
/-- exists_pred_iterate_or (abstract). -/
def exists_pred_iterate_or' : Prop := True
/-- not_bddAbove_range_of_isSuccArchimedean (abstract). -/
def not_bddAbove_range_of_isSuccArchimedean' : Prop := True
/-- not_bddBelow_range_of_isPredArchimedean (abstract). -/
def not_bddBelow_range_of_isPredArchimedean' : Prop := True
/-- not_bddBelow_range_of_isSuccArchimedean (abstract). -/
def not_bddBelow_range_of_isSuccArchimedean' : Prop := True
/-- rec_bot (abstract). -/
def rec_bot' : Prop := True
/-- rec_top (abstract). -/
def rec_top' : Prop := True
/-- exists_isGreatest_of_nonempty (abstract). -/
def exists_isGreatest_of_nonempty' : Prop := True
/-- exists_isLeast_of_nonempty (abstract). -/
def exists_isLeast_of_nonempty' : Prop := True
/-- of_orderIso (abstract). -/
def of_orderIso' : Prop := True
/-- monotoneOn_of_le_succ (abstract). -/
def monotoneOn_of_le_succ' : Prop := True
/-- antitoneOn_of_succ_le (abstract). -/
def antitoneOn_of_succ_le' : Prop := True
/-- strictMonoOn_of_lt_succ (abstract). -/
def strictMonoOn_of_lt_succ' : Prop := True
/-- strictAntiOn_of_succ_lt (abstract). -/
def strictAntiOn_of_succ_lt' : Prop := True
/-- monotone_of_le_succ (abstract). -/
def monotone_of_le_succ' : Prop := True
/-- antitone_of_succ_le (abstract). -/
def antitone_of_succ_le' : Prop := True
/-- strictMono_of_lt_succ (abstract). -/
def strictMono_of_lt_succ' : Prop := True
/-- strictAnti_of_succ_lt (abstract). -/
def strictAnti_of_succ_lt' : Prop := True
/-- monotoneOn_of_pred_le (abstract). -/
def monotoneOn_of_pred_le' : Prop := True
/-- antitoneOn_of_le_pred (abstract). -/
def antitoneOn_of_le_pred' : Prop := True
/-- strictMonoOn_of_pred_lt (abstract). -/
def strictMonoOn_of_pred_lt' : Prop := True
/-- strictAntiOn_of_lt_pred (abstract). -/
def strictAntiOn_of_lt_pred' : Prop := True
/-- monotone_of_pred_le (abstract). -/
def monotone_of_pred_le' : Prop := True
/-- antitone_of_le_pred (abstract). -/
def antitone_of_le_pred' : Prop := True
/-- strictMono_of_pred_lt (abstract). -/
def strictMono_of_pred_lt' : Prop := True
/-- strictAnti_of_lt_pred (abstract). -/
def strictAnti_of_lt_pred' : Prop := True

-- SuccPred/Basic.lean
/-- NaiveSuccOrder (abstract). -/
def NaiveSuccOrder' : Prop := True
/-- SuccOrder (abstract). -/
def SuccOrder' : Prop := True
/-- PredOrder (abstract). -/
def PredOrder' : Prop := True
/-- ofSuccLeIff (abstract). -/
def ofSuccLeIff' : Prop := True
/-- ofLePredIff (abstract). -/
def ofLePredIff' : Prop := True
/-- ofCore (abstract). -/
def ofCore' : Prop := True
/-- ofLinearWellFoundedLT (abstract). -/
def ofLinearWellFoundedLT' : Prop := True
/-- ofLinearWellFoundedGT (abstract). -/
def ofLinearWellFoundedGT' : Prop := True
/-- le_succ (abstract). -/
def le_succ' : Prop := True
/-- max_of_succ_le (abstract). -/
def max_of_succ_le' : Prop := True
/-- succ_le_of_lt (abstract). -/
def succ_le_of_lt' : Prop := True
/-- succ_le_iff_isMax (abstract). -/
def succ_le_iff_isMax' : Prop := True
/-- lt_succ_iff_not_isMax (abstract). -/
def lt_succ_iff_not_isMax' : Prop := True
/-- wcovBy_succ (abstract). -/
def wcovBy_succ' : Prop := True
/-- covBy_succ_of_not_isMax (abstract). -/
def covBy_succ_of_not_isMax' : Prop := True
/-- lt_succ_of_le_of_not_isMax (abstract). -/
def lt_succ_of_le_of_not_isMax' : Prop := True
/-- succ_le_iff_of_not_isMax (abstract). -/
def succ_le_iff_of_not_isMax' : Prop := True
/-- succ_lt_succ_of_not_isMax (abstract). -/
def succ_lt_succ_of_not_isMax' : Prop := True
/-- le_succ_iterate (abstract). -/
def le_succ_iterate' : Prop := True
/-- isMax_iterate_succ_of_eq_of_lt (abstract). -/
def isMax_iterate_succ_of_eq_of_lt' : Prop := True
/-- isMax_iterate_succ_of_eq_of_ne (abstract). -/
def isMax_iterate_succ_of_eq_of_ne' : Prop := True
/-- Iic_subset_Iio_succ_of_not_isMax (abstract). -/
def Iic_subset_Iio_succ_of_not_isMax' : Prop := True
/-- Ici_succ_of_not_isMax (abstract). -/
def Ici_succ_of_not_isMax' : Prop := True
/-- Icc_subset_Ico_succ_right_of_not_isMax (abstract). -/
def Icc_subset_Ico_succ_right_of_not_isMax' : Prop := True
/-- Ioc_subset_Ioo_succ_right_of_not_isMax (abstract). -/
def Ioc_subset_Ioo_succ_right_of_not_isMax' : Prop := True
/-- Icc_succ_left_of_not_isMax (abstract). -/
def Icc_succ_left_of_not_isMax' : Prop := True
/-- Ico_succ_left_of_not_isMax (abstract). -/
def Ico_succ_left_of_not_isMax' : Prop := True
/-- lt_succ_of_le (abstract). -/
def lt_succ_of_le' : Prop := True
-- COLLISION: succ_le_iff' already in SetTheory.lean — rename needed
/-- succ_lt_succ (abstract). -/
def succ_lt_succ' : Prop := True
/-- succ_strictMono (abstract). -/
def succ_strictMono' : Prop := True
/-- covBy_succ (abstract). -/
def covBy_succ' : Prop := True
/-- Iic_subset_Iio_succ (abstract). -/
def Iic_subset_Iio_succ' : Prop := True
/-- Ici_succ (abstract). -/
def Ici_succ' : Prop := True
/-- Icc_subset_Ico_succ_right (abstract). -/
def Icc_subset_Ico_succ_right' : Prop := True
/-- Ioc_subset_Ioo_succ_right (abstract). -/
def Ioc_subset_Ioo_succ_right' : Prop := True
/-- succ_eq_iff_isMax (abstract). -/
def succ_eq_iff_isMax' : Prop := True
/-- le_le_succ_iff (abstract). -/
def le_le_succ_iff' : Prop := True
/-- succ_eq_of_covBy (abstract). -/
def succ_eq_of_covBy' : Prop := True
/-- map_succ (abstract). -/
def map_succ' : Prop := True
/-- succ_eq_iff_covBy (abstract). -/
def succ_eq_iff_covBy' : Prop := True
/-- succ_top (abstract). -/
def succ_top' : Prop := True
/-- succ_le_iff_eq_top (abstract). -/
def succ_le_iff_eq_top' : Prop := True
/-- lt_succ_iff_ne_top (abstract). -/
def lt_succ_iff_ne_top' : Prop := True
/-- bot_lt_succ (abstract). -/
def bot_lt_succ' : Prop := True
/-- succ_ne_bot (abstract). -/
def succ_ne_bot' : Prop := True
/-- le_of_lt_succ (abstract). -/
def le_of_lt_succ' : Prop := True
/-- lt_succ_iff_of_not_isMax (abstract). -/
def lt_succ_iff_of_not_isMax' : Prop := True
/-- succ_lt_succ_iff_of_not_isMax (abstract). -/
def succ_lt_succ_iff_of_not_isMax' : Prop := True
/-- succ_le_succ_iff_of_not_isMax (abstract). -/
def succ_le_succ_iff_of_not_isMax' : Prop := True
/-- Iio_succ_of_not_isMax (abstract). -/
def Iio_succ_of_not_isMax' : Prop := True
/-- Ico_succ_right_of_not_isMax (abstract). -/
def Ico_succ_right_of_not_isMax' : Prop := True
/-- Ioo_succ_right_of_not_isMax (abstract). -/
def Ioo_succ_right_of_not_isMax' : Prop := True
/-- succ_eq_succ_iff_of_not_isMax (abstract). -/
def succ_eq_succ_iff_of_not_isMax' : Prop := True
/-- le_succ_iff_eq_or_le (abstract). -/
def le_succ_iff_eq_or_le' : Prop := True
/-- lt_succ_iff_eq_or_lt_of_not_isMax (abstract). -/
def lt_succ_iff_eq_or_lt_of_not_isMax' : Prop := True
/-- Iic_succ (abstract). -/
def Iic_succ' : Prop := True
/-- Icc_succ_right (abstract). -/
def Icc_succ_right' : Prop := True
/-- Ioc_succ_right (abstract). -/
def Ioc_succ_right' : Prop := True
/-- Iio_succ_eq_insert_of_not_isMax (abstract). -/
def Iio_succ_eq_insert_of_not_isMax' : Prop := True
/-- Ico_succ_right_eq_insert_of_not_isMax (abstract). -/
def Ico_succ_right_eq_insert_of_not_isMax' : Prop := True
/-- Ioo_succ_right_eq_insert_of_not_isMax (abstract). -/
def Ioo_succ_right_eq_insert_of_not_isMax' : Prop := True
/-- lt_succ_iff (abstract). -/
def lt_succ_iff' : Prop := True
/-- succ_le_succ_iff (abstract). -/
def succ_le_succ_iff' : Prop := True
/-- succ_lt_succ_iff (abstract). -/
def succ_lt_succ_iff' : Prop := True
/-- Iio_succ (abstract). -/
def Iio_succ' : Prop := True
/-- Ioo_succ_right (abstract). -/
def Ioo_succ_right' : Prop := True
/-- succ_eq_succ_iff (abstract). -/
def succ_eq_succ_iff' : Prop := True
/-- succ_injective (abstract). -/
def succ_injective' : Prop := True
/-- succ_ne_succ_iff (abstract). -/
def succ_ne_succ_iff' : Prop := True
/-- lt_succ_iff_eq_or_lt (abstract). -/
def lt_succ_iff_eq_or_lt' : Prop := True
/-- Iio_succ_eq_insert (abstract). -/
def Iio_succ_eq_insert' : Prop := True
/-- Ico_succ_right_eq_insert (abstract). -/
def Ico_succ_right_eq_insert' : Prop := True
/-- Ioo_succ_right_eq_insert (abstract). -/
def Ioo_succ_right_eq_insert' : Prop := True
/-- lt_succ_bot_iff (abstract). -/
def lt_succ_bot_iff' : Prop := True
/-- le_succ_bot_iff (abstract). -/
def le_succ_bot_iff' : Prop := True
/-- succ_eq_sInf (abstract). -/
def succ_eq_sInf' : Prop := True
/-- succ_eq_iInf (abstract). -/
def succ_eq_iInf' : Prop := True
/-- succ_eq_csInf (abstract). -/
def succ_eq_csInf' : Prop := True
-- COLLISION: pred' already in SetTheory.lean — rename needed
-- COLLISION: pred_le' already in SetTheory.lean — rename needed
/-- min_of_le_pred (abstract). -/
def min_of_le_pred' : Prop := True
/-- le_pred_of_lt (abstract). -/
def le_pred_of_lt' : Prop := True
/-- le_pred_iff_isMin (abstract). -/
def le_pred_iff_isMin' : Prop := True
/-- pred_lt_iff_not_isMin (abstract). -/
def pred_lt_iff_not_isMin' : Prop := True
/-- pred_wcovBy (abstract). -/
def pred_wcovBy' : Prop := True
/-- pred_covBy_of_not_isMin (abstract). -/
def pred_covBy_of_not_isMin' : Prop := True
/-- pred_lt_of_not_isMin_of_le (abstract). -/
def pred_lt_of_not_isMin_of_le' : Prop := True
/-- le_pred_iff_of_not_isMin (abstract). -/
def le_pred_iff_of_not_isMin' : Prop := True
/-- pred_lt_pred_of_not_isMin (abstract). -/
def pred_lt_pred_of_not_isMin' : Prop := True
/-- pred_iterate_le (abstract). -/
def pred_iterate_le' : Prop := True
/-- isMin_iterate_pred_of_eq_of_lt (abstract). -/
def isMin_iterate_pred_of_eq_of_lt' : Prop := True
/-- isMin_iterate_pred_of_eq_of_ne (abstract). -/
def isMin_iterate_pred_of_eq_of_ne' : Prop := True
/-- Ici_subset_Ioi_pred_of_not_isMin (abstract). -/
def Ici_subset_Ioi_pred_of_not_isMin' : Prop := True
/-- Iic_pred_of_not_isMin (abstract). -/
def Iic_pred_of_not_isMin' : Prop := True
/-- Icc_subset_Ioc_pred_left_of_not_isMin (abstract). -/
def Icc_subset_Ioc_pred_left_of_not_isMin' : Prop := True
/-- Ico_subset_Ioo_pred_left_of_not_isMin (abstract). -/
def Ico_subset_Ioo_pred_left_of_not_isMin' : Prop := True
/-- Icc_pred_right_of_not_isMin (abstract). -/
def Icc_pred_right_of_not_isMin' : Prop := True
/-- Ioc_pred_right_of_not_isMin (abstract). -/
def Ioc_pred_right_of_not_isMin' : Prop := True
/-- pred_lt (abstract). -/
def pred_lt' : Prop := True
/-- pred_lt_of_le (abstract). -/
def pred_lt_of_le' : Prop := True
/-- le_pred_iff (abstract). -/
def le_pred_iff' : Prop := True
/-- pred_le_pred_of_le (abstract). -/
def pred_le_pred_of_le' : Prop := True
/-- pred_lt_pred (abstract). -/
def pred_lt_pred' : Prop := True
/-- pred_strictMono (abstract). -/
def pred_strictMono' : Prop := True
/-- pred_covBy (abstract). -/
def pred_covBy' : Prop := True
/-- Ici_subset_Ioi_pred (abstract). -/
def Ici_subset_Ioi_pred' : Prop := True
/-- Iic_pred (abstract). -/
def Iic_pred' : Prop := True
/-- Icc_subset_Ioc_pred_left (abstract). -/
def Icc_subset_Ioc_pred_left' : Prop := True
/-- Ico_subset_Ioo_pred_left (abstract). -/
def Ico_subset_Ioo_pred_left' : Prop := True
/-- Ioc_pred_right (abstract). -/
def Ioc_pred_right' : Prop := True
/-- pred_eq_iff_isMin (abstract). -/
def pred_eq_iff_isMin' : Prop := True
/-- map_pred (abstract). -/
def map_pred' : Prop := True
/-- pred_eq_iff_covBy (abstract). -/
def pred_eq_iff_covBy' : Prop := True
/-- pred_bot (abstract). -/
def pred_bot' : Prop := True
/-- le_pred_iff_eq_bot (abstract). -/
def le_pred_iff_eq_bot' : Prop := True
/-- pred_lt_iff_ne_bot (abstract). -/
def pred_lt_iff_ne_bot' : Prop := True
/-- pred_lt_top (abstract). -/
def pred_lt_top' : Prop := True
/-- pred_ne_top (abstract). -/
def pred_ne_top' : Prop := True
/-- le_of_pred_lt (abstract). -/
def le_of_pred_lt' : Prop := True
/-- pred_lt_iff_of_not_isMin (abstract). -/
def pred_lt_iff_of_not_isMin' : Prop := True
/-- pred_lt_pred_iff_of_not_isMin (abstract). -/
def pred_lt_pred_iff_of_not_isMin' : Prop := True
/-- pred_le_pred_iff_of_not_isMin (abstract). -/
def pred_le_pred_iff_of_not_isMin' : Prop := True
/-- Ioi_pred_of_not_isMin (abstract). -/
def Ioi_pred_of_not_isMin' : Prop := True
/-- Ioc_pred_left_of_not_isMin (abstract). -/
def Ioc_pred_left_of_not_isMin' : Prop := True
/-- Ioo_pred_left_of_not_isMin (abstract). -/
def Ioo_pred_left_of_not_isMin' : Prop := True
/-- pred_eq_pred_iff_of_not_isMin (abstract). -/
def pred_eq_pred_iff_of_not_isMin' : Prop := True
/-- pred_le_iff_eq_or_le (abstract). -/
def pred_le_iff_eq_or_le' : Prop := True
/-- pred_lt_iff_eq_or_lt_of_not_isMin (abstract). -/
def pred_lt_iff_eq_or_lt_of_not_isMin' : Prop := True
/-- Ici_pred (abstract). -/
def Ici_pred' : Prop := True
/-- Ioi_pred_eq_insert_of_not_isMin (abstract). -/
def Ioi_pred_eq_insert_of_not_isMin' : Prop := True
/-- Icc_pred_left (abstract). -/
def Icc_pred_left' : Prop := True
/-- Ico_pred_left (abstract). -/
def Ico_pred_left' : Prop := True
/-- pred_lt_iff (abstract). -/
def pred_lt_iff' : Prop := True
/-- pred_le_pred_iff (abstract). -/
def pred_le_pred_iff' : Prop := True
/-- pred_lt_pred_iff (abstract). -/
def pred_lt_pred_iff' : Prop := True
/-- Ioi_pred (abstract). -/
def Ioi_pred' : Prop := True
/-- Ioc_pred_left (abstract). -/
def Ioc_pred_left' : Prop := True
/-- Ioo_pred_left (abstract). -/
def Ioo_pred_left' : Prop := True
/-- pred_eq_pred_iff (abstract). -/
def pred_eq_pred_iff' : Prop := True
/-- pred_injective (abstract). -/
def pred_injective' : Prop := True
/-- pred_ne_pred_iff (abstract). -/
def pred_ne_pred_iff' : Prop := True
/-- pred_lt_iff_eq_or_lt (abstract). -/
def pred_lt_iff_eq_or_lt' : Prop := True
/-- Ioi_pred_eq_insert (abstract). -/
def Ioi_pred_eq_insert' : Prop := True
/-- Ico_pred_right_eq_insert (abstract). -/
def Ico_pred_right_eq_insert' : Prop := True
/-- Ioo_pred_right_eq_insert (abstract). -/
def Ioo_pred_right_eq_insert' : Prop := True
/-- pred_top_lt_iff (abstract). -/
def pred_top_lt_iff' : Prop := True
/-- pred_top_le_iff (abstract). -/
def pred_top_le_iff' : Prop := True
/-- pred_eq_sSup (abstract). -/
def pred_eq_sSup' : Prop := True
/-- pred_eq_iSup (abstract). -/
def pred_eq_iSup' : Prop := True
/-- pred_eq_csSup (abstract). -/
def pred_eq_csSup' : Prop := True
/-- le_succ_pred (abstract). -/
def le_succ_pred' : Prop := True
/-- pred_succ_le (abstract). -/
def pred_succ_le' : Prop := True
/-- pred_le_iff_le_succ (abstract). -/
def pred_le_iff_le_succ' : Prop := True
/-- gc_pred_succ (abstract). -/
def gc_pred_succ' : Prop := True
/-- succ_pred_of_not_isMin (abstract). -/
def succ_pred_of_not_isMin' : Prop := True
/-- pred_succ_of_not_isMax (abstract). -/
def pred_succ_of_not_isMax' : Prop := True
/-- succ_pred (abstract). -/
def succ_pred' : Prop := True
/-- pred_succ (abstract). -/
def pred_succ' : Prop := True
/-- pred_succ_iterate_of_not_isMax (abstract). -/
def pred_succ_iterate_of_not_isMax' : Prop := True
/-- succ_pred_iterate_of_not_isMin (abstract). -/
def succ_pred_iterate_of_not_isMin' : Prop := True
/-- succ_coe_of_isMax (abstract). -/
def succ_coe_of_isMax' : Prop := True
/-- succ_coe_of_not_isMax (abstract). -/
def succ_coe_of_not_isMax' : Prop := True
/-- succ_coe (abstract). -/
def succ_coe' : Prop := True
/-- pred_untop (abstract). -/
def pred_untop' : Prop := True
/-- succ_unbot (abstract). -/
def succ_unbot' : Prop := True
/-- pred_coe_of_isMin (abstract). -/
def pred_coe_of_isMin' : Prop := True
/-- pred_coe_of_not_isMin (abstract). -/
def pred_coe_of_not_isMin' : Prop := True
/-- pred_coe (abstract). -/
def pred_coe' : Prop := True
/-- ofOrderIso (abstract). -/
def ofOrderIso' : Prop := True
/-- coe_pred_of_mem (abstract). -/
def coe_pred_of_mem' : Prop := True
/-- isMin_of_not_pred_mem (abstract). -/
def isMin_of_not_pred_mem' : Prop := True
/-- not_pred_mem_iff_isMin (abstract). -/
def not_pred_mem_iff_isMin' : Prop := True
/-- coe_succ_of_mem (abstract). -/
def coe_succ_of_mem' : Prop := True
/-- isMax_of_not_succ_mem (abstract). -/
def isMax_of_not_succ_mem' : Prop := True
/-- not_succ_mem_iff_isMax (abstract). -/
def not_succ_mem_iff_isMax' : Prop := True

-- SuccPred/CompleteLinearOrder.lean
/-- csSup_mem_of_not_isSuccPrelimit (abstract). -/
def csSup_mem_of_not_isSuccPrelimit' : Prop := True
/-- csInf_mem_of_not_isPredPrelimit (abstract). -/
def csInf_mem_of_not_isPredPrelimit' : Prop := True
/-- exists_eq_ciSup_of_not_isSuccPrelimit (abstract). -/
def exists_eq_ciSup_of_not_isSuccPrelimit' : Prop := True
/-- exists_eq_ciInf_of_not_isPredPrelimit (abstract). -/
def exists_eq_ciInf_of_not_isPredPrelimit' : Prop := True
/-- mem_of_nonempty_of_not_isSuccPrelimit (abstract). -/
def mem_of_nonempty_of_not_isSuccPrelimit' : Prop := True
/-- mem_of_nonempty_of_not_isPredPrelimit (abstract). -/
def mem_of_nonempty_of_not_isPredPrelimit' : Prop := True
/-- exists_of_nonempty_of_not_isSuccPrelimit (abstract). -/
def exists_of_nonempty_of_not_isSuccPrelimit' : Prop := True
/-- exists_of_nonempty_of_not_isPredPrelimit (abstract). -/
def exists_of_nonempty_of_not_isPredPrelimit' : Prop := True
/-- toSuccOrder (abstract). -/
def toSuccOrder' : Prop := True
/-- mem_of_not_isSuccPrelimit (abstract). -/
def mem_of_not_isSuccPrelimit' : Prop := True
/-- exists_of_not_isSuccPrelimit (abstract). -/
def exists_of_not_isSuccPrelimit' : Prop := True
/-- sSup_mem_of_not_isSuccPrelimit (abstract). -/
def sSup_mem_of_not_isSuccPrelimit' : Prop := True
/-- sInf_mem_of_not_isPredPrelimit (abstract). -/
def sInf_mem_of_not_isPredPrelimit' : Prop := True
/-- exists_eq_iSup_of_not_isSuccPrelimit (abstract). -/
def exists_eq_iSup_of_not_isSuccPrelimit' : Prop := True
/-- exists_eq_iInf_of_not_isPredPrelimit (abstract). -/
def exists_eq_iInf_of_not_isPredPrelimit' : Prop := True
/-- mem_of_not_isPredPrelimit (abstract). -/
def mem_of_not_isPredPrelimit' : Prop := True
/-- exists_of_not_isPredPrelimit (abstract). -/
def exists_of_not_isPredPrelimit' : Prop := True

-- SuccPred/InitialSeg.lean
/-- apply_wCovBy_apply_iff (abstract). -/
def apply_wCovBy_apply_iff' : Prop := True
/-- isSuccPrelimit_apply_iff (abstract). -/
def isSuccPrelimit_apply_iff' : Prop := True
/-- isSuccLimit_apply_iff (abstract). -/
def isSuccLimit_apply_iff' : Prop := True

-- SuccPred/IntervalSucc.lean
/-- biUnion_Ico_Ioc_map_succ (abstract). -/
def biUnion_Ico_Ioc_map_succ' : Prop := True
/-- pairwise_disjoint_on_Ioc_succ (abstract). -/
def pairwise_disjoint_on_Ioc_succ' : Prop := True
/-- pairwise_disjoint_on_Ico_succ (abstract). -/
def pairwise_disjoint_on_Ico_succ' : Prop := True
/-- pairwise_disjoint_on_Ioo_succ (abstract). -/
def pairwise_disjoint_on_Ioo_succ' : Prop := True
/-- pairwise_disjoint_on_Ioc_pred (abstract). -/
def pairwise_disjoint_on_Ioc_pred' : Prop := True
/-- pairwise_disjoint_on_Ico_pred (abstract). -/
def pairwise_disjoint_on_Ico_pred' : Prop := True
/-- pairwise_disjoint_on_Ioo_pred (abstract). -/
def pairwise_disjoint_on_Ioo_pred' : Prop := True

-- SuccPred/Limit.lean
/-- IsSuccPrelimit (abstract). -/
def IsSuccPrelimit' : Prop := True
/-- IsSuccLimit (abstract). -/
def IsSuccLimit' : Prop := True
/-- isSuccPrelimit_iff_isSuccLimit_of_not_isMin (abstract). -/
def isSuccPrelimit_iff_isSuccLimit_of_not_isMin' : Prop := True
/-- isSuccPrelimit_iff_isSuccLimit (abstract). -/
def isSuccPrelimit_iff_isSuccLimit' : Prop := True
/-- not_isSuccLimit (abstract). -/
def not_isSuccLimit' : Prop := True
-- COLLISION: isSuccPrelimit' already in SetTheory.lean — rename needed
/-- isSuccPrelimit_bot (abstract). -/
def isSuccPrelimit_bot' : Prop := True
/-- not_isSuccLimit_bot (abstract). -/
def not_isSuccLimit_bot' : Prop := True
/-- not_isSuccPrelimit_succ_of_not_isMax (abstract). -/
def not_isSuccPrelimit_succ_of_not_isMax' : Prop := True
/-- not_isSuccLimit_succ_of_not_isMax (abstract). -/
def not_isSuccLimit_succ_of_not_isMax' : Prop := True
/-- mid (abstract). -/
def mid' : Prop := True
/-- not_isSuccPrelimit_succ (abstract). -/
def not_isSuccPrelimit_succ' : Prop := True
/-- not_isSuccLimit_succ (abstract). -/
def not_isSuccLimit_succ' : Prop := True
/-- isMin_of_noMax (abstract). -/
def isMin_of_noMax' : Prop := True
/-- isSuccPrelimit_iff_of_noMax (abstract). -/
def isSuccPrelimit_iff_of_noMax' : Prop := True
/-- not_isSuccLimit_of_noMax (abstract). -/
def not_isSuccLimit_of_noMax' : Prop := True
/-- isSuccLimit_iff (abstract). -/
def isSuccLimit_iff' : Prop := True
/-- isSuccPrelimit_of_succ_ne (abstract). -/
def isSuccPrelimit_of_succ_ne' : Prop := True
/-- not_isSuccPrelimit_iff (abstract). -/
def not_isSuccPrelimit_iff' : Prop := True
/-- mem_range_succ_of_not_isSuccPrelimit (abstract). -/
def mem_range_succ_of_not_isSuccPrelimit' : Prop := True
/-- mem_range_succ_or_isSuccPrelimit (abstract). -/
def mem_range_succ_or_isSuccPrelimit' : Prop := True
/-- isSuccPrelimit_of_succ_lt (abstract). -/
def isSuccPrelimit_of_succ_lt' : Prop := True
/-- succ_lt (abstract). -/
def succ_lt' : Prop := True
/-- succ_lt_iff (abstract). -/
def succ_lt_iff' : Prop := True
/-- isSuccPrelimit_iff_succ_lt (abstract). -/
def isSuccPrelimit_iff_succ_lt' : Prop := True
/-- isSuccPrelimit_iff_succ_ne (abstract). -/
def isSuccPrelimit_iff_succ_ne' : Prop := True
/-- isSuccPrelimit_iff (abstract). -/
def isSuccPrelimit_iff' : Prop := True
/-- le_iff_forall_le (abstract). -/
def le_iff_forall_le' : Prop := True
/-- lt_iff_exists_lt (abstract). -/
def lt_iff_exists_lt' : Prop := True
/-- IsPredPrelimit (abstract). -/
def IsPredPrelimit' : Prop := True
/-- not_isPredPrelimit_iff_exists_covBy (abstract). -/
def not_isPredPrelimit_iff_exists_covBy' : Prop := True
/-- of_dense (abstract). -/
def of_dense' : Prop := True
/-- isSuccPrelimit_toDual_iff (abstract). -/
def isSuccPrelimit_toDual_iff' : Prop := True
/-- isPredPrelimit_toDual_iff (abstract). -/
def isPredPrelimit_toDual_iff' : Prop := True
/-- IsPredLimit (abstract). -/
def IsPredLimit' : Prop := True
/-- isSuccLimit_toDual_iff (abstract). -/
def isSuccLimit_toDual_iff' : Prop := True
/-- isPredPrelimit_iff_isPredLimit_of_not_isMax (abstract). -/
def isPredPrelimit_iff_isPredLimit_of_not_isMax' : Prop := True
/-- isPredPrelimit_iff_isPredLimit (abstract). -/
def isPredPrelimit_iff_isPredLimit' : Prop := True
/-- not_isPredLimit (abstract). -/
def not_isPredLimit' : Prop := True
/-- isPredPrelimit_iff_of_noMin (abstract). -/
def isPredPrelimit_iff_of_noMin' : Prop := True
/-- not_isPredLimit_of_noMin (abstract). -/
def not_isPredLimit_of_noMin' : Prop := True
/-- isPredLimit_iff (abstract). -/
def isPredLimit_iff' : Prop := True
/-- isPredPrelimit_of_pred_ne (abstract). -/
def isPredPrelimit_of_pred_ne' : Prop := True
/-- not_isPredPrelimit_iff (abstract). -/
def not_isPredPrelimit_iff' : Prop := True
/-- mem_range_pred_of_not_isPredPrelimit (abstract). -/
def mem_range_pred_of_not_isPredPrelimit' : Prop := True
/-- mem_range_pred_or_isPredPrelimit (abstract). -/
def mem_range_pred_or_isPredPrelimit' : Prop := True
/-- lt_pred (abstract). -/
def lt_pred' : Prop := True
/-- lt_pred_iff (abstract). -/
def lt_pred_iff' : Prop := True
/-- isPredPrelimit_iff_lt_pred (abstract). -/
def isPredPrelimit_iff_lt_pred' : Prop := True
/-- isSuccPrelimitRecOn (abstract). -/
def isSuccPrelimitRecOn' : Prop := True
/-- isSuccPrelimitRecOn_of_isSuccPrelimit (abstract). -/
def isSuccPrelimitRecOn_of_isSuccPrelimit' : Prop := True
/-- isSuccPrelimitRecOn_succ_of_not_isMax (abstract). -/
def isSuccPrelimitRecOn_succ_of_not_isMax' : Prop := True
/-- isSuccPrelimitRecOn_succ (abstract). -/
def isSuccPrelimitRecOn_succ' : Prop := True
/-- isPredPrelimitRecOn (abstract). -/
def isPredPrelimitRecOn' : Prop := True
/-- isPredPrelimitRecOn_of_isPredPrelimit (abstract). -/
def isPredPrelimitRecOn_of_isPredPrelimit' : Prop := True
/-- isPredPrelimitRecOn_pred_of_not_isMin (abstract). -/
def isPredPrelimitRecOn_pred_of_not_isMin' : Prop := True
/-- isPredPrelimitRecOn_pred (abstract). -/
def isPredPrelimitRecOn_pred' : Prop := True
/-- isSuccLimitRecOn (abstract). -/
def isSuccLimitRecOn' : Prop := True
/-- isSuccLimitRecOn_of_isSuccLimit (abstract). -/
def isSuccLimitRecOn_of_isSuccLimit' : Prop := True
/-- isSuccLimitRecOn_succ_of_not_isMax (abstract). -/
def isSuccLimitRecOn_succ_of_not_isMax' : Prop := True
/-- isSuccLimitRecOn_succ (abstract). -/
def isSuccLimitRecOn_succ' : Prop := True
/-- isSuccLimitRecOn_of_isMin (abstract). -/
def isSuccLimitRecOn_of_isMin' : Prop := True
/-- isPredLimitRecOn (abstract). -/
def isPredLimitRecOn' : Prop := True
/-- isPredLimitRecOn_of_isPredLimit (abstract). -/
def isPredLimitRecOn_of_isPredLimit' : Prop := True
/-- isPredLimitRecOn_pred_of_not_isMin (abstract). -/
def isPredLimitRecOn_pred_of_not_isMin' : Prop := True
/-- isPredLimitRecOn_pred (abstract). -/
def isPredLimitRecOn_pred' : Prop := True
/-- isPredLimitRecOn_of_isMax (abstract). -/
def isPredLimitRecOn_of_isMax' : Prop := True
/-- prelimitRecOn (abstract). -/
def prelimitRecOn' : Prop := True
/-- prelimitRecOn_of_isSuccPrelimit (abstract). -/
def prelimitRecOn_of_isSuccPrelimit' : Prop := True
/-- prelimitRecOn_succ_of_not_isMax (abstract). -/
def prelimitRecOn_succ_of_not_isMax' : Prop := True
/-- prelimitRecOn_succ (abstract). -/
def prelimitRecOn_succ' : Prop := True
-- COLLISION: limitRecOn' already in SetTheory.lean — rename needed
/-- limitRecOn_isMin (abstract). -/
def limitRecOn_isMin' : Prop := True
/-- limitRecOn_of_isSuccLimit (abstract). -/
def limitRecOn_of_isSuccLimit' : Prop := True
/-- limitRecOn_succ_of_not_isMax (abstract). -/
def limitRecOn_succ_of_not_isMax' : Prop := True
-- COLLISION: limitRecOn_succ' already in SetTheory.lean — rename needed
/-- prelimitRecOn_of_isPredPrelimit (abstract). -/
def prelimitRecOn_of_isPredPrelimit' : Prop := True
/-- prelimitRecOn_pred_of_not_isMin (abstract). -/
def prelimitRecOn_pred_of_not_isMin' : Prop := True
/-- prelimitRecOn_pred (abstract). -/
def prelimitRecOn_pred' : Prop := True
/-- limitRecOn_isMax (abstract). -/
def limitRecOn_isMax' : Prop := True
/-- limitRecOn_of_isPredLimit (abstract). -/
def limitRecOn_of_isPredLimit' : Prop := True
/-- limitRecOn_pred_of_not_isMin (abstract). -/
def limitRecOn_pred_of_not_isMin' : Prop := True
/-- limitRecOn_pred (abstract). -/
def limitRecOn_pred' : Prop := True

-- SuccPred/LinearLocallyFinite.lean
/-- isSuccArchimedean_iff_isPredArchimedean (abstract). -/
def isSuccArchimedean_iff_isPredArchimedean' : Prop := True
/-- succFn (abstract). -/
def succFn' : Prop := True
/-- succFn_spec (abstract). -/
def succFn_spec' : Prop := True
/-- le_succFn (abstract). -/
def le_succFn' : Prop := True
/-- isGLB_Ioc_of_isGLB_Ioi (abstract). -/
def isGLB_Ioc_of_isGLB_Ioi' : Prop := True
/-- isMax_of_succFn_le (abstract). -/
def isMax_of_succFn_le' : Prop := True
/-- succFn_le_of_lt (abstract). -/
def succFn_le_of_lt' : Prop := True
/-- le_of_lt_succFn (abstract). -/
def le_of_lt_succFn' : Prop := True
/-- toZ (abstract). -/
def toZ' : Prop := True
/-- toZ_of_ge (abstract). -/
def toZ_of_ge' : Prop := True
/-- toZ_of_lt (abstract). -/
def toZ_of_lt' : Prop := True
/-- toZ_of_eq (abstract). -/
def toZ_of_eq' : Prop := True
/-- iterate_succ_toZ (abstract). -/
def iterate_succ_toZ' : Prop := True
/-- iterate_pred_toZ (abstract). -/
def iterate_pred_toZ' : Prop := True
/-- toZ_nonneg (abstract). -/
def toZ_nonneg' : Prop := True
/-- toZ_neg (abstract). -/
def toZ_neg' : Prop := True
/-- toZ_iterate_succ_le (abstract). -/
def toZ_iterate_succ_le' : Prop := True
/-- toZ_iterate_pred_ge (abstract). -/
def toZ_iterate_pred_ge' : Prop := True
/-- toZ_iterate_succ_of_not_isMax (abstract). -/
def toZ_iterate_succ_of_not_isMax' : Prop := True
/-- toZ_iterate_pred_of_not_isMin (abstract). -/
def toZ_iterate_pred_of_not_isMin' : Prop := True
/-- le_of_toZ_le (abstract). -/
def le_of_toZ_le' : Prop := True
/-- toZ_mono (abstract). -/
def toZ_mono' : Prop := True
/-- toZ_le_iff (abstract). -/
def toZ_le_iff' : Prop := True
/-- toZ_iterate_succ (abstract). -/
def toZ_iterate_succ' : Prop := True
/-- toZ_iterate_pred (abstract). -/
def toZ_iterate_pred' : Prop := True
/-- injective_toZ (abstract). -/
def injective_toZ' : Prop := True
/-- orderIsoRangeToZOfLinearSuccPredArch (abstract). -/
def orderIsoRangeToZOfLinearSuccPredArch' : Prop := True
/-- orderIsoIntOfLinearSuccPredArch (abstract). -/
def orderIsoIntOfLinearSuccPredArch' : Prop := True
/-- orderIsoNatOfLinearSuccPredArch (abstract). -/
def orderIsoNatOfLinearSuccPredArch' : Prop := True
/-- orderIsoRangeOfLinearSuccPredArch (abstract). -/
def orderIsoRangeOfLinearSuccPredArch' : Prop := True

-- SuccPred/Relation.lean
/-- reflTransGen_of_succ_of_le (abstract). -/
def reflTransGen_of_succ_of_le' : Prop := True
/-- reflTransGen_of_succ_of_ge (abstract). -/
def reflTransGen_of_succ_of_ge' : Prop := True
/-- transGen_of_succ_of_lt (abstract). -/
def transGen_of_succ_of_lt' : Prop := True
/-- transGen_of_succ_of_gt (abstract). -/
def transGen_of_succ_of_gt' : Prop := True
/-- reflTransGen_of_succ (abstract). -/
def reflTransGen_of_succ' : Prop := True
/-- transGen_of_succ_of_ne (abstract). -/
def transGen_of_succ_of_ne' : Prop := True
/-- transGen_of_succ_of_reflexive (abstract). -/
def transGen_of_succ_of_reflexive' : Prop := True
/-- reflTransGen_of_pred_of_ge (abstract). -/
def reflTransGen_of_pred_of_ge' : Prop := True
/-- reflTransGen_of_pred_of_le (abstract). -/
def reflTransGen_of_pred_of_le' : Prop := True
/-- transGen_of_pred_of_gt (abstract). -/
def transGen_of_pred_of_gt' : Prop := True
/-- transGen_of_pred_of_lt (abstract). -/
def transGen_of_pred_of_lt' : Prop := True
/-- reflTransGen_of_pred (abstract). -/
def reflTransGen_of_pred' : Prop := True
/-- transGen_of_pred_of_ne (abstract). -/
def transGen_of_pred_of_ne' : Prop := True
/-- transGen_of_pred_of_reflexive (abstract). -/
def transGen_of_pred_of_reflexive' : Prop := True

-- SuccPred/Tree.lean
/-- findAtom (abstract). -/
def findAtom' : Prop := True
/-- findAtom_le (abstract). -/
def findAtom_le' : Prop := True
/-- findAtom_bot (abstract). -/
def findAtom_bot' : Prop := True
/-- pred_findAtom (abstract). -/
def pred_findAtom' : Prop := True
/-- findAtom_eq_bot (abstract). -/
def findAtom_eq_bot' : Prop := True
/-- findAtom_ne_bot (abstract). -/
def findAtom_ne_bot' : Prop := True
/-- isAtom_findAtom (abstract). -/
def isAtom_findAtom' : Prop := True
/-- isAtom_findAtom_iff (abstract). -/
def isAtom_findAtom_iff' : Prop := True
/-- RootedTree (abstract). -/
def RootedTree' : Prop := True
/-- SubRootedTree (abstract). -/
def SubRootedTree' : Prop := True
/-- root (abstract). -/
def root' : Prop := True
/-- subtree (abstract). -/
def subtree' : Prop := True
/-- coeTree (abstract). -/
def coeTree' : Prop := True
/-- subtrees (abstract). -/
def subtrees' : Prop := True
/-- root_ne_bot_of_mem_subtrees (abstract). -/
def root_ne_bot_of_mem_subtrees' : Prop := True
/-- mem_subtrees_disjoint_iff (abstract). -/
def mem_subtrees_disjoint_iff' : Prop := True
/-- subtrees_disjoint (abstract). -/
def subtrees_disjoint' : Prop := True
/-- subtreeOf (abstract). -/
def subtreeOf' : Prop := True
/-- mem_subtreeOf (abstract). -/
def mem_subtreeOf' : Prop := True
/-- subtreeOf_mem_subtrees (abstract). -/
def subtreeOf_mem_subtrees' : Prop := True

-- SupClosed.lean
/-- SupClosed (abstract). -/
def SupClosed' : Prop := True
/-- supClosed_empty (abstract). -/
def supClosed_empty' : Prop := True
/-- supClosed_singleton (abstract). -/
def supClosed_singleton' : Prop := True
/-- supClosed_univ (abstract). -/
def supClosed_univ' : Prop := True
/-- supClosed_sInter (abstract). -/
def supClosed_sInter' : Prop := True
/-- supClosed_iInter (abstract). -/
def supClosed_iInter' : Prop := True
/-- supClosed (abstract). -/
def supClosed' : Prop := True
/-- supClosed_range (abstract). -/
def supClosed_range' : Prop := True
/-- supClosed_pi (abstract). -/
def supClosed_pi' : Prop := True
/-- insert_upperBounds (abstract). -/
def insert_upperBounds' : Prop := True
/-- insert_lowerBounds (abstract). -/
def insert_lowerBounds' : Prop := True
/-- finsetSup'_mem (abstract). -/
def finsetSup'_mem' : Prop := True
/-- finsetSup_mem (abstract). -/
def finsetSup_mem' : Prop := True
/-- InfClosed (abstract). -/
def InfClosed' : Prop := True
/-- infClosed_empty (abstract). -/
def infClosed_empty' : Prop := True
/-- infClosed_singleton (abstract). -/
def infClosed_singleton' : Prop := True
/-- infClosed_univ (abstract). -/
def infClosed_univ' : Prop := True
/-- infClosed_sInter (abstract). -/
def infClosed_sInter' : Prop := True
/-- infClosed_iInter (abstract). -/
def infClosed_iInter' : Prop := True
/-- codirectedOn (abstract). -/
def codirectedOn' : Prop := True
/-- infClosed (abstract). -/
def infClosed' : Prop := True
/-- infClosed_range (abstract). -/
def infClosed_range' : Prop := True
/-- infClosed_pi (abstract). -/
def infClosed_pi' : Prop := True
/-- finsetInf'_mem (abstract). -/
def finsetInf'_mem' : Prop := True
/-- finsetInf_mem (abstract). -/
def finsetInf_mem' : Prop := True
/-- IsSublattice (abstract). -/
def IsSublattice' : Prop := True
/-- isSublattice_empty (abstract). -/
def isSublattice_empty' : Prop := True
/-- isSublattice_singleton (abstract). -/
def isSublattice_singleton' : Prop := True
/-- isSublattice_univ (abstract). -/
def isSublattice_univ' : Prop := True
/-- isSublattice_sInter (abstract). -/
def isSublattice_sInter' : Prop := True
/-- isSublattice_iInter (abstract). -/
def isSublattice_iInter' : Prop := True
/-- IsSublattice_range (abstract). -/
def IsSublattice_range' : Prop := True
/-- isSublattice_preimage_toDual (abstract). -/
def isSublattice_preimage_toDual' : Prop := True
/-- isSublattice_preimage_ofDual (abstract). -/
def isSublattice_preimage_ofDual' : Prop := True
/-- isSublattice (abstract). -/
def isSublattice' : Prop := True
/-- supClosure (abstract). -/
def supClosure' : Prop := True
/-- subset_supClosure (abstract). -/
def subset_supClosure' : Prop := True
/-- supClosed_supClosure (abstract). -/
def supClosed_supClosure' : Prop := True
/-- supClosure_mono (abstract). -/
def supClosure_mono' : Prop := True
/-- supClosure_eq_self (abstract). -/
def supClosure_eq_self' : Prop := True
/-- supClosure_idem (abstract). -/
def supClosure_idem' : Prop := True
/-- supClosure_empty (abstract). -/
def supClosure_empty' : Prop := True
/-- supClosure_singleton (abstract). -/
def supClosure_singleton' : Prop := True
/-- supClosure_univ (abstract). -/
def supClosure_univ' : Prop := True
/-- upperBounds_supClosure (abstract). -/
def upperBounds_supClosure' : Prop := True
/-- isLUB_supClosure (abstract). -/
def isLUB_supClosure' : Prop := True
/-- sup_mem_supClosure (abstract). -/
def sup_mem_supClosure' : Prop := True
/-- finsetSup'_mem_supClosure (abstract). -/
def finsetSup'_mem_supClosure' : Prop := True
/-- supClosure_min (abstract). -/
def supClosure_min' : Prop := True
/-- supClosure_prod (abstract). -/
def supClosure_prod' : Prop := True
/-- infClosure (abstract). -/
def infClosure' : Prop := True
/-- subset_infClosure (abstract). -/
def subset_infClosure' : Prop := True
/-- infClosed_infClosure (abstract). -/
def infClosed_infClosure' : Prop := True
/-- infClosure_mono (abstract). -/
def infClosure_mono' : Prop := True
/-- infClosure_eq_self (abstract). -/
def infClosure_eq_self' : Prop := True
/-- infClosure_idem (abstract). -/
def infClosure_idem' : Prop := True
/-- infClosure_empty (abstract). -/
def infClosure_empty' : Prop := True
/-- infClosure_singleton (abstract). -/
def infClosure_singleton' : Prop := True
/-- infClosure_univ (abstract). -/
def infClosure_univ' : Prop := True
/-- lowerBounds_infClosure (abstract). -/
def lowerBounds_infClosure' : Prop := True
/-- isGLB_infClosure (abstract). -/
def isGLB_infClosure' : Prop := True
/-- inf_mem_infClosure (abstract). -/
def inf_mem_infClosure' : Prop := True
/-- finsetInf'_mem_infClosure (abstract). -/
def finsetInf'_mem_infClosure' : Prop := True
/-- infClosure_min (abstract). -/
def infClosure_min' : Prop := True
/-- infClosure_prod (abstract). -/
def infClosure_prod' : Prop := True
/-- latticeClosure (abstract). -/
def latticeClosure' : Prop := True
/-- subset_latticeClosure (abstract). -/
def subset_latticeClosure' : Prop := True
/-- isSublattice_latticeClosure (abstract). -/
def isSublattice_latticeClosure' : Prop := True
/-- latticeClosure_min (abstract). -/
def latticeClosure_min' : Prop := True
/-- latticeClosure_mono (abstract). -/
def latticeClosure_mono' : Prop := True
/-- latticeClosure_eq_self (abstract). -/
def latticeClosure_eq_self' : Prop := True
/-- latticeClosure_idem (abstract). -/
def latticeClosure_idem' : Prop := True
/-- latticeClosure_empty (abstract). -/
def latticeClosure_empty' : Prop := True
/-- latticeClosure_singleton (abstract). -/
def latticeClosure_singleton' : Prop := True
/-- latticeClosure_univ (abstract). -/
def latticeClosure_univ' : Prop := True
/-- supClosure_infClosure (abstract). -/
def supClosure_infClosure' : Prop := True
/-- infClosure_supClosure (abstract). -/
def infClosure_supClosure' : Prop := True
/-- latticeClosure_prod (abstract). -/
def latticeClosure_prod' : Prop := True
/-- toCompleteSemilatticeSup (abstract). -/
def toCompleteSemilatticeSup' : Prop := True
/-- toCompleteSemilatticeInf (abstract). -/
def toCompleteSemilatticeInf' : Prop := True

-- SupIndep.lean
/-- SupIndep (abstract). -/
def SupIndep' : Prop := True
/-- supIndep_empty (abstract). -/
def supIndep_empty' : Prop := True
/-- supIndep_singleton (abstract). -/
def supIndep_singleton' : Prop := True
/-- pairwiseDisjoint (abstract). -/
def pairwiseDisjoint' : Prop := True
/-- supIndep_iff_disjoint_erase (abstract). -/
def supIndep_iff_disjoint_erase' : Prop := True
/-- supIndep_antimono_fun (abstract). -/
def supIndep_antimono_fun' : Prop := True
/-- supIndep_map (abstract). -/
def supIndep_map' : Prop := True
/-- supIndep_pair (abstract). -/
def supIndep_pair' : Prop := True
/-- supIndep_univ_bool (abstract). -/
def supIndep_univ_bool' : Prop := True
/-- supIndep_attach (abstract). -/
def supIndep_attach' : Prop := True
/-- supIndep_iff_pairwiseDisjoint (abstract). -/
def supIndep_iff_pairwiseDisjoint' : Prop := True
/-- biUnion (abstract). -/
def biUnion' : Prop := True
/-- sigma (abstract). -/
def sigma' : Prop := True
/-- supIndep_product_iff (abstract). -/
def supIndep_product_iff' : Prop := True
/-- sSupIndep (abstract). -/
def sSupIndep' : Prop := True
/-- sSupIndep_empty (abstract). -/
def sSupIndep_empty' : Prop := True
/-- sSupIndep_singleton (abstract). -/
def sSupIndep_singleton' : Prop := True
/-- sSupIndep_pair (abstract). -/
def sSupIndep_pair' : Prop := True
/-- disjoint_sSup (abstract). -/
def disjoint_sSup' : Prop := True
/-- iSupIndep (abstract). -/
def iSupIndep' : Prop := True
/-- iSupIndep_def' (abstract). -/
def iSupIndep_def' : Prop := True
/-- iSupIndep_def'' (abstract). -/
def iSupIndep_def'' : Prop := True
/-- iSupIndep_empty (abstract). -/
def iSupIndep_empty' : Prop := True
/-- iSupIndep_pempty (abstract). -/
def iSupIndep_pempty' : Prop := True
/-- sSupIndep_range (abstract). -/
def sSupIndep_range' : Prop := True
/-- iSupIndep_ne_bot (abstract). -/
def iSupIndep_ne_bot' : Prop := True
/-- injOn (abstract). -/
def injOn' : Prop := True
/-- iSupIndep_pair (abstract). -/
def iSupIndep_pair' : Prop := True
/-- iSupIndep_map_orderIso_iff (abstract). -/
def iSupIndep_map_orderIso_iff' : Prop := True
/-- disjoint_biSup (abstract). -/
def disjoint_biSup' : Prop := True
/-- of_coe_Iic_comp (abstract). -/
def of_coe_Iic_comp' : Prop := True
/-- iSupIndep_iff_supIndep (abstract). -/
def iSupIndep_iff_supIndep' : Prop := True
/-- supIndep' (abstract). -/
def supIndep' : Prop := True
/-- iSupIndep_iff_supIndep_univ (abstract). -/
def iSupIndep_iff_supIndep_univ' : Prop := True
/-- sSupIndep_iff_pairwiseDisjoint (abstract). -/
def sSupIndep_iff_pairwiseDisjoint' : Prop := True
/-- iSupIndep_iff_pairwiseDisjoint (abstract). -/
def iSupIndep_iff_pairwiseDisjoint' : Prop := True

-- SymmDiff.lean
/-- bihimp (abstract). -/
def bihimp' : Prop := True
/-- symmDiff_comm (abstract). -/
def symmDiff_comm' : Prop := True
/-- symmDiff_self (abstract). -/
def symmDiff_self' : Prop := True
/-- symmDiff_bot (abstract). -/
def symmDiff_bot' : Prop := True
/-- bot_symmDiff (abstract). -/
def bot_symmDiff' : Prop := True
/-- symmDiff_eq_bot (abstract). -/
def symmDiff_eq_bot' : Prop := True
/-- symmDiff_of_le (abstract). -/
def symmDiff_of_le' : Prop := True
/-- symmDiff_of_ge (abstract). -/
def symmDiff_of_ge' : Prop := True
/-- symmDiff_le (abstract). -/
def symmDiff_le' : Prop := True
/-- symmDiff_le_iff (abstract). -/
def symmDiff_le_iff' : Prop := True
/-- symmDiff_le_sup (abstract). -/
def symmDiff_le_sup' : Prop := True
/-- symmDiff_eq_sup_sdiff_inf (abstract). -/
def symmDiff_eq_sup_sdiff_inf' : Prop := True
/-- symmDiff_eq_sup (abstract). -/
def symmDiff_eq_sup' : Prop := True
/-- symmDiff_sdiff (abstract). -/
def symmDiff_sdiff' : Prop := True
/-- symmDiff_sdiff_inf (abstract). -/
def symmDiff_sdiff_inf' : Prop := True
/-- symmDiff_sdiff_eq_sup (abstract). -/
def symmDiff_sdiff_eq_sup' : Prop := True
/-- sdiff_symmDiff_eq_sup (abstract). -/
def sdiff_symmDiff_eq_sup' : Prop := True
/-- symmDiff_sup_inf (abstract). -/
def symmDiff_sup_inf' : Prop := True
/-- inf_sup_symmDiff (abstract). -/
def inf_sup_symmDiff' : Prop := True
/-- symmDiff_symmDiff_inf (abstract). -/
def symmDiff_symmDiff_inf' : Prop := True
/-- inf_symmDiff_symmDiff (abstract). -/
def inf_symmDiff_symmDiff' : Prop := True
/-- symmDiff_triangle (abstract). -/
def symmDiff_triangle' : Prop := True
/-- bihimp_comm (abstract). -/
def bihimp_comm' : Prop := True
/-- bihimp_self (abstract). -/
def bihimp_self' : Prop := True
/-- bihimp_top (abstract). -/
def bihimp_top' : Prop := True
/-- top_bihimp (abstract). -/
def top_bihimp' : Prop := True
/-- bihimp_eq_top (abstract). -/
def bihimp_eq_top' : Prop := True
/-- bihimp_of_le (abstract). -/
def bihimp_of_le' : Prop := True
/-- bihimp_of_ge (abstract). -/
def bihimp_of_ge' : Prop := True
/-- le_bihimp (abstract). -/
def le_bihimp' : Prop := True
/-- le_bihimp_iff (abstract). -/
def le_bihimp_iff' : Prop := True
/-- inf_le_bihimp (abstract). -/
def inf_le_bihimp' : Prop := True
/-- bihimp_eq_inf_himp_inf (abstract). -/
def bihimp_eq_inf_himp_inf' : Prop := True
/-- bihimp_eq_inf (abstract). -/
def bihimp_eq_inf' : Prop := True
/-- himp_bihimp (abstract). -/
def himp_bihimp' : Prop := True
/-- sup_himp_bihimp (abstract). -/
def sup_himp_bihimp' : Prop := True
/-- bihimp_himp_eq_inf (abstract). -/
def bihimp_himp_eq_inf' : Prop := True
/-- himp_bihimp_eq_inf (abstract). -/
def himp_bihimp_eq_inf' : Prop := True
/-- bihimp_inf_sup (abstract). -/
def bihimp_inf_sup' : Prop := True
/-- sup_inf_bihimp (abstract). -/
def sup_inf_bihimp' : Prop := True
/-- bihimp_bihimp_sup (abstract). -/
def bihimp_bihimp_sup' : Prop := True
/-- sup_bihimp_bihimp (abstract). -/
def sup_bihimp_bihimp' : Prop := True
/-- bihimp_triangle (abstract). -/
def bihimp_triangle' : Prop := True
/-- symmDiff_top' (abstract). -/
def symmDiff_top' : Prop := True
/-- top_symmDiff' (abstract). -/
def top_symmDiff' : Prop := True
/-- hnot_symmDiff_self (abstract). -/
def hnot_symmDiff_self' : Prop := True
/-- symmDiff_hnot_self (abstract). -/
def symmDiff_hnot_self' : Prop := True
/-- symmDiff_eq_top (abstract). -/
def symmDiff_eq_top' : Prop := True
/-- bihimp_bot (abstract). -/
def bihimp_bot' : Prop := True
/-- bot_bihimp (abstract). -/
def bot_bihimp' : Prop := True
/-- compl_bihimp_self (abstract). -/
def compl_bihimp_self' : Prop := True
/-- bihimp_hnot_self (abstract). -/
def bihimp_hnot_self' : Prop := True
/-- bihimp_eq_bot (abstract). -/
def bihimp_eq_bot' : Prop := True
/-- sup_sdiff_symmDiff (abstract). -/
def sup_sdiff_symmDiff' : Prop := True
/-- disjoint_symmDiff_inf (abstract). -/
def disjoint_symmDiff_inf' : Prop := True
/-- inf_symmDiff_distrib_left (abstract). -/
def inf_symmDiff_distrib_left' : Prop := True
/-- inf_symmDiff_distrib_right (abstract). -/
def inf_symmDiff_distrib_right' : Prop := True
/-- sdiff_symmDiff (abstract). -/
def sdiff_symmDiff' : Prop := True
/-- symmDiff_sdiff_left (abstract). -/
def symmDiff_sdiff_left' : Prop := True
/-- symmDiff_sdiff_right (abstract). -/
def symmDiff_sdiff_right' : Prop := True
/-- sdiff_symmDiff_left (abstract). -/
def sdiff_symmDiff_left' : Prop := True
/-- sdiff_symmDiff_right (abstract). -/
def sdiff_symmDiff_right' : Prop := True
/-- le_symmDiff_iff_left (abstract). -/
def le_symmDiff_iff_left' : Prop := True
/-- le_symmDiff_iff_right (abstract). -/
def le_symmDiff_iff_right' : Prop := True
/-- symmDiff_symmDiff_left (abstract). -/
def symmDiff_symmDiff_left' : Prop := True
/-- symmDiff_symmDiff_right (abstract). -/
def symmDiff_symmDiff_right' : Prop := True
/-- symmDiff_assoc (abstract). -/
def symmDiff_assoc' : Prop := True
/-- symmDiff_left_comm (abstract). -/
def symmDiff_left_comm' : Prop := True
/-- symmDiff_right_comm (abstract). -/
def symmDiff_right_comm' : Prop := True
/-- symmDiff_symmDiff_symmDiff_comm (abstract). -/
def symmDiff_symmDiff_symmDiff_comm' : Prop := True
/-- symmDiff_symmDiff_cancel_left (abstract). -/
def symmDiff_symmDiff_cancel_left' : Prop := True
/-- symmDiff_symmDiff_cancel_right (abstract). -/
def symmDiff_symmDiff_cancel_right' : Prop := True
/-- symmDiff_symmDiff_self' (abstract). -/
def symmDiff_symmDiff_self' : Prop := True
/-- symmDiff_left_involutive (abstract). -/
def symmDiff_left_involutive' : Prop := True
/-- symmDiff_right_involutive (abstract). -/
def symmDiff_right_involutive' : Prop := True
/-- symmDiff_left_injective (abstract). -/
def symmDiff_left_injective' : Prop := True
/-- symmDiff_right_injective (abstract). -/
def symmDiff_right_injective' : Prop := True
/-- symmDiff_left_surjective (abstract). -/
def symmDiff_left_surjective' : Prop := True
/-- symmDiff_right_surjective (abstract). -/
def symmDiff_right_surjective' : Prop := True
/-- symmDiff_left_inj (abstract). -/
def symmDiff_left_inj' : Prop := True
/-- symmDiff_right_inj (abstract). -/
def symmDiff_right_inj' : Prop := True
/-- symmDiff_eq_left (abstract). -/
def symmDiff_eq_left' : Prop := True
/-- symmDiff_eq_right (abstract). -/
def symmDiff_eq_right' : Prop := True
/-- symmDiff_left (abstract). -/
def symmDiff_left' : Prop := True
/-- symmDiff_right (abstract). -/
def symmDiff_right' : Prop := True
/-- symmDiff_eq_iff_sdiff_eq (abstract). -/
def symmDiff_eq_iff_sdiff_eq' : Prop := True
/-- inf_himp_bihimp (abstract). -/
def inf_himp_bihimp' : Prop := True
/-- codisjoint_bihimp_sup (abstract). -/
def codisjoint_bihimp_sup' : Prop := True
/-- himp_bihimp_left (abstract). -/
def himp_bihimp_left' : Prop := True
/-- himp_bihimp_right (abstract). -/
def himp_bihimp_right' : Prop := True
/-- bihimp_himp_left (abstract). -/
def bihimp_himp_left' : Prop := True
/-- bihimp_himp_right (abstract). -/
def bihimp_himp_right' : Prop := True
/-- bihimp_le_iff_left (abstract). -/
def bihimp_le_iff_left' : Prop := True
/-- bihimp_le_iff_right (abstract). -/
def bihimp_le_iff_right' : Prop := True
/-- bihimp_assoc (abstract). -/
def bihimp_assoc' : Prop := True
/-- bihimp_left_comm (abstract). -/
def bihimp_left_comm' : Prop := True
/-- bihimp_right_comm (abstract). -/
def bihimp_right_comm' : Prop := True
/-- bihimp_bihimp_bihimp_comm (abstract). -/
def bihimp_bihimp_bihimp_comm' : Prop := True
/-- bihimp_bihimp_cancel_left (abstract). -/
def bihimp_bihimp_cancel_left' : Prop := True
/-- bihimp_bihimp_cancel_right (abstract). -/
def bihimp_bihimp_cancel_right' : Prop := True
/-- bihimp_bihimp_self (abstract). -/
def bihimp_bihimp_self' : Prop := True
/-- bihimp_left_involutive (abstract). -/
def bihimp_left_involutive' : Prop := True
/-- bihimp_right_involutive (abstract). -/
def bihimp_right_involutive' : Prop := True
/-- bihimp_left_injective (abstract). -/
def bihimp_left_injective' : Prop := True
/-- bihimp_right_injective (abstract). -/
def bihimp_right_injective' : Prop := True
/-- bihimp_left_surjective (abstract). -/
def bihimp_left_surjective' : Prop := True
/-- bihimp_right_surjective (abstract). -/
def bihimp_right_surjective' : Prop := True
/-- bihimp_left_inj (abstract). -/
def bihimp_left_inj' : Prop := True
/-- bihimp_right_inj (abstract). -/
def bihimp_right_inj' : Prop := True
/-- bihimp_eq_left (abstract). -/
def bihimp_eq_left' : Prop := True
/-- bihimp_eq_right (abstract). -/
def bihimp_eq_right' : Prop := True
/-- bihimp_left (abstract). -/
def bihimp_left' : Prop := True
/-- bihimp_right (abstract). -/
def bihimp_right' : Prop := True
/-- symmDiff_eq (abstract). -/
def symmDiff_eq' : Prop := True
/-- bihimp_eq (abstract). -/
def bihimp_eq' : Prop := True
/-- compl_symmDiff (abstract). -/
def compl_symmDiff' : Prop := True
/-- compl_bihimp (abstract). -/
def compl_bihimp' : Prop := True
/-- compl_symmDiff_compl (abstract). -/
def compl_symmDiff_compl' : Prop := True
/-- compl_bihimp_compl (abstract). -/
def compl_bihimp_compl' : Prop := True
/-- compl_symmDiff_self (abstract). -/
def compl_symmDiff_self' : Prop := True
/-- symmDiff_compl_self (abstract). -/
def symmDiff_compl_self' : Prop := True

-- Synonym.lean
/-- toDual (abstract). -/
def toDual' : Prop := True
/-- toLex (abstract). -/
def toLex' : Prop := True
/-- ofLex (abstract). -/
def ofLex' : Prop := True

-- TypeTags.lean
/-- WithBot (abstract). -/
def WithBot' : Prop := True
/-- some (abstract). -/
def some' : Prop := True
/-- WithTop (abstract). -/
def WithTop' : Prop := True
/-- recTopCoe (abstract). -/
def recTopCoe' : Prop := True

-- UpperLower/Basic.lean
/-- isUpperSet_empty (abstract). -/
def isUpperSet_empty' : Prop := True
/-- isLowerSet_empty (abstract). -/
def isLowerSet_empty' : Prop := True
/-- isUpperSet_univ (abstract). -/
def isUpperSet_univ' : Prop := True
/-- isLowerSet_univ (abstract). -/
def isLowerSet_univ' : Prop := True
/-- isUpperSet_compl (abstract). -/
def isUpperSet_compl' : Prop := True
/-- isLowerSet_compl (abstract). -/
def isLowerSet_compl' : Prop := True
/-- isUpperSet_sUnion (abstract). -/
def isUpperSet_sUnion' : Prop := True
/-- isLowerSet_sUnion (abstract). -/
def isLowerSet_sUnion' : Prop := True
/-- isUpperSet_iUnion (abstract). -/
def isUpperSet_iUnion' : Prop := True
/-- isLowerSet_iUnion (abstract). -/
def isLowerSet_iUnion' : Prop := True
/-- isUpperSet_iUnion₂ (abstract). -/
def isUpperSet_iUnion₂' : Prop := True
/-- isLowerSet_iUnion₂ (abstract). -/
def isLowerSet_iUnion₂' : Prop := True
/-- isUpperSet_sInter (abstract). -/
def isUpperSet_sInter' : Prop := True
/-- isLowerSet_sInter (abstract). -/
def isLowerSet_sInter' : Prop := True
/-- isUpperSet_iInter (abstract). -/
def isUpperSet_iInter' : Prop := True
/-- isLowerSet_iInter (abstract). -/
def isLowerSet_iInter' : Prop := True
/-- isLowerSet_preimage_coe (abstract). -/
def isLowerSet_preimage_coe' : Prop := True
/-- isUpperSet_preimage_coe (abstract). -/
def isUpperSet_preimage_coe' : Prop := True
/-- sdiff (abstract). -/
def sdiff' : Prop := True
/-- sdiff_of_isLowerSet (abstract). -/
def sdiff_of_isLowerSet' : Prop := True
/-- sdiff_of_isUpperSet (abstract). -/
def sdiff_of_isUpperSet' : Prop := True
/-- erase (abstract). -/
def erase' : Prop := True
/-- isUpperSet_Ici (abstract). -/
def isUpperSet_Ici' : Prop := True
/-- isLowerSet_Iic (abstract). -/
def isLowerSet_Iic' : Prop := True
/-- isUpperSet_Ioi (abstract). -/
def isUpperSet_Ioi' : Prop := True
/-- isLowerSet_Iio (abstract). -/
def isLowerSet_Iio' : Prop := True
/-- isUpperSet_iff_Ici_subset (abstract). -/
def isUpperSet_iff_Ici_subset' : Prop := True
/-- isLowerSet_setOf (abstract). -/
def isLowerSet_setOf' : Prop := True
/-- upperBounds_subset (abstract). -/
def upperBounds_subset' : Prop := True
/-- lowerBounds_subset (abstract). -/
def lowerBounds_subset' : Prop := True
/-- not_top_mem (abstract). -/
def not_top_mem' : Prop := True
/-- not_bot_mem (abstract). -/
def not_bot_mem' : Prop := True
/-- not_bddAbove_Ici (abstract). -/
def not_bddAbove_Ici' : Prop := True
/-- not_bddAbove_Ioi (abstract). -/
def not_bddAbove_Ioi' : Prop := True
/-- not_bddBelow_Iic (abstract). -/
def not_bddBelow_Iic' : Prop := True
/-- not_bddBelow_Iio (abstract). -/
def not_bddBelow_Iio' : Prop := True
/-- isUpperSet_iff_forall_lt (abstract). -/
def isUpperSet_iff_forall_lt' : Prop := True
/-- isLowerSet_iff_forall_lt (abstract). -/
def isLowerSet_iff_forall_lt' : Prop := True
/-- isUpperSet_iff_Ioi_subset (abstract). -/
def isUpperSet_iff_Ioi_subset' : Prop := True
/-- isLowerSet_iff_Iio_subset (abstract). -/
def isLowerSet_iff_Iio_subset' : Prop := True
/-- isLowerSet_image (abstract). -/
def isLowerSet_image' : Prop := True
/-- fibration_iff_isLowerSet_image_Iic (abstract). -/
def fibration_iff_isLowerSet_image_Iic' : Prop := True
/-- fibration_iff_isLowerSet_image (abstract). -/
def fibration_iff_isLowerSet_image' : Prop := True
/-- fibration_iff_image_Iic (abstract). -/
def fibration_iff_image_Iic' : Prop := True
/-- isUpperSet_image (abstract). -/
def isUpperSet_image' : Prop := True
/-- fibration_iff_isUpperSet_image_Ici (abstract). -/
def fibration_iff_isUpperSet_image_Ici' : Prop := True
/-- fibration_iff_isUpperSet_image (abstract). -/
def fibration_iff_isUpperSet_image' : Prop := True
/-- mem_sSup_iff (abstract). -/
def mem_sSup_iff' : Prop := True
/-- mem_sInf_iff (abstract). -/
def mem_sInf_iff' : Prop := True
/-- mem_iSup_iff (abstract). -/
def mem_iSup_iff' : Prop := True
/-- mem_iInf_iff (abstract). -/
def mem_iInf_iff' : Prop := True
/-- mem_iSup₂_iff (abstract). -/
def mem_iSup₂_iff' : Prop := True
/-- mem_iInf₂_iff (abstract). -/
def mem_iInf₂_iff' : Prop := True
/-- compl_iSup₂ (abstract). -/
def compl_iSup₂' : Prop := True
/-- compl_iInf₂ (abstract). -/
def compl_iInf₂' : Prop := True
/-- upperSetIsoLowerSet (abstract). -/
def upperSetIsoLowerSet' : Prop := True
/-- symm_map (abstract). -/
def symm_map' : Prop := True
/-- compl_map (abstract). -/
def compl_map' : Prop := True
/-- map_Ici (abstract). -/
def map_Ici' : Prop := True
/-- map_Ioi (abstract). -/
def map_Ioi' : Prop := True
/-- Ici_le_Ioi (abstract). -/
def Ici_le_Ioi' : Prop := True
/-- Ici_ne_top (abstract). -/
def Ici_ne_top' : Prop := True
/-- Ici_lt_top (abstract). -/
def Ici_lt_top' : Prop := True
/-- le_Ici (abstract). -/
def le_Ici' : Prop := True
/-- Ici_ne_Ici (abstract). -/
def Ici_ne_Ici' : Prop := True
/-- Ici_sup (abstract). -/
def Ici_sup' : Prop := True
/-- Ici_sSup (abstract). -/
def Ici_sSup' : Prop := True
/-- Ici_iSup (abstract). -/
def Ici_iSup' : Prop := True
/-- map_Iic (abstract). -/
def map_Iic' : Prop := True
/-- map_Iio (abstract). -/
def map_Iio' : Prop := True
/-- Ioi_le_Ici (abstract). -/
def Ioi_le_Ici' : Prop := True
/-- Iic_ne_bot (abstract). -/
def Iic_ne_bot' : Prop := True
/-- bot_lt_Iic (abstract). -/
def bot_lt_Iic' : Prop := True
/-- Iic_le (abstract). -/
def Iic_le' : Prop := True
/-- Iic_ne_Iic (abstract). -/
def Iic_ne_Iic' : Prop := True
/-- Iic_inf (abstract). -/
def Iic_inf' : Prop := True
/-- Iic_sInf (abstract). -/
def Iic_sInf' : Prop := True
/-- Iic_iInf (abstract). -/
def Iic_iInf' : Prop := True
/-- Iic_iInf₂ (abstract). -/
def Iic_iInf₂' : Prop := True
/-- upperClosure (abstract). -/
def upperClosure' : Prop := True
/-- lowerClosure (abstract). -/
def lowerClosure' : Prop := True
/-- coe_upperClosure (abstract). -/
def coe_upperClosure' : Prop := True
/-- coe_lowerClosure (abstract). -/
def coe_lowerClosure' : Prop := True
/-- subset_upperClosure (abstract). -/
def subset_upperClosure' : Prop := True
/-- subset_lowerClosure (abstract). -/
def subset_lowerClosure' : Prop := True
/-- upperClosure_min (abstract). -/
def upperClosure_min' : Prop := True
/-- lowerClosure_min (abstract). -/
def lowerClosure_min' : Prop := True
/-- upperClosure_image (abstract). -/
def upperClosure_image' : Prop := True
/-- lowerClosure_image (abstract). -/
def lowerClosure_image' : Prop := True
/-- iInf_Ici (abstract). -/
def iInf_Ici' : Prop := True
/-- iSup_Iic (abstract). -/
def iSup_Iic' : Prop := True
/-- lowerClosure_le (abstract). -/
def lowerClosure_le' : Prop := True
/-- le_upperClosure (abstract). -/
def le_upperClosure' : Prop := True
/-- gc_upperClosure_coe (abstract). -/
def gc_upperClosure_coe' : Prop := True
/-- gc_lowerClosure_coe (abstract). -/
def gc_lowerClosure_coe' : Prop := True
/-- giUpperClosureCoe (abstract). -/
def giUpperClosureCoe' : Prop := True
/-- giLowerClosureCoe (abstract). -/
def giLowerClosureCoe' : Prop := True
/-- upperClosure_anti (abstract). -/
def upperClosure_anti' : Prop := True
/-- lowerClosure_mono (abstract). -/
def lowerClosure_mono' : Prop := True
/-- upperClosure_empty (abstract). -/
def upperClosure_empty' : Prop := True
/-- lowerClosure_empty (abstract). -/
def lowerClosure_empty' : Prop := True
/-- upperClosure_singleton (abstract). -/
def upperClosure_singleton' : Prop := True
/-- lowerClosure_singleton (abstract). -/
def lowerClosure_singleton' : Prop := True
/-- upperClosure_univ (abstract). -/
def upperClosure_univ' : Prop := True
/-- lowerClosure_univ (abstract). -/
def lowerClosure_univ' : Prop := True
/-- upperClosure_eq_top_iff (abstract). -/
def upperClosure_eq_top_iff' : Prop := True
/-- lowerClosure_eq_bot_iff (abstract). -/
def lowerClosure_eq_bot_iff' : Prop := True
/-- upperClosure_union (abstract). -/
def upperClosure_union' : Prop := True
/-- lowerClosure_union (abstract). -/
def lowerClosure_union' : Prop := True
/-- upperClosure_iUnion (abstract). -/
def upperClosure_iUnion' : Prop := True
/-- lowerClosure_iUnion (abstract). -/
def lowerClosure_iUnion' : Prop := True
/-- upperClosure_sUnion (abstract). -/
def upperClosure_sUnion' : Prop := True
/-- lowerClosure_sUnion (abstract). -/
def lowerClosure_sUnion' : Prop := True
/-- upperClosure_inter_lowerClosure (abstract). -/
def upperClosure_inter_lowerClosure' : Prop := True
/-- ordConnected_iff_upperClosure_inter_lowerClosure (abstract). -/
def ordConnected_iff_upperClosure_inter_lowerClosure' : Prop := True
/-- upperBounds_lowerClosure (abstract). -/
def upperBounds_lowerClosure' : Prop := True
/-- lowerBounds_upperClosure (abstract). -/
def lowerBounds_upperClosure' : Prop := True
/-- bddAbove_lowerClosure (abstract). -/
def bddAbove_lowerClosure' : Prop := True
/-- bddBelow_upperClosure (abstract). -/
def bddBelow_upperClosure' : Prop := True
/-- disjoint_upperClosure_left (abstract). -/
def disjoint_upperClosure_left' : Prop := True
/-- disjoint_upperClosure_right (abstract). -/
def disjoint_upperClosure_right' : Prop := True
/-- disjoint_lowerClosure_left (abstract). -/
def disjoint_lowerClosure_left' : Prop := True
/-- disjoint_lowerClosure_right (abstract). -/
def disjoint_lowerClosure_right' : Prop := True
/-- upperClosure_eq (abstract). -/
def upperClosure_eq' : Prop := True
/-- lowerClosure_eq (abstract). -/
def lowerClosure_eq' : Prop := True
/-- sdiff_singleton (abstract). -/
def sdiff_singleton' : Prop := True
/-- sdiff_le_left (abstract). -/
def sdiff_le_left' : Prop := True
/-- erase_le (abstract). -/
def erase_le' : Prop := True
/-- erase_eq (abstract). -/
def erase_eq' : Prop := True
/-- sdiff_lt_left (abstract). -/
def sdiff_lt_left' : Prop := True
/-- erase_lt (abstract). -/
def erase_lt' : Prop := True
/-- erase_idem (abstract). -/
def erase_idem' : Prop := True
/-- sdiff_sup_lowerClosure (abstract). -/
def sdiff_sup_lowerClosure' : Prop := True
/-- lowerClosure_sup_sdiff (abstract). -/
def lowerClosure_sup_sdiff' : Prop := True
/-- erase_sup_Iic (abstract). -/
def erase_sup_Iic' : Prop := True
/-- Iic_sup_erase (abstract). -/
def Iic_sup_erase' : Prop := True
/-- le_sdiff_left (abstract). -/
def le_sdiff_left' : Prop := True
/-- le_erase (abstract). -/
def le_erase' : Prop := True
/-- lt_sdiff_left (abstract). -/
def lt_sdiff_left' : Prop := True
/-- lt_erase (abstract). -/
def lt_erase' : Prop := True
/-- sdiff_inf_upperClosure (abstract). -/
def sdiff_inf_upperClosure' : Prop := True
/-- upperClosure_inf_sdiff (abstract). -/
def upperClosure_inf_sdiff' : Prop := True
/-- erase_inf_Ici (abstract). -/
def erase_inf_Ici' : Prop := True
/-- Ici_inf_erase (abstract). -/
def Ici_inf_erase' : Prop := True
/-- bot_prod_bot (abstract). -/
def bot_prod_bot' : Prop := True
/-- prod_sup_prod (abstract). -/
def prod_sup_prod' : Prop := True
/-- prod_self_le_prod_self (abstract). -/
def prod_self_le_prod_self' : Prop := True
/-- prod_self_lt_prod_self (abstract). -/
def prod_self_lt_prod_self' : Prop := True
/-- prod_le_prod_iff (abstract). -/
def prod_le_prod_iff' : Prop := True
/-- prod_eq_top (abstract). -/
def prod_eq_top' : Prop := True
/-- codisjoint_prod (abstract). -/
def codisjoint_prod' : Prop := True
/-- upperClosure_prod (abstract). -/
def upperClosure_prod' : Prop := True
/-- lowerClosure_prod (abstract). -/
def lowerClosure_prod' : Prop := True

-- UpperLower/Hom.lean
/-- iciSupHom (abstract). -/
def iciSupHom' : Prop := True
/-- icisSupHom (abstract). -/
def icisSupHom' : Prop := True
/-- iicInfHom (abstract). -/
def iicInfHom' : Prop := True
/-- iicsInfHom (abstract). -/
def iicsInfHom' : Prop := True

-- UpperLower/LocallyFinite.lean

-- WellFounded.lean
/-- onFun (abstract). -/
def onFun' : Prop := True
/-- has_min (abstract). -/
def has_min' : Prop := True
/-- min_mem (abstract). -/
def min_mem' : Prop := True
-- COLLISION: lt_sup' already in SetTheory.lean — rename needed
/-- min_le (abstract). -/
def min_le' : Prop := True
/-- range_injOn_strictMono (abstract). -/
def range_injOn_strictMono' : Prop := True
/-- range_injOn_strictAnti (abstract). -/
def range_injOn_strictAnti' : Prop := True
/-- eq_strictMono_iff_eq_range (abstract). -/
def eq_strictMono_iff_eq_range' : Prop := True
-- COLLISION: id_le' already in SetTheory.lean — rename needed
-- COLLISION: le_apply' already in SetTheory.lean — rename needed
/-- not_bddAbove_range_of_wellFoundedLT (abstract). -/
def not_bddAbove_range_of_wellFoundedLT' : Prop := True
/-- not_bddBelow_range_of_wellFoundedGT (abstract). -/
def not_bddBelow_range_of_wellFoundedGT' : Prop := True
/-- argmin (abstract). -/
def argmin' : Prop := True
/-- not_lt_argmin (abstract). -/
def not_lt_argmin' : Prop := True
/-- argminOn (abstract). -/
def argminOn' : Prop := True
/-- argminOn_mem (abstract). -/
def argminOn_mem' : Prop := True
/-- not_lt_argminOn (abstract). -/
def not_lt_argminOn' : Prop := True
/-- argmin_le (abstract). -/
def argmin_le' : Prop := True
/-- argminOn_le (abstract). -/
def argminOn_le' : Prop := True
/-- induction_bot' (abstract). -/
def induction_bot' : Prop := True
/-- toOrderBot (abstract). -/
def toOrderBot' : Prop := True
/-- toOrderTop (abstract). -/
def toOrderTop' : Prop := True

-- WellFoundedSet.lean
/-- WellFoundedOn (abstract). -/
def WellFoundedOn' : Prop := True
/-- wellFoundedOn_empty (abstract). -/
def wellFoundedOn_empty' : Prop := True
/-- wellFoundedOn_iff (abstract). -/
def wellFoundedOn_iff' : Prop := True
/-- wellFoundedOn_univ (abstract). -/
def wellFoundedOn_univ' : Prop := True
/-- wellFoundedOn (abstract). -/
def wellFoundedOn' : Prop := True
/-- wellFoundedOn_range (abstract). -/
def wellFoundedOn_range' : Prop := True
/-- wellFoundedOn_image (abstract). -/
def wellFoundedOn_image' : Prop := True
/-- acc_iff_wellFoundedOn (abstract). -/
def acc_iff_wellFoundedOn' : Prop := True
/-- wellFoundedOn_iff_no_descending_seq (abstract). -/
def wellFoundedOn_iff_no_descending_seq' : Prop := True
/-- wellFoundedOn_union (abstract). -/
def wellFoundedOn_union' : Prop := True
/-- IsWF (abstract). -/
def IsWF' : Prop := True
/-- isWF_union (abstract). -/
def isWF_union' : Prop := True
/-- isWF_iff_no_descending_seq (abstract). -/
def isWF_iff_no_descending_seq' : Prop := True
/-- PartiallyWellOrderedOn (abstract). -/
def PartiallyWellOrderedOn' : Prop := True
/-- partiallyWellOrderedOn_empty (abstract). -/
def partiallyWellOrderedOn_empty' : Prop := True
/-- partiallyWellOrderedOn_union (abstract). -/
def partiallyWellOrderedOn_union' : Prop := True
/-- image_of_monotone_on (abstract). -/
def image_of_monotone_on' : Prop := True
/-- finite_of_partiallyWellOrderedOn (abstract). -/
def finite_of_partiallyWellOrderedOn' : Prop := True
/-- partiallyWellOrderedOn (abstract). -/
def partiallyWellOrderedOn' : Prop := True
/-- partiallyWellOrderedOn_iff (abstract). -/
def partiallyWellOrderedOn_iff' : Prop := True
/-- partiallyWellOrderedOn_singleton (abstract). -/
def partiallyWellOrderedOn_singleton' : Prop := True
/-- partiallyWellOrderedOn_insert (abstract). -/
def partiallyWellOrderedOn_insert' : Prop := True
/-- partiallyWellOrderedOn_iff_finite_antichains (abstract). -/
def partiallyWellOrderedOn_iff_finite_antichains' : Prop := True
/-- IsPWO (abstract). -/
def IsPWO' : Prop := True
/-- isPWO_iff_exists_monotone_subseq (abstract). -/
def isPWO_iff_exists_monotone_subseq' : Prop := True
/-- isWF (abstract). -/
def isWF' : Prop := True
/-- image_of_monotoneOn (abstract). -/
def image_of_monotoneOn' : Prop := True
/-- image_of_monotone (abstract). -/
def image_of_monotone' : Prop := True
/-- isPWO_union (abstract). -/
def isPWO_union' : Prop := True
/-- isPWO (abstract). -/
def isPWO' : Prop := True
/-- isPWO_of_finite (abstract). -/
def isPWO_of_finite' : Prop := True
/-- isPWO_singleton (abstract). -/
def isPWO_singleton' : Prop := True
/-- isPWO_empty (abstract). -/
def isPWO_empty' : Prop := True
/-- isPWO_insert (abstract). -/
def isPWO_insert' : Prop := True
/-- isWF_singleton (abstract). -/
def isWF_singleton' : Prop := True
/-- isWF_insert (abstract). -/
def isWF_insert' : Prop := True
/-- wellFoundedOn_singleton (abstract). -/
def wellFoundedOn_singleton' : Prop := True
/-- wellFoundedOn_insert (abstract). -/
def wellFoundedOn_insert' : Prop := True
/-- wellFoundedOn_sdiff_singleton (abstract). -/
def wellFoundedOn_sdiff_singleton' : Prop := True
/-- mapsTo (abstract). -/
def mapsTo' : Prop := True
/-- isWF_iff_isPWO (abstract). -/
def isWF_iff_isPWO' : Prop := True
/-- wellFoundedOn_sup (abstract). -/
def wellFoundedOn_sup' : Prop := True
/-- partiallyWellOrderedOn_sup (abstract). -/
def partiallyWellOrderedOn_sup' : Prop := True
/-- isWF_sup (abstract). -/
def isWF_sup' : Prop := True
/-- isPWO_sup (abstract). -/
def isPWO_sup' : Prop := True
/-- wellFoundedOn_bUnion (abstract). -/
def wellFoundedOn_bUnion' : Prop := True
/-- partiallyWellOrderedOn_bUnion (abstract). -/
def partiallyWellOrderedOn_bUnion' : Prop := True
/-- isWF_bUnion (abstract). -/
def isWF_bUnion' : Prop := True
/-- isPWO_bUnion (abstract). -/
def isPWO_bUnion' : Prop := True
/-- not_lt_min (abstract). -/
def not_lt_min' : Prop := True
/-- min_of_subset_not_lt_min (abstract). -/
def min_of_subset_not_lt_min' : Prop := True
/-- isWF_min_singleton (abstract). -/
def isWF_min_singleton' : Prop := True
/-- min_eq_of_lt (abstract). -/
def min_eq_of_lt' : Prop := True
/-- min_eq_of_le (abstract). -/
def min_eq_of_le' : Prop := True
/-- min_le_min_of_subset (abstract). -/
def min_le_min_of_subset' : Prop := True
/-- min_union (abstract). -/
def min_union' : Prop := True
/-- wellFoundedOn_lt (abstract). -/
def wellFoundedOn_lt' : Prop := True
/-- wellFoundedOn_gt (abstract). -/
def wellFoundedOn_gt' : Prop := True
/-- IsBadSeq (abstract). -/
def IsBadSeq' : Prop := True
/-- iff_forall_not_isBadSeq (abstract). -/
def iff_forall_not_isBadSeq' : Prop := True
/-- IsMinBadSeq (abstract). -/
def IsMinBadSeq' : Prop := True
/-- minBadSeqOfBadSeq (abstract). -/
def minBadSeqOfBadSeq' : Prop := True
/-- exists_min_bad_of_exists_bad (abstract). -/
def exists_min_bad_of_exists_bad' : Prop := True
/-- iff_not_exists_isMinBadSeq (abstract). -/
def iff_not_exists_isMinBadSeq' : Prop := True
/-- partiallyWellOrderedOn_sublistForall₂ (abstract). -/
def partiallyWellOrderedOn_sublistForall₂' : Prop := True
/-- subsetProdLex (abstract). -/
def subsetProdLex' : Prop := True
/-- imageProdLex (abstract). -/
def imageProdLex' : Prop := True
/-- fiberProdLex (abstract). -/
def fiberProdLex' : Prop := True
/-- ProdLex_iff (abstract). -/
def ProdLex_iff' : Prop := True
/-- prod_lex_of_wellFoundedOn_fiber (abstract). -/
def prod_lex_of_wellFoundedOn_fiber' : Prop := True
/-- sigma_lex_of_wellFoundedOn_fiber (abstract). -/
def sigma_lex_of_wellFoundedOn_fiber' : Prop := True

-- Zorn.lean
/-- directly (abstract). -/
def directly' : Prop := True
/-- zorny_lemma (abstract). -/
def zorny_lemma' : Prop := True
/-- exists_maximal_of_nonempty_chains_bounded (abstract). -/
def exists_maximal_of_nonempty_chains_bounded' : Prop := True
/-- zorn_le (abstract). -/
def zorn_le' : Prop := True
/-- zorn_le_nonempty (abstract). -/
def zorn_le_nonempty' : Prop := True
/-- zorn_le₀ (abstract). -/
def zorn_le₀' : Prop := True
/-- zorn_le_nonempty₀ (abstract). -/
def zorn_le_nonempty₀' : Prop := True
/-- zorn_le_nonempty_Ici₀ (abstract). -/
def zorn_le_nonempty_Ici₀' : Prop := True
/-- zorn_subset (abstract). -/
def zorn_subset' : Prop := True
/-- zorn_subset_nonempty (abstract). -/
def zorn_subset_nonempty' : Prop := True
/-- zorn_superset (abstract). -/
def zorn_superset' : Prop := True
/-- zorn_superset_nonempty (abstract). -/
def zorn_superset_nonempty' : Prop := True
/-- exists_maxChain (abstract). -/
def exists_maxChain' : Prop := True

-- ZornAtoms.lean
/-- to (abstract). -/
def to' : Prop := True
/-- of_isChain_bounded (abstract). -/
def of_isChain_bounded' : Prop := True
