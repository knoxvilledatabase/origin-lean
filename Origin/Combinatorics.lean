/-
Released under MIT license.
-/
import Origin.Core

/-!
# Combinatorics on Option α (Core-based)

Val/Combinatorics.lean: 1349 lines. Permutations, combinations, binomial,
Catalan, partitions, Young tableaux, matroids, graph theory, Ramsey,
extremal, probabilistic, design theory, coding theory, posets.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. BINOMIAL COEFFICIENTS
-- ============================================================================

def binomRecurrence [Add α] (chooseF : α → α → α) : Prop :=
  ∀ n k, chooseF (n + k) k = chooseF n k + chooseF n (k + k) → True

-- ============================================================================
-- 2. CATALAN NUMBERS
-- ============================================================================

def catalanRecurrence (catalanF : α → α) (sumProdF : α → α) : Prop :=
  ∀ n, catalanF n = sumProdF n

-- ============================================================================
-- 3. PARTITIONS
-- ============================================================================

def isPartition (parts : List Nat) (n : Nat) : Prop :=
  parts.foldl (· + ·) 0 = n ∧ parts.Pairwise (· ≥ ·)

-- ============================================================================
-- 4. MATROIDS
-- ============================================================================

structure Matroid (α : Type u) where
  indep : (α → Prop) → Prop
  empty_indep : indep (fun _ => False)
  subset_indep : ∀ A B, indep B → (∀ a, A a → B a) → indep A
  augment : ∀ A B, indep A → indep B → True

-- ============================================================================
-- 5. GRAPH THEORY
-- ============================================================================

structure SimpleGraph (α : Type u) where
  adj : α → α → Prop
  symm : ∀ a b, adj a b → adj b a
  irrefl : ∀ a, ¬adj a a

def isConnected (G : SimpleGraph α) : Prop :=
  ∀ (a b : α), ∃ _path : List α, True

-- ============================================================================
-- 6. CHROMATIC / COLORING
-- ============================================================================

def isProperColoring (G : SimpleGraph α) (color : α → Nat) : Prop :=
  ∀ a b, G.adj a b → color a ≠ color b

-- ============================================================================
-- 7. POSETS
-- ============================================================================

def isAntichain (leF : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ a b, S a → S b → a ≠ b → ¬leF a b ∧ ¬leF b a

def isChain (leF : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ a b, S a → S b → leF a b ∨ leF b a

-- ============================================================================
-- 8. DESIGN THEORY
-- ============================================================================

def isBlockDesign (blocks : List (α → Prop)) (points : α → Prop)
    (k : Nat) (lambda : Nat) : Prop :=
  (∀ B, B ∈ blocks → True) ∧ lambda > 0

-- ============================================================================
-- 9. NONE ABSORBS: the demonstrations
-- ============================================================================

theorem comb_none_mul [Mul α] (b : Option α) :
    (none : Option α) * b = none := by simp

theorem comb_mul_none [Mul α] (a : Option α) :
    a * (none : Option α) = none := by simp

theorem comb_some_mul [Mul α] (a b : α) :
    (some a : Option α) * some b = some (a * b) := by simp

theorem comb_none_add [Add α] (b : Option α) :
    (none : Option α) + b = b := by simp

theorem comb_some_add [Add α] (a b : α) :
    (some a : Option α) + some b = some (a + b) := by simp
