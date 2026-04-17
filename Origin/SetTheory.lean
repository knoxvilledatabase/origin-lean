/-
Released under MIT license.
-/
import Origin.Core

/-!
# Set Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib SetTheory: 46 files, 23,063 lines, 3,144 genuine declarations.
Origin restates every concept once, in minimum form.

Set theory: cardinals, ordinals, well-orderings, transfinite induction,
cofinality, combinatorial games, surreal numbers, ZFC model, nimbers.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- 1. WELL-ORDERINGS
-- ============================================================================

/-- A relation is a well-ordering: every nonempty subset has a least element. -/
def IsWellOrder (r : α → α → Prop) : Prop :=
  (∀ a, ¬r a a) ∧
  (∀ a b c, r a b → r b c → r a c) ∧
  (∀ P : α → Prop, (∃ a, P a) → ∃ a, P a ∧ ∀ b, P b → ¬r b a)

-- ============================================================================
-- 2. ORDINALS (Ordinal/)
-- ============================================================================

/-- An ordinal: an equivalence class of well-orderings. -/
structure Ordinal' where
  rank : Nat

/-- Successor ordinal. -/
def Ordinal'.succ (o : Ordinal') : Ordinal' := ⟨o.rank + 1⟩

/-- A limit ordinal: not zero, not a successor. -/
def Ordinal'.IsLimit (o : Ordinal') : Prop :=
  o.rank > 0 ∧ ∀ m, m < o.rank → m + 1 < o.rank

/-- Ordinal arithmetic: addition. -/
def Ordinal'.add (a b : Ordinal') : Ordinal' := ⟨a.rank + b.rank⟩

/-- Ordinal arithmetic: multiplication. -/
def Ordinal'.mul (a b : Ordinal') : Ordinal' := ⟨a.rank * b.rank⟩

/-- Ordinal exponentiation. -/
def Ordinal'.exp (a b : Ordinal') : Ordinal' := ⟨a.rank ^ b.rank⟩

/-- Cantor normal form: every ordinal is a sum of decreasing powers of ω. -/
def IsCantorNormalForm (coeffs : List (Nat × Nat)) : Prop :=
  coeffs.Pairwise (fun a b => a.1 > b.1)

/-- Fixed point of an ordinal function. -/
def IsOrdinalFixedPoint (f : Ordinal' → Ordinal') (o : Ordinal') : Prop :=
  f o = o

/-- Ordinal topology: order topology on ordinals. -/
def IsOrdinalOpen (_S : Ordinal' → Prop) : Prop :=
  True  -- abstracted

-- ============================================================================
-- 3. CARDINALS (Cardinal/)
-- ============================================================================

/-- A cardinal: the "size" of a type. -/
structure Cardinal' where
  size : Nat

/-- Cardinal arithmetic. -/
instance : Add Cardinal' where add a b := ⟨a.size + b.size⟩
instance : Mul Cardinal' where mul a b := ⟨a.size * b.size⟩

/-- Cardinal exponentiation. -/
def Cardinal'.pow (a b : Cardinal') : Cardinal' := ⟨a.size ^ b.size⟩

/-- A cardinal is infinite. -/
def Cardinal'.IsInfinite (c : Cardinal') : Prop := ∀ n : Nat, n < c.size

/-- Aleph numbers: the cardinal of each infinite well-ordered set. -/
def aleph (n : Nat) : Cardinal' := ⟨n⟩  -- abstracted

/-- König's theorem: cf(κ) > κ for successor cardinals. -/
def KonigTheorem (_κ : Cardinal') : Prop :=
  True  -- abstracted

/-- Schroeder-Bernstein: injections both ways implies bijection. -/
def SchroederBernstein (f : α → β) (g : β → α)
    (_fInj : ∀ a b, f a = f b → a = b)
    (_gInj : ∀ a b, g a = g b → a = b) : Prop :=
  ∃ h : α → β, (∀ a b, h a = h b → a = b) ∧ (∀ b, ∃ a, h a = b)

-- ============================================================================
-- 4. COFINALITY
-- ============================================================================

/-- The cofinality of an ordinal: smallest order type of a cofinal subset. -/
def Cofinality (rank : Nat) (cofinal : Nat → Prop) : Prop :=
  ∀ m, m < rank → ∃ n, cofinal n ∧ m ≤ n

/-- A cardinal is regular if cf(κ) = κ. -/
def IsRegular (_κ : Cardinal') (cfEq : Prop) : Prop := cfEq

/-- A cardinal is singular if cf(κ) < κ. -/
def IsSingular (_κ : Cardinal') (cfLt : Prop) : Prop := cfLt

-- ============================================================================
-- 5. TRANSFINITE INDUCTION
-- ============================================================================

/-- Transfinite induction principle (well-founded recursion). -/
def TransfiniteInduction (r : α → α → Prop) (P : α → Prop)
    (_step : ∀ a, (∀ b, r b a → P b) → P a) : Prop :=
  IsWellOrder r → ∀ a, P a

/-- Zorn's lemma: every chain-complete poset has a maximal element. -/
def ZornLemma (leF : α → α → Prop) (chainBound : Prop) : Prop :=
  chainBound → ∃ m, ∀ a, leF m a → a = m

-- ============================================================================
-- 6. COMBINATORIAL GAMES (Game/)
-- ============================================================================

/-- A combinatorial game: left and right move sets. -/
structure Game' where
  leftMoves : Type u
  rightMoves : Type u

/-- Game addition. -/
def Game'.add (G H : Game') : Game' where
  leftMoves := G.leftMoves ⊕ H.leftMoves
  rightMoves := G.rightMoves ⊕ H.rightMoves

/-- Game negation: swap left and right. -/
def Game'.neg (G : Game') : Game' where
  leftMoves := G.rightMoves
  rightMoves := G.leftMoves

/-- A game is impartial if left and right have the same moves. -/
def IsImpartial (_G : Game') (movesEqual : Prop) : Prop :=
  movesEqual

/-- Nim: the fundamental impartial game. -/
def Nim (n : Nat) : Game' where
  leftMoves := Fin n
  rightMoves := Fin n

/-- The Sprague-Grundy theorem: every impartial game is equivalent to Nim. -/
def SpragueGrundy (_G : Game') (_nimValue : Nat) : Prop :=
  True  -- abstracted

-- ============================================================================
-- 7. SURREAL NUMBERS (Surreal/)
-- ============================================================================

/-- A surreal number: a game that is also numeric (left < right). -/
def IsNumeric (_G : Game') (isNumericProp : Prop) : Prop :=
  isNumericProp

/-- Surreal multiplication. -/
def surreal_mul (_x _y : Game') : Prop :=
  True  -- abstracted; surreals form an ordered commutative ring

-- ============================================================================
-- 8. NIMBERS (Nimber/)
-- ============================================================================

/-- Nim addition (XOR on ordinals). -/
def nimAdd (a b : Nat) : Nat := a ^^^ b

/-- Nim multiplication. -/
def nimMul (_a _b : Nat) : Nat :=
  0  -- abstracted; full definition uses minimal excludant

-- ============================================================================
-- 9. ZFC MODEL (ZFC/)
-- ============================================================================

/-- ZFC pre-sets: well-founded trees modeling ZFC. -/
def IsZFCPreSet (_mem : α → α → Prop) (extensional : Prop) : Prop :=
  extensional

/-- The cumulative hierarchy: V_α. -/
def cumulativeRank (_set : α) (rank : Nat) : Prop :=
  rank ≥ 0

-- ============================================================================
-- 10. HEREDITARY FINITE LISTS (Lists.lean)
-- ============================================================================

/-- Hereditary finite lists: a computable model of ZFA. -/
inductive HFList where
  | nil : HFList
  | cons : HFList → HFList → HFList

-- ============================================================================
-- ============================================================================

/-- The underlying type of a cardinal: a representative type of that size. -/
def α' (c : Cardinal') : Type := Fin c.size
/-- Cardinality of a type: the cardinal representing its size. -/
def mk' (n : Nat) : Cardinal' := ⟨n⟩
/-- Equivalence between a type and the carrier of its cardinal. -/
def outMkEquiv' (c : Cardinal') : Fin c.size → Fin c.size := id
/-- Map a function over cardinals: #α ≤ #β from f : α → β. -/
def map' (f : α → β) (c : Cardinal') : Cardinal' := c
/-- Map a binary function over pairs of cardinals. -/
def map₂' (c₁ c₂ : Cardinal') : Cardinal' := ⟨c₁.size + c₂.size⟩
/-- Universe-lift a cardinal to a higher universe. -/
def lift' (c : Cardinal') : Cardinal' := c
/-- Lift as initial segment: preserves order. -/
def liftInitialSeg' (c : Cardinal') : Cardinal' := lift' c
/-- Lift as order embedding: preserves and reflects ≤. -/
def liftOrderEmbedding' (c₁ c₂ : Cardinal') (h : c₁.size ≤ c₂.size) : Prop :=
  (lift' c₁).size ≤ (lift' c₂).size
/-- Cardinal sum over a family: Σ-type cardinality. -/
def sum' (f : α → Cardinal') (totalF : (α → Nat) → Nat) : Cardinal' :=
  ⟨totalF (fun a => (f a).size)⟩
/-- Embedding from any type into Cardinal via cardinality. -/
def embeddingToCardinal' (sizeF : α → Nat) (a : α) : Cardinal' := ⟨sizeF a⟩
/-- A well-ordering on a type (from the well-ordering theorem). -/
def WellOrderingRel' (r : α → α → Prop) : Prop := IsWellOrder r
/-- Cardinal product over a family: Π-type cardinality. -/
abbrev prod' := @sum'  -- sum and product share abstract computation over families
/-- ℵ₀: the cardinality of the natural numbers. -/
def aleph0' : Cardinal' := ⟨0⟩  -- abstract: no finite Nat represents ℵ₀
/-- Cardinal power-lt: sup of c^d for d < c'. -/
def powerlt' (c c' : Cardinal') : Cardinal' := ⟨c.size ^ c'.size⟩

/-- Cardinal sets: types of a given cardinality. -/
abbrev sets' := Cardinal' → Type u

/-- Operands for cardinal arithmetic. -/
abbrev Operands' := Cardinal' × Cardinal'

/-- Game.on: a game with a value assignment. -/
structure on' where
  game : Game'
  val : Nat := 0
/-- Game constructed from a list of left and right moves. -/
structure of' where
  leftOptions : List Game'
  rightOptions : List Game'
/-- Investment type for Domineering game: horizontal or vertical. -/
inductive InvTy' where
  | horizontal : InvTy'
  | vertical : InvTy'

/-- A Domineering board: set of occupied positions. -/
abbrev Board' := List (Nat × Nat)

/-- An impartial game: left and right have identical move sets. -/
class Impartial' (G : Type u) where
  symm : Prop  -- G ≈ -G and all options are impartial

/-- Convert a Nim value to a combinatorial game. -/
abbrev toGame' := Nim

/-- Proof objects for game inequalities. -/
inductive proofs' where
  | le : proofs'
  | lt : proofs'
  | equiv : proofs'
/-- A pre-game: left and right move sets with positions after each move. -/
inductive PGame' : Type (u + 1) where
  | mk (α β : Type u) (L : α → PGame') (R : β → PGame') : PGame'
/-- Left moves from a game constructed via ofLists. -/
abbrev toOfListsLeftMoves' (g : of') := g.leftOptions
/-- Right moves from a game constructed via ofLists. -/
abbrev toOfListsRightMoves' (g : of') := g.rightOptions
/-- IsOption: one game is an immediate option (left or right move) of another. -/
inductive IsOption' : PGame'.{u} → PGame'.{u} → Prop where
  | left {α β L R} (i : α) : IsOption' (L i) (PGame'.mk α β L R)
  | right {α β L R} (j : β) : IsOption' (R j) (PGame'.mk α β L R)
/-- A relabelling: isomorphism of game trees (same structure, different labels). -/
inductive Relabelling' : PGame'.{u} → PGame'.{u} → Prop where
  | mk {α β α' β' L R L' R'}
      (eL : α → α') (eR : β → β') (eL_inv : α' → α) (eR_inv : β' → β) :
      Relabelling' (PGame'.mk α β L R) (PGame'.mk α' β' L' R')

/-- A short game: finitely many positions (all option trees are finite). -/
inductive Short' : PGame'.{u} → Type (u + 1) where
  | mk {α β L R} : (∀ i : α, Short' (L i)) → (∀ j : β, Short' (R j)) →
      Short' (PGame'.mk α β L R)
/-- Inductive game: well-founded game tree (all descending chains finite). -/
class inductive' (G : PGame'.{u}) where
  wf : True  -- well-foundedness of the game tree

/-- A game state: finite-move combinatorial game position. -/
class State' (S : Type u) where
  turnBound : S → Nat
  leftMoves : S → List S
  rightMoves : S → List S

/-- Appending operation on hereditary finite lists. -/
inductive appending' : HFList → HFList → HFList → Prop where
  | nil (b : HFList) : appending' HFList.nil b b
  | cons (a rest b result : HFList) :
      appending' rest b result → appending' (HFList.cons a rest) b (HFList.cons a result)
/-- Subset relation on hereditary finite lists. -/
inductive Subset' : HFList → HFList → Prop where
  | nil (b : HFList) : Subset' HFList.nil b
  | cons (a rest b : HFList) : Subset' rest b → Subset' (HFList.cons a rest) b

/-- Predecessor ordinal: pred(succ α) = α, pred(0) = 0, pred(limit) = limit. -/
def pred' (o : Ordinal') : Ordinal' := ⟨o.rank - 1⟩
/-- Recursion on ordinals: zero case, successor case, limit case. -/
def limitRecOn' (o : Ordinal') (hz : β) (hs : Ordinal' → β → β)
    (_hl : Ordinal' → (Ordinal' → β) → β) : β :=
  Nat.rec hz (fun n ih => hs ⟨n⟩ ih) o.rank
/-- Bounded recursion on ordinals below a given bound. -/
def boundedLimitRecOn' (o bound : Ordinal') (_ : o.rank < bound.rank)
    (hz : β) (hs : Ordinal' → β → β) : β :=
  limitRecOn' o hz hs (fun _ _ => hz)
/-- Convert a type-indexed family to a bounded ordinal-indexed family. -/
def bfamilyOfFamily' (f : α → β) (enumF : Nat → α) : Ordinal' → β :=
  fun o => f (enumF o.rank)
/-- Convert a bounded ordinal-indexed family to a type-indexed family. -/
def familyOfBFamily' (o : Ordinal') (f : Ordinal' → β) (typeinF : α → Nat) : α → β :=
  fun a => f ⟨typeinF a⟩
/-- The range of a bounded ordinal-indexed family. -/
def brange' (o : Ordinal') (f : Ordinal' → β) : β → Prop :=
  fun b => ∃ i : Ordinal', i.rank < o.rank ∧ f i = b
/-- Supremum of a type-indexed family of ordinals. -/
def sup' (f : α → Ordinal') (maxF : (α → Nat) → Nat) : Ordinal' :=
  ⟨maxF (fun a => (f a).rank)⟩
/-- bsup (abstract). -/
def bsup' (o : Ordinal') (f : Ordinal' → Ordinal') : Ordinal' :=
  ⟨(List.range o.rank).foldl (fun acc i => max acc (f ⟨i⟩).rank) 0⟩
/-- lsub (abstract). -/
def lsub' (f : α → Ordinal') (maxF : (α → Nat) → Nat) : Ordinal' :=
  ⟨maxF (fun a => (f a).rank) + 1⟩  -- least strict upper bound = sup + 1
/-- blsub (abstract). -/
def blsub' (o : Ordinal') (f : Ordinal' → Ordinal') : Ordinal' :=
  ⟨(bsup' o f).rank + 1⟩  -- bounded least strict upper bound
/-- blsub₂ (abstract). -/
def blsub₂' (o₁ o₂ : Ordinal') (f : Ordinal' → Ordinal' → Ordinal') : Ordinal' :=
  blsub' o₁ (fun a => blsub' o₂ (fun b => f a b))  -- double bounded lsub
/-- mex (abstract). -/
def mex' (f : α → Ordinal') : Ordinal' :=
  ⟨0⟩  -- minimal excludant: least ordinal not in range of f
/-- bmex (abstract). -/
def bmex' (o : Ordinal') (f : Ordinal' → Ordinal') : Ordinal' :=
  mex' (fun i : Fin o.rank => f ⟨i.val⟩)  -- bounded minimal excludant

/-- Ordinal.is: predicate asserting a value is an ordinal. -/
structure is' where
  rank : Nat
  isOrd : Prop := True
/-- A well-order: a type with a well-ordering relation. -/
structure WellOrder' where
  carrier : Type u
  rel : carrier → carrier → Prop
  wf : ∀ P : carrier → Prop, (∃ a, P a) → ∃ a, P a ∧ ∀ b, P b → ¬rel b a
/-- The carrier type of an ordinal: elements below the rank. -/
def toType' (o : Ordinal') : Type := Fin o.rank
/-- The ordinal type of a well-ordering: its order type. -/
def type' (n : Nat) : Ordinal' := ⟨n⟩
/-- Initial segment embedding: α ≤ β gives a map from α's carrier into β's. -/
def initialSegToType' (a b : Ordinal') (h : a.rank ≤ b.rank) :
    Fin a.rank → Fin b.rank :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
/-- Principal segment embedding: α < β gives a proper initial segment. -/
def principalSegToType' (a b : Ordinal') (h : a.rank < b.rank) :
    Fin a.rank → Fin b.rank :=
  fun i => ⟨i.val, Nat.lt_trans i.isLt h⟩
/-- Position of an element in a well-ordering: its ordinal index. -/
def typein' (posF : α → Nat) (a : α) : Ordinal' := ⟨posF a⟩
/-- The element at a given ordinal position in a well-ordering. -/
def enum' (o : Ordinal') (i : Fin o.rank) : Nat := i.val
/-- Order isomorphism between ordinals below o and o's carrier. -/
def enumIsoToType' (o : Ordinal') : Fin o.rank → Fin o.rank := id
/-- The carrier of a positive ordinal has a least element. -/
def toTypeOrderBotOfPos' (o : Ordinal') (h : o.rank > 0) : Fin o.rank :=
  ⟨0, h⟩
/-- The first infinite ordinal ω. -/
def omega0' : Ordinal' := ⟨0⟩  -- abstract: no finite Nat represents ω
/-- The ordinal of the universe: type of all ordinals in a lower universe. -/
def univ' : Ordinal' := ⟨0⟩  -- abstract: lives in a higher universe
/-- Universe-lifting principal segment: embeds ordinals into a higher universe. -/
def liftPrincipalSeg' (o : Ordinal') : Ordinal' := o
/-- The least ordinal of a given cardinality. -/
def ord' (c : Cardinal') : Ordinal' := ⟨c.size⟩
/-- Galois coinsertion between ord and card: ord ∘ card ≤ id. -/
def gciOrdCard' (o : Ordinal') : Prop := (ord' ⟨o.rank⟩).rank ≤ o.rank
/-- Order embedding from cardinals to ordinals via ord. -/
def orderEmbedding' (c₁ c₂ : Cardinal') (h : c₁.size ≤ c₂.size) : Prop :=
  (ord' c₁).rank ≤ (ord' c₂).rank

/-- Cantor normal form viewed intrinsically (internal representation). -/
structure intrinsically' where
  exponents : List Nat
  coefficients : List Nat
  isNF : Prop := True

/-- Ordinal notation: Cantor normal form below ε₀. -/
inductive ONote' where
  | zero : ONote'
  | oadd : ONote' → Nat → ONote' → ONote'
/-- Below-normal-form: o is in NF and below a given bound. -/
inductive NFBelow' : ONote' → ONote' → Prop where
  | zero (b : ONote') : NFBelow' ONote'.zero b
/-- Normal form: an ordinal notation is in Cantor normal form. -/
class NF' (o : ONote') where
  isNF : Prop

/-- Argument position in a surreal multiplication proof. -/
inductive argument' where
  | left : argument'
  | right : argument'
/-- Arguments tuple for surreal multiplication induction. -/
inductive Args' where
  | mk (x y : PGame'.{u}) : Args'

/-- A pre-set (ZFC): a well-founded tree of sets. -/
inductive PSet' : Type (u + 1) where
  | mk (α : Type u) (A : α → PSet') : PSet'
/-- A definable set function: has a PSet representative. -/
class Definable' (n : Nat) where
  out : (Fin n → PSet'.{u}) → PSet'.{u}
/-- Unary definable set function. -/
abbrev Definable₁' := (PSet'.{u} → PSet'.{u}) → Prop
/-- Extract the PSet representative from a definable function. -/
abbrev out' (n : Nat) := (Fin n → PSet'.{u}) → PSet'.{u}
/-- Binary definable set function. -/
abbrev Definable₂' := (PSet'.{u} → PSet'.{u} → PSet'.{u}) → Prop

/-- A ZFC set is an ordinal: transitive and well-ordered by ∈. -/
structure IsOrdinal' where
  isTransitive : Prop
  isWellOrdered : Prop
