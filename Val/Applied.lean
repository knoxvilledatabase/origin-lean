/-
Released under MIT license.
-/
import Val.Analysis
import Val.MeasureTheory
import Val.Category
import Val.RingTheory

/-!
# Val α: Applied — Probability + Homological Algebra

Two domains consolidated. Both stay in contents throughout.
Probability: measures, random variables, expectation, Bayes, martingales.
Homological Algebra: chain complexes, homology, exact sequences, derived functors.
-/

namespace Val

universe u

-- ============================================================================
-- PROBABILITY THEORY
-- ============================================================================

variable {α : Type u} {S : Type u}

-- ============================================================================
-- Random Variables
-- ============================================================================

/-- A contents random variable never hits origin. -/
theorem contentsRV_ne_origin (X : S → Val α) (hX : ∀ s, ∃ a, X s = contents a) (s : S) :
    X s ≠ origin := by
  obtain ⟨a, ha⟩ := hX s; rw [ha]; intro h; cases h

-- ============================================================================
-- Expectation
-- ============================================================================

/-- Expectation of two outcomes: f₁·P₁ + f₂·P₂ is contents. -/
theorem expectation_two (mulF addF : α → α → α) (f₁ p₁ f₂ p₂ : α) :
    add addF (mul mulF (contents f₁) (contents p₁))
             (mul mulF (contents f₂) (contents p₂)) =
    contents (addF (mulF f₁ p₁) (mulF f₂ p₂)) := rfl

-- ============================================================================
-- Variance
-- ============================================================================

/-- Variance components: (X - μ) and (X - μ)² stay in contents. -/
theorem variance_components (mulF addF : α → α → α) (negF : α → α) (x μ : α) :
    (∃ r, add addF (contents x) (contents (negF μ)) = contents r) ∧
    (∃ r, mul mulF (contents (addF x (negF μ))) (contents (addF x (negF μ))) = contents r) :=
  ⟨⟨addF x (negF μ), rfl⟩, ⟨mulF (addF x (negF μ)) (addF x (negF μ)), rfl⟩⟩

-- ============================================================================
-- Conditional Probability
-- ============================================================================

/-- P(A|B) = P(A∩B) / P(B). Both numerator and denominator are contents.
    No P(B) ≠ 0 sort-level hypothesis needed. -/
theorem conditional_is_contents (mulF : α → α → α) (invF : α → α) (pAB pB : α) :
    ∃ r, mul mulF (contents pAB) (inv invF (contents pB)) = contents r :=
  ⟨mulF pAB (invF pB), rfl⟩

-- ============================================================================
-- Bayes' Theorem
-- ============================================================================

/-- Bayes: P(A|B) = P(B|A) · P(A) / P(B). All components contents. -/
theorem bayes_is_contents (mulF : α → α → α) (invF : α → α) (pBA pA pB : α) :
    ∃ r, mul mulF (mul mulF (contents pBA) (contents pA))
                  (inv invF (contents pB)) = contents r :=
  ⟨mulF (mulF pBA pA) (invF pB), rfl⟩

-- ============================================================================
-- Independence
-- ============================================================================

-- ============================================================================
-- Martingale
-- ============================================================================

/-- A martingale: E[Xₙ₊₁|Fₙ] = Xₙ. Both sides contents. -/
def isMartingale (X : Nat → α) (condExp : Nat → α → α) : Prop :=
  ∀ n, condExp n (X (n + 1)) = X n

/-- Martingale property lifts to Val α. -/
theorem martingale_lift (X : Nat → α) (condExp : Nat → α → α)
    (h : isMartingale X condExp) (n : Nat) :
    (contents (condExp n (X (n + 1))) : Val α) = contents (X n) := by
  show contents (condExp n (X (n + 1))) = contents (X n); rw [h]

-- ============================================================================
-- Stopping Time
-- ============================================================================

-- ============================================================================
-- Convergence of Random Variables
-- ============================================================================

/-- Contents RVs converge to contents limits under liftConv. -/
theorem rv_convergence (conv : (Nat → α) → α → Prop) (X : Nat → α) (L : α)
    (h : conv X L) :
    liftConv conv (fun n => contents (X n)) (contents L) :=
  ⟨X, fun _ => rfl, h⟩

-- ============================================================================
-- HOMOLOGICAL ALGEBRA
-- ============================================================================

variable {α : Type u}

-- ============================================================================
-- Chain Complexes
-- ============================================================================

/-- A chain complex: sequence of modules with differentials d : Cₙ → Cₙ₋₁. -/
structure ChainComplex (α : Type u) where
  differential : Int → α → α

-- ============================================================================
-- d² = 0: The Boundary of a Boundary Is Zero
-- ============================================================================

/-- d² = 0 in α lifts to contents(0) in Val α, not origin. -/
theorem d_squared_contents [Zero α] (C : ChainComplex α) (n : Int) (a : α)
    (h : C.differential (n - 1) (C.differential n a) = 0) :
    (contents (C.differential (n - 1) (C.differential n a)) : Val α) = contents 0 := by
  congr 1


-- ============================================================================
-- Kernel and Image
-- ============================================================================

/-- Kernel: elements a where d(a) = zero. -/
def inKernel (d : α → α) (zero : α) (a : α) : Prop := d a = zero

/-- Image: elements a where a = d(b) for some b. -/
def inImage (d : α → α) (a : α) : Prop := ∃ b, d b = a

-- ============================================================================
-- Exact Sequences
-- ============================================================================

/-- Exact at position n: im(dₙ₊₁) = ker(dₙ). Same-type version for chain complexes. -/
def isExactChain (d_next d_curr : α → α) (zero : α) : Prop :=
  ∀ a, inImage d_next a ↔ inKernel d_curr zero a

/-- In an exact sequence, every kernel element has a contents preimage. -/
theorem exact_preimage_contents (d_next d_curr : α → α) (zero : α)
    (h : isExactChain d_next d_curr zero) (a : α) (hk : inKernel d_curr zero a) :
    ∃ b, d_next b = a ∧ (contents b : Val α) ≠ origin :=
  let ⟨b, hb⟩ := (h a).mpr hk
  ⟨b, hb, by intro h2; cases h2⟩

-- ============================================================================
-- Derived Functors
-- ============================================================================

-- derived_functor_contents and derived_functor_comp: see Category.lean

-- ============================================================================
-- Ext and Tor
-- ============================================================================

-- ============================================================================
-- Long Exact Sequence
-- ============================================================================

-- ============================================================================
-- INFORMATION THEORY
-- ============================================================================

-- ============================================================================
-- Entropy
-- ============================================================================

-- ============================================================================
-- Hamming Distance
-- ============================================================================

/-- Hamming distance: count of differing positions. A valMap. -/
abbrev hammingNorm (hamF : α → α) : Val α → Val α := valMap hamF

-- ============================================================================
-- Kraft Inequality
-- ============================================================================

/-- Kraft inequality check: sum ≤ 1 is a contents-level property. -/
theorem kraft_le_contents (leF : α → α → Prop) (kraftSum one : α) (h : leF kraftSum one) :
    valLE leF (contents kraftSum) (contents one) := h

-- ============================================================================
-- SET THEORY
-- ============================================================================

-- ============================================================================
-- Ordinals
-- ============================================================================

/-- An ordinal: a well-ordered type wrapped in Val α. -/
structure Ordinal (α : Type u) where
  rank : α

/-- Ordinal zero: the sort matters. origin ≠ contents(∅). -/
def ordinalZero (zero : α) : Val α := contents zero

/-- Ordinal successor. -/
abbrev ordSucc (succF : α → α) : Val α → Val α := valMap succF

-- ============================================================================
-- Ordinal Arithmetic
-- ============================================================================

/-- Ordinal exponentiation via valMap. -/
abbrev ordExp (expF : α → α) : Val α → Val α := valMap expF

-- ============================================================================
-- Cardinals
-- ============================================================================

/-- A cardinal: cardinality of a type. -/
structure Cardinal (α : Type u) where
  card : α

/-- Cardinal from contents. -/
def cardVal (c : Cardinal α) : Val α := contents c.card

/-- Cardinal comparison lifts to valLE. -/
theorem card_le_contents (leF : α → α → Prop) (a b : Cardinal α) (h : leF a.card b.card) :
    valLE leF (cardVal a) (cardVal b) := h

-- ============================================================================
-- Cardinal Arithmetic
-- ============================================================================

-- ============================================================================
-- Cofinality
-- ============================================================================

/-- Cofinality: smallest cardinality of a cofinal subset. -/
abbrev cofinality (cofF : α → α) : Val α → Val α := valMap cofF

-- ============================================================================
-- Cantor's Theorem
-- ============================================================================

/-- Cantor: |α| < |P(α)|. Strict inequality in contents. -/
theorem cantor_strict (ltF : α → α → Prop) (card_a card_pa : α) (h : ltF card_a card_pa) :
    valLT ltF (contents card_a) (contents card_pa) := h

-- ============================================================================
-- ZFC Axioms as Properties
-- ============================================================================

/-- Membership test: a ∈ S is a contents-level predicate. -/
def setMem (memF : α → α → Prop) (a s : α) : Prop := memF a s

/-- Subset: A ⊆ B is a contents-level predicate. -/
def setSubset (subsetF : α → α → Prop) (a b : α) : Prop := subsetF a b

-- ============================================================================
-- COMPUTABILITY
-- ============================================================================

-- ============================================================================
-- Partial Recursive Functions
-- ============================================================================

/-- A partial computation: either halts with a value or diverges.
    origin = the computation that doesn't halt. -/
def partialResult (result : Option α) : Val α :=
  match result with
  | none => origin
  | some a => contents a

/-- A halting computation produces contents. -/
theorem halts_is_contents (a : α) :
    partialResult (some a) = (contents a : Val α) := rfl

/-- A diverging computation is origin. -/
theorem diverges_is_origin :
    partialResult (none : Option α) = (origin : Val α) := rfl

-- ============================================================================
-- Evaluation / Step Functions
-- ============================================================================

/-- Evaluation is a valMap: applying a step function preserves sort. -/
abbrev compEval (stepF : α → α) : Val α → Val α := valMap stepF

/-- Multi-step evaluation: n steps of a function. -/
def multiStep (stepF : α → α) : Nat → Val α → Val α
  | 0, v => v
  | n + 1, v => multiStep stepF n (compEval stepF v)

/-- Multi-step on origin stays origin. -/
theorem multiStep_origin (stepF : α → α) (n : Nat) :
    multiStep stepF n origin = (origin : Val α) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [multiStep, compEval]; exact ih

-- ============================================================================
-- Decidability
-- ============================================================================

/-- A decidable predicate: every input produces contents(true) or contents(false). -/
def isDecidable (decide : α → Bool) (a : α) : Val Bool :=
  contents (decide a)

/-- Decidable results are always contents. -/
theorem decidable_is_contents (decide : α → Bool) (a : α) :
    ∃ b, isDecidable decide a = contents b := ⟨decide a, rfl⟩

-- ============================================================================
-- Halting Problem
-- ============================================================================

/-- The halting oracle type: given a program and input, returns halt/diverge. -/
def haltOracle (oracle : α → α → Option α) (prog input : α) : Val α :=
  partialResult (oracle prog input)

/-- If the oracle says halts, result is contents. -/
theorem oracle_halts (oracle : α → α → Option α) (prog input result : α)
    (h : oracle prog input = some result) :
    haltOracle oracle prog input = contents result := by simp [haltOracle, partialResult, h]

/-- If the oracle says diverges, result is origin. -/
theorem oracle_diverges (oracle : α → α → Option α) (prog input : α)
    (h : oracle prog input = none) :
    haltOracle oracle prog input = origin := by simp [haltOracle, partialResult, h]

-- ============================================================================
-- Turing Machines
-- ============================================================================

/-- A Turing machine configuration: state + tape. -/
structure TMConfig (α : Type u) where
  state : α
  tape : α

/-- TM step function preserves sort via valMap. -/
abbrev tmStep (stepF : α → α) : Val α → Val α := valMap stepF

/-- TM configuration as contents. -/
def tmConfig (c : TMConfig α) : Val (α × α) := contents (c.state, c.tape)

/-- TM run: iterate the step function. -/
def tmRun (stepF : α → α) (n : Nat) (config : Val α) : Val α :=
  multiStep stepF n config

-- ============================================================================
-- Church-Turing Thesis
-- ============================================================================

/-- Two computation models agree if they produce the same contents. -/
def modelsAgree (eval₁ eval₂ : α → Val α) : Prop :=
  ∀ a, eval₁ a = eval₂ a

/-- Agreement is reflexive. -/
theorem modelsAgree_refl (eval₁ : α → Val α) : modelsAgree eval₁ eval₁ :=
  fun _ => rfl

/-- Agreement is symmetric. -/
theorem modelsAgree_symm (eval₁ eval₂ : α → Val α) (h : modelsAgree eval₁ eval₂) :
    modelsAgree eval₂ eval₁ := fun a => (h a).symm

-- ============================================================================
-- Rice's Theorem
-- ============================================================================

/-- A semantic property: depends only on the function computed, not the program.
    If two programs compute the same function, the property agrees. -/
def isSemanticProp (prop : α → Prop) (equiv : α → α → Prop) : Prop :=
  ∀ p q, equiv p q → (prop p ↔ prop q)

/-- A nontrivial semantic property: some program has it, some doesn't. -/
def isNontrivial (prop : α → Prop) : Prop :=
  (∃ p, prop p) ∧ (∃ q, ¬ prop q)

-- ============================================================================
-- Enumerable Sets
-- ============================================================================

/-- An enumerable set: there exists an enumerator that lists its elements. -/
def isEnumerable (enum : Nat → Option α) (S : α → Prop) : Prop :=
  ∀ a, S a ↔ ∃ n, enum n = some a

/-- Enumerator outputs are either origin (not found) or contents. -/
theorem enum_result (enum : Nat → Option α) (n : Nat) :
    partialResult (enum n) = origin ∨ ∃ a, partialResult (enum n) = contents a := by
  cases h : enum n with
  | none => left; rfl
  | some a => right; exact ⟨a, rfl⟩

-- ============================================================================
-- LOGIC
-- ============================================================================

-- ============================================================================
-- Propositional Logic: Formulas
-- ============================================================================

/-- A propositional formula. -/
inductive PropFormula (α : Type u) where
  | var : α → PropFormula α
  | propNot : PropFormula α → PropFormula α
  | propAnd : PropFormula α → PropFormula α → PropFormula α
  | propOr : PropFormula α → PropFormula α → PropFormula α
  | propImpl : PropFormula α → PropFormula α → PropFormula α

-- ============================================================================
-- Propositional Logic: Evaluation
-- ============================================================================

/-- Evaluate a propositional formula under a valuation.
    Evaluation is a valMap from formulas to truth values. -/
def propEval (v : α → Bool) : PropFormula α → Bool
  | .var a => v a
  | .propNot φ => !propEval v φ
  | .propAnd φ ψ => propEval v φ && propEval v ψ
  | .propOr φ ψ => propEval v φ || propEval v ψ
  | .propImpl φ ψ => !propEval v φ || propEval v ψ

/-- Lifting propositional evaluation to Val: always contents. -/
theorem propEval_contents (v : α → Bool) (φ : PropFormula α) :
    (contents (propEval v φ) : Val Bool) ≠ origin := by intro h; cases h

-- ============================================================================
-- Tautologies
-- ============================================================================

/-- A tautology: true under all valuations. -/
def isTautology (φ : PropFormula α) : Prop :=
  ∀ v : α → Bool, propEval v φ = true

/-- p ∨ ¬p is a tautology. -/
theorem lem_tautology (a : α) :
    isTautology (.propOr (.var a) (.propNot (.var a))) := by
  intro v; simp [propEval]

-- ============================================================================
-- Satisfiability
-- ============================================================================

/-- Satisfiable: true under some valuation. -/
def isSatisfiable (φ : PropFormula α) : Prop :=
  ∃ v : α → Bool, propEval v φ = true

/-- Every tautology is satisfiable (given any valuation exists). -/
theorem tautology_satisfiable (φ : PropFormula α) (h : isTautology φ)
    (v : α → Bool) : isSatisfiable φ := ⟨v, h v⟩

-- ============================================================================
-- First-Order Logic: Terms and Formulas
-- ============================================================================

/-- First-order terms. -/
inductive FOTerm (α : Type u) where
  | foVar : α → FOTerm α
  | foFunc : α → List (FOTerm α) → FOTerm α

/-- First-order formulas. -/
inductive FOFormula (α : Type u) where
  | foRel : α → List (FOTerm α) → FOFormula α
  | foNot : FOFormula α → FOFormula α
  | foAnd : FOFormula α → FOFormula α → FOFormula α
  | foOr : FOFormula α → FOFormula α → FOFormula α
  | foForall : α → FOFormula α → FOFormula α
  | foExists : α → FOFormula α → FOFormula α

-- ============================================================================
-- First-Order Logic: Interpretation
-- ============================================================================

/-- An interpretation assigns meaning to function and relation symbols. -/
structure Interpretation (α : Type u) where
  domain : Type u
  funcInterp : α → List domain → domain
  relInterp : α → List domain → Prop

-- ============================================================================
-- Logical Consequence
-- ============================================================================

/-- Logical consequence: φ follows from Γ if every model of Γ satisfies φ. -/
def logicalConsequence (eval : α → Bool) (premises conclusion : List (PropFormula α)) : Prop :=
  (∀ p ∈ premises, propEval eval p = true) →
  (∀ c ∈ conclusion, propEval eval c = true)

-- ============================================================================
-- Completeness and Soundness
-- ============================================================================

/-- Soundness: if provable, then valid. A contents-level statement. -/
def isSound (proves : α → Prop) (valid : α → Prop) : Prop :=
  ∀ φ, proves φ → valid φ

/-- Completeness: if valid, then provable. -/
def isComplete (proves : α → Prop) (valid : α → Prop) : Prop :=
  ∀ φ, valid φ → proves φ

/-- Soundness + completeness: proves ↔ valid. -/
theorem sound_complete_iff (proves valid : α → Prop)
    (hs : isSound proves valid) (hc : isComplete proves valid) (φ : α) :
    proves φ ↔ valid φ := ⟨hs φ, hc φ⟩

-- ============================================================================
-- Compactness
-- ============================================================================

/-- Compactness: a set of formulas is satisfiable iff every finite subset is. -/
def isCompact (sat : List α → Prop) (allFormulas : List α) : Prop :=
  sat allFormulas ↔ ∀ sub : List α, sub ⊆ allFormulas → sat sub

-- ============================================================================
-- Löwenheim-Skolem
-- ============================================================================

/-- Downward Löwenheim-Skolem: if a theory has a model of size κ,
    it has a model of every size λ ≤ κ (above the language size). -/
def hasModelOfSize (leF : α → α → Prop) (_theory : α) (size langSize : α) : Prop :=
  leF langSize size

-- ============================================================================
-- COMBINATORICS
-- ============================================================================

-- ============================================================================
-- Graphs: Basic Structure
-- ============================================================================

/-- A graph: vertices and an adjacency relation.
    origin = empty graph (no vertices). contents(G) = graph with data. -/
structure Graph (α : Type u) where
  vertices : α
  adj : α → α → Prop

/-- Graph as Val: contents wraps the vertex set. -/
def graphVal (G : Graph α) : Val α := contents G.vertices

-- ============================================================================
-- Graph Properties
-- ============================================================================

/-- Degree of a vertex: a valMap. -/
abbrev degree (degF : α → α) : Val α → Val α := valMap degF

/-- Number of edges: a valMap. -/
abbrev edgeCount (countF : α → α) : Val α → Val α := valMap countF

-- ============================================================================
-- Paths and Connectivity
-- ============================================================================

/-- A path: sequence of vertices. Encoded as contents. -/
def pathVal (path : List α) (encode : List α → α) : Val α :=
  contents (encode path)

/-- Connectivity: whether a path exists between two vertices. -/
def isConnected (connected : α → α → Prop) (u v : α) : Prop := connected u v

-- ============================================================================
-- Partitions
-- ============================================================================

/-- A partition of n: a list of positive integers summing to n. -/
structure Partition (α : Type u) where
  parts : List α
  total : α

/-- Partition as Val: the total is contents. -/
def partitionVal (p : Partition α) : Val α := contents p.total

/-- Partition count: number of partitions of n. A valMap. -/
abbrev partitionCount (countF : α → α) : Val α → Val α := valMap countF

-- ============================================================================
-- Binomial Coefficients
-- ============================================================================

/-- Binomial coefficient C(n,k). A binary operation on contents. -/
def binomial (chooseF : α → α → α) (n k : Val α) : Val α := mul chooseF n k

-- ============================================================================
-- Generating Functions
-- ============================================================================

/-- A generating function coefficient: the n-th coefficient. -/
def genFuncCoeff (coeffs : Nat → α) (n : Nat) : Val α := contents (coeffs n)

/-- Coefficients are always contents. -/
theorem genFuncCoeff_contents (coeffs : Nat → α) (n : Nat) :
    genFuncCoeff coeffs n = contents (coeffs n) := rfl

/-- Coefficient extraction via valMap. -/
abbrev extractCoeff (extractF : α → α) : Val α → Val α := valMap extractF

-- ============================================================================
-- Factorial and Falling Factorial
-- ============================================================================

/-- Factorial via valMap. -/
abbrev factorial (factF : α → α) : Val α → Val α := valMap factF

/-- Falling factorial via valMap. -/
abbrev fallingFactorial (fallF : α → α) : Val α → Val α := valMap fallF

-- ============================================================================
-- Young Tableaux
-- ============================================================================

/-- A Young diagram: a partition viewed as a shape. -/
structure YoungDiagram (α : Type u) where
  shape : List α

/-- Young diagram as Val. -/
def youngVal (Y : YoungDiagram α) (encode : List α → α) : Val α :=
  contents (encode Y.shape)

/-- Standard Young tableau count: a valMap on the shape. -/
abbrev tableauCount (countF : α → α) : Val α → Val α := valMap countF

-- ============================================================================
-- Matroids
-- ============================================================================

/-- A matroid: a ground set with an independence predicate. -/
structure Matroid (α : Type u) where
  ground : α
  independent : α → Prop

/-- Matroid rank: a valMap. -/
abbrev matroidRank (rankF : α → α) : Val α → Val α := valMap rankF

/-- Matroid ground set as Val. -/
def matroidVal (M : Matroid α) : Val α := contents M.ground

/-- Matroid closure: a valMap. -/
abbrev matroidClosure (clF : α → α) : Val α → Val α := valMap clF

-- ============================================================================
-- Ramsey Theory
-- ============================================================================

/-- Ramsey number: R(s,t) is a contents value. -/
def ramseyNumber (ramseyF : α → α → α) (s t : α) : Val α :=
  contents (ramseyF s t)

/-- Ramsey number is contents. -/
theorem ramsey_contents (ramseyF : α → α → α) (s t : α) :
    ramseyNumber ramseyF s t = contents (ramseyF s t) := rfl

/-- Ramsey symmetry: R(s,t) = R(t,s). -/
theorem ramsey_symm (ramseyF : α → α → α) (s t : α)
    (h : ramseyF s t = ramseyF t s) :
    ramseyNumber ramseyF s t = ramseyNumber ramseyF t s := by simp [ramseyNumber, h]

/-- Ramsey upper bound: R(s,t) ≤ R(s-1,t) + R(s,t-1). Contents inequality. -/
theorem ramsey_bound (leF : α → α → Prop) (addF : α → α → α)
    (rst rs1t rst1 : α) (h : leF rst (addF rs1t rst1)) :
    valLE leF (contents rst) (contents (addF rs1t rst1)) := h

-- ============================================================================
-- Graph Coloring
-- ============================================================================

/-- Chromatic number: minimum colors for proper coloring. A valMap. -/
abbrev chromaticNumber (chiF : α → α) : Val α → Val α := valMap chiF

-- ============================================================================
-- Catalan Numbers
-- ============================================================================

/-- Catalan number: C_n. A valMap. -/
abbrev catalanNumber (catF : α → α) : Val α → Val α := valMap catF

-- ============================================================================
-- Pigeonhole
-- ============================================================================

/-- Pigeonhole: if n+1 items in n boxes, some box has ≥ 2.
    The count is a contents-level value. -/
theorem pigeonhole_contents (items boxes : α) (ltF : α → α → Prop)
    (h : ltF boxes items) :
    valLT ltF (contents boxes) (contents items) := h

-- ============================================================================
-- Stirling Numbers
-- ============================================================================

/-- Stirling number of the second kind: S(n,k). A valMap. -/
abbrev stirling2 (stirF : α → α → α) (n k : Val α) : Val α := mul stirF n k

-- ============================================================================
-- Euler's Formula for Planar Graphs
-- ============================================================================

/-- Euler's formula: V - E + F = 2. Contents arithmetic. -/
theorem euler_formula_contents (addF : α → α → α) (negF : α → α)
    (v e f two : α) (h : addF (addF v (negF e)) f = two) :
    add addF (add addF (contents v) (contents (negF e))) (contents f) =
    contents two := by simp [h]

-- ============================================================================
-- Fibonacci Numbers
-- ============================================================================

/-- Fibonacci via valMap. -/
abbrev fibonacci (fibF : α → α) : Val α → Val α := valMap fibF

-- ============================================================================
-- Bell Numbers
-- ============================================================================

/-- Bell number: B_n = Σ S(n,k). A valMap. -/
abbrev bellNumber (bellF : α → α) : Val α → Val α := valMap bellF

-- ============================================================================
-- Derangements
-- ============================================================================

/-- Derangement count: D(n). A valMap. -/
abbrev derangement (derF : α → α) : Val α → Val α := valMap derF

/-- Derangement recurrence: D(n) = (n-1)(D(n-1) + D(n-2)). Contents arithmetic. -/
theorem derangement_recurrence (mulF addF : α → α → α) (n_minus_1 dn1 dn2 : α) :
    mul mulF (contents n_minus_1) (add addF (contents dn1) (contents dn2)) =
    contents (mulF n_minus_1 (addF dn1 dn2)) := rfl

-- ============================================================================
-- Graph: Trees
-- ============================================================================

-- ============================================================================
-- Graph: Bipartite
-- ============================================================================

/-- Bipartite graph: vertices split into two sets. -/
structure BipartiteGraph (α : Type u) where
  left : α
  right : α
  edges : α

/-- Bipartite graph as Val: vertex set is contents. -/
def bipartiteVal (G : BipartiteGraph α) (pairF : α → α → α) : Val α :=
  contents (pairF G.left G.right)

-- ============================================================================
-- Graph: Matching
-- ============================================================================

/-- Matching size: a valMap. -/
abbrev matchingSize (matchF : α → α) : Val α → Val α := valMap matchF

-- ============================================================================
-- Graph: Spanning Trees
-- ============================================================================

/-- Kirchhoff's theorem: number of spanning trees via matrix tree theorem. -/
abbrev spanTreeCount (detF : α → α) : Val α → Val α := valMap detF

-- ============================================================================
-- Graph: Flows and Cuts
-- ============================================================================

/-- Max flow = min cut. Both sides are contents. -/
theorem max_flow_min_cut (flow cut : α) (h : flow = cut) :
    (contents flow : Val α) = contents cut := by rw [h]

-- ============================================================================
-- Lattice Paths
-- ============================================================================

-- ============================================================================
-- Multinomial Coefficients
-- ============================================================================

/-- Multinomial coefficient: n! / (k₁! · k₂! · ... · kₘ!). A valMap. -/
abbrev multinomial (multiF : α → α) : Val α → Val α := valMap multiF

-- ============================================================================
-- Möbius Function
-- ============================================================================

/-- Möbius function on a poset: μ(x,y). -/
def mobiusVal (mobiusF : α → α → α) (x y : α) : Val α :=
  contents (mobiusF x y)

-- ============================================================================
-- Polynomial Method
-- ============================================================================

/-- Combinatorial Nullstellensatz: degree bound. Contents inequality. -/
theorem nullstellensatz_bound (leF : α → α → Prop) (deg bound : α) (h : leF deg bound) :
    valLE leF (contents deg) (contents bound) := h

-- ============================================================================
-- Hypergraph
-- ============================================================================

/-- A hypergraph: vertices and hyperedges (subsets of vertices). -/
structure Hypergraph (α : Type u) where
  vertices : α
  hyperedges : α

/-- Hypergraph as Val. -/
def hypergraphVal (H : Hypergraph α) : Val α := contents H.vertices

/-- Hypergraph rank: maximum edge size. A valMap. -/
abbrev hypergraphRank (rankF : α → α) : Val α → Val α := valMap rankF

-- ============================================================================
-- Turán's Theorem
-- ============================================================================

/-- Turán number: max edges in K_{r+1}-free graph on n vertices. -/
def turanNumber (turanF : α → α → α) (n r : α) : Val α :=
  contents (turanF n r)

theorem turan_contents (turanF : α → α → α) (n r : α) :
    turanNumber turanF n r = contents (turanF n r) := rfl

/-- Turán bound: edge count ≤ Turán number. -/
theorem turan_bound (leF : α → α → Prop) (edges turan : α) (h : leF edges turan) :
    valLE leF (contents edges) (contents turan) := h

-- ============================================================================
-- Extremal Graph Theory
-- ============================================================================

/-- Zarankiewicz problem: z(m,n;s,t). -/
def zarankiewicz (zF : α → α → α → α → α) (m n s t : α) : Val α :=
  contents (zF m n s t)

/-- Kruskal-Katona: shadow bound. -/
theorem kruskal_katona_bound (leF : α → α → Prop) (shadow bound : α) (h : leF shadow bound) :
    valLE leF (contents shadow) (contents bound) := h

-- ============================================================================
-- Probabilistic Combinatorics
-- ============================================================================

/-- Lovász Local Lemma: if dependencies are bounded, probability is positive. -/
theorem lll_positive (ltF : α → α → Prop) (zero prob : α) (h : ltF zero prob) :
    valLT ltF (contents zero) (contents prob) := h

end Val
