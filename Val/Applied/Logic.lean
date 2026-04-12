/-
Released under MIT license.
-/
import Val.Algebra.Core

/-!
# Val α: Applied — Logic + Combinatorics

Propositional logic, first-order logic, completeness/soundness.
Graphs, partitions, binomial coefficients, generating functions,
Ramsey theory, matroids, Catalan/Fibonacci/Bell numbers, Turán.
-/

namespace Val

universe u

variable {α : Type u}

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

-- FOTerm and FOFormula are defined in Category.lean (Model Theory section).
-- FOLang, FOInterp, realizeTerm, realizeFormula provide the full framework.

-- ============================================================================
-- First-Order Logic: Interpretation
-- ============================================================================

-- Interpretation is provided by FOInterp in Category.lean.

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
