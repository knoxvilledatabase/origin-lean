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

/-- Expectation of a single outcome: f · P is contents. -/
theorem expectation_single (mulF : α → α → α) (f_val p_val : α) :
    mul mulF (contents f_val) (contents p_val) = contents (mulF f_val p_val) := rfl

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

/-- P(A∩B) = P(A)·P(B): independence is a contents-level property. -/
theorem independence_is_contents (mulF : α → α → α) (pA pB : α) :
    mul mulF (contents pA) (contents pB) = contents (mulF pA pB) := rfl

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

/-- Differentials map contents to contents. -/
theorem differential_contents (C : ChainComplex α) (n : Int) (a : α) :
    valMap (C.differential n) (contents a) = contents (C.differential n a) := rfl


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

/-- Homology class: quotient map sends contents to contents. -/
theorem homology_class_contents (proj : α → α) (a : α) :
    quotientMap proj (contents a) = contents (proj a) := rfl


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

/-- Tor: tensor of contents with contents is contents (multiplication). -/
theorem tor_contents (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl


-- ============================================================================
-- Long Exact Sequence
-- ============================================================================

/-- The connecting homomorphism δ maps contents to contents. -/
theorem connecting_homomorphism_contents (delta : α → α) (a : α) :
    valMap delta (contents a) = contents (delta a) := rfl

-- ============================================================================
-- INFORMATION THEORY
-- ============================================================================

-- ============================================================================
-- Entropy
-- ============================================================================

/-- Shannon entropy term: -p · log(p). Both factors contents. -/
theorem entropy_term_contents (mulF : α → α → α) (negF : α → α) (logF : α → α)
    (p : α) :
    mul mulF (contents (negF p)) (contents (logF p)) = contents (mulF (negF p) (logF p)) := rfl

/-- Entropy sum: accumulating entropy terms stays in contents. -/
theorem entropy_sum_contents (addF : α → α → α) (h₁ h₂ : α) :
    add addF (contents h₁) (contents h₂) = contents (addF h₁ h₂) := rfl

-- ============================================================================
-- KL Divergence
-- ============================================================================

/-- KL divergence term: p · log(p/q). Scaling guards dissolve. -/
theorem kl_term_contents (mulF : α → α → α) (logF : α → α) (invF : α → α) (p q : α) :
    mul mulF (contents p) (contents (logF (mulF p (invF q)))) =
    contents (mulF p (logF (mulF p (invF q)))) := rfl

-- ============================================================================
-- Mutual Information
-- ============================================================================

/-- Mutual information: I(X;Y) = H(X) + H(Y) - H(X,Y). Contents arithmetic. -/
theorem mutual_info_contents (addF : α → α → α) (negF : α → α) (hx hy hxy : α) :
    add addF (add addF (contents hx) (contents hy)) (contents (negF hxy)) =
    contents (addF (addF hx hy) (negF hxy)) := rfl

-- ============================================================================
-- Hamming Distance
-- ============================================================================

/-- Hamming distance: count of differing positions. A valMap. -/
abbrev hammingNorm (hamF : α → α) : Val α → Val α := valMap hamF

/-- Hamming norm of contents is contents. -/
theorem hammingNorm_contents (hamF : α → α) (a : α) :
    hammingNorm hamF (contents a) = contents (hamF a) := rfl

-- ============================================================================
-- Kraft Inequality
-- ============================================================================

/-- Kraft sum: Σ 2^(-lᵢ). Accumulates in contents. -/
theorem kraft_sum_contents (addF : α → α → α) (powF : α → α) (l₁ l₂ : α) :
    add addF (contents (powF l₁)) (contents (powF l₂)) =
    contents (addF (powF l₁) (powF l₂)) := rfl

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

/-- Successor of contents is contents. -/
theorem ordSucc_contents (succF : α → α) (a : α) :
    ordSucc succF (contents a) = contents (succF a) := rfl

-- ============================================================================
-- Ordinal Arithmetic
-- ============================================================================

/-- Ordinal addition: contents + contents = contents. -/
theorem ordAdd_contents (addF : α → α → α) (a b : α) :
    add addF (contents a) (contents b) = contents (addF a b) := rfl

/-- Ordinal multiplication: contents · contents = contents. -/
theorem ordMul_contents (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

/-- Ordinal exponentiation via valMap. -/
abbrev ordExp (expF : α → α) : Val α → Val α := valMap expF

theorem ordExp_contents (expF : α → α) (a : α) :
    ordExp expF (contents a) = contents (expF a) := rfl

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

/-- Cardinal addition. -/
theorem cardAdd_contents (addF : α → α → α) (a b : Cardinal α) :
    add addF (cardVal a) (cardVal b) = contents (addF a.card b.card) := rfl

/-- Cardinal multiplication. -/
theorem cardMul_contents (mulF : α → α → α) (a b : Cardinal α) :
    mul mulF (cardVal a) (cardVal b) = contents (mulF a.card b.card) := rfl

/-- Cardinal exponentiation. -/
theorem cardExp_contents (expF : α → α) (a : Cardinal α) :
    valMap expF (cardVal a) = contents (expF a.card) := rfl

-- ============================================================================
-- Cofinality
-- ============================================================================

/-- Cofinality: smallest cardinality of a cofinal subset. -/
abbrev cofinality (cofF : α → α) : Val α → Val α := valMap cofF

theorem cofinality_contents (cofF : α → α) (a : α) :
    cofinality cofF (contents a) = contents (cofF a) := rfl

-- ============================================================================
-- Cantor's Theorem
-- ============================================================================

/-- Cantor: |α| < |P(α)|. Strict inequality in contents. -/
theorem cantor_strict (ltF : α → α → Prop) (card_a card_pa : α) (h : ltF card_a card_pa) :
    valLT ltF (contents card_a) (contents card_pa) := h

-- ============================================================================
-- ZFC Axioms as Properties
-- ============================================================================

/-- Empty set: contents(∅), not origin. The sort distinguishes them. -/
theorem empty_set_is_contents (empty : α) :
    (contents empty : Val α) ≠ origin := by intro h; cases h

/-- Pairing: {a, b} is contents. -/
theorem pairing_contents (pairF : α → α → α) (a b : α) :
    mul pairF (contents a) (contents b) = contents (pairF a b) := rfl

/-- Union: ∪S is contents when S is contents. -/
theorem union_contents (unionF : α → α) (a : α) :
    valMap unionF (contents a) = contents (unionF a) := rfl

/-- Power set: P(S) is contents when S is contents. -/
theorem powerset_contents (powerF : α → α) (a : α) :
    valMap powerF (contents a) = contents (powerF a) := rfl

/-- Separation: {x ∈ S | φ(x)} is contents when S is contents. -/
theorem separation_contents (filterF : α → α) (a : α) :
    valMap filterF (contents a) = contents (filterF a) := rfl

/-- Replacement: {F(x) | x ∈ S} is contents when S is contents. -/
theorem replacement_contents (replF : α → α) (a : α) :
    valMap replF (contents a) = contents (replF a) := rfl

/-- Infinity: ω is contents. -/
theorem infinity_contents (omega : α) :
    (contents omega : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Set Operations
-- ============================================================================

/-- Intersection: A ∩ B is contents. -/
theorem inter_contents (interF : α → α → α) (a b : α) :
    mul interF (contents a) (contents b) = contents (interF a b) := rfl

/-- Set difference: A \ B is contents. -/
theorem sdiff_contents (sdiffF : α → α → α) (a b : α) :
    mul sdiffF (contents a) (contents b) = contents (sdiffF a b) := rfl

/-- Symmetric difference. -/
theorem symm_diff_contents (symmF : α → α → α) (a b : α) :
    mul symmF (contents a) (contents b) = contents (symmF a b) := rfl

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

/-- Evaluation of contents is contents. -/
theorem compEval_contents (stepF : α → α) (a : α) :
    compEval stepF (contents a) = contents (stepF a) := rfl

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

/-- Interpretation maps are valMaps: they preserve sort. -/
theorem interp_contents (f : α → α) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

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

/-- Model existence lifts to Val: the model size is contents. -/
theorem model_size_contents (size : α) :
    (contents size : Val α) ≠ origin := by intro h; cases h

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

/-- Empty graph vs origin: contents(∅) ≠ origin. -/
theorem empty_graph_ne_origin (emptyVerts : α) :
    (contents emptyVerts : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Graph Properties
-- ============================================================================

/-- Degree of a vertex: a valMap. -/
abbrev degree (degF : α → α) : Val α → Val α := valMap degF

theorem degree_contents (degF : α → α) (v : α) :
    degree degF (contents v) = contents (degF v) := rfl

/-- Number of edges: a valMap. -/
abbrev edgeCount (countF : α → α) : Val α → Val α := valMap countF

-- ============================================================================
-- Paths and Connectivity
-- ============================================================================

/-- A path: sequence of vertices. Encoded as contents. -/
def pathVal (path : List α) (encode : List α → α) : Val α :=
  contents (encode path)

/-- Path existence: a contents-level property. -/
theorem path_is_contents (path : List α) (encode : List α → α) :
    ∃ r, pathVal path encode = contents r := ⟨encode path, rfl⟩

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

theorem partitionCount_contents (countF : α → α) (n : α) :
    partitionCount countF (contents n) = contents (countF n) := rfl

-- ============================================================================
-- Binomial Coefficients
-- ============================================================================

/-- Binomial coefficient C(n,k). A binary operation on contents. -/
def binomial (chooseF : α → α → α) (n k : Val α) : Val α := mul chooseF n k

/-- Binomial of contents is contents. -/
theorem binomial_contents (chooseF : α → α → α) (n k : α) :
    binomial chooseF (contents n) (contents k) = contents (chooseF n k) := rfl

/-- Pascal's rule: C(n+1,k+1) = C(n,k) + C(n,k+1). Contents arithmetic. -/
theorem pascal_contents (addF _chooseF : α → α → α) (nk nk1 : α) :
    add addF (contents nk) (contents nk1) = contents (addF nk nk1) := rfl

/-- Vandermonde identity: sum form. Contents addition. -/
theorem vandermonde_sum (addF : α → α → α) (term₁ term₂ : α) :
    add addF (contents term₁) (contents term₂) = contents (addF term₁ term₂) := rfl

-- ============================================================================
-- Generating Functions
-- ============================================================================

/-- A generating function coefficient: the n-th coefficient. -/
def genFuncCoeff (coeffs : Nat → α) (n : Nat) : Val α := contents (coeffs n)

/-- Coefficients are always contents. -/
theorem genFuncCoeff_contents (coeffs : Nat → α) (n : Nat) :
    genFuncCoeff coeffs n = contents (coeffs n) := rfl

/-- Product of generating functions: Cauchy product (convolution). -/
theorem cauchy_product_contents (mulF _addF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

/-- Coefficient extraction via valMap. -/
abbrev extractCoeff (extractF : α → α) : Val α → Val α := valMap extractF

-- ============================================================================
-- Factorial and Falling Factorial
-- ============================================================================

/-- Factorial via valMap. -/
abbrev factorial (factF : α → α) : Val α → Val α := valMap factF

theorem factorial_contents (factF : α → α) (n : α) :
    factorial factF (contents n) = contents (factF n) := rfl

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

theorem tableauCount_contents (countF : α → α) (shape : α) :
    tableauCount countF (contents shape) = contents (countF shape) := rfl

-- ============================================================================
-- Matroids
-- ============================================================================

/-- A matroid: a ground set with an independence predicate. -/
structure Matroid (α : Type u) where
  ground : α
  independent : α → Prop

/-- Matroid rank: a valMap. -/
abbrev matroidRank (rankF : α → α) : Val α → Val α := valMap rankF

theorem matroidRank_contents (rankF : α → α) (a : α) :
    matroidRank rankF (contents a) = contents (rankF a) := rfl

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

theorem chromatic_contents (chiF : α → α) (g : α) :
    chromaticNumber chiF (contents g) = contents (chiF g) := rfl

/-- Chromatic polynomial: number of proper k-colorings. -/
theorem chromatic_poly_contents (polyF : α → α → α) (g k : α) :
    mul polyF (contents g) (contents k) = contents (polyF g k) := rfl

-- ============================================================================
-- Catalan Numbers
-- ============================================================================

/-- Catalan number: C_n. A valMap. -/
abbrev catalanNumber (catF : α → α) : Val α → Val α := valMap catF

theorem catalan_contents (catF : α → α) (n : α) :
    catalanNumber catF (contents n) = contents (catF n) := rfl

/-- Catalan recurrence: C_{n+1} = Σ C_i · C_{n-i}. Contents accumulation. -/
theorem catalan_recurrence (_addF mulF : α → α → α) (ci cnmi : α) :
    mul mulF (contents ci) (contents cnmi) = contents (mulF ci cnmi) := rfl

-- ============================================================================
-- Inclusion-Exclusion
-- ============================================================================

/-- Inclusion-exclusion: alternating sum stays in contents. -/
theorem inclusion_exclusion_step (addF : α → α → α) (negF : α → α) (pos neg_term : α) :
    add addF (contents pos) (contents (negF neg_term)) =
    contents (addF pos (negF neg_term)) := rfl

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

theorem stirling2_contents (stirF : α → α → α) (n k : α) :
    stirling2 stirF (contents n) (contents k) = contents (stirF n k) := rfl

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

theorem fibonacci_contents (fibF : α → α) (n : α) :
    fibonacci fibF (contents n) = contents (fibF n) := rfl

/-- Fibonacci recurrence: F(n+2) = F(n+1) + F(n). Contents arithmetic. -/
theorem fib_recurrence (addF : α → α → α) (fn fn1 : α) :
    add addF (contents fn1) (contents fn) = contents (addF fn1 fn) := rfl

-- ============================================================================
-- Bell Numbers
-- ============================================================================

/-- Bell number: B_n = Σ S(n,k). A valMap. -/
abbrev bellNumber (bellF : α → α) : Val α → Val α := valMap bellF

theorem bell_contents (bellF : α → α) (n : α) :
    bellNumber bellF (contents n) = contents (bellF n) := rfl

-- ============================================================================
-- Derangements
-- ============================================================================

/-- Derangement count: D(n). A valMap. -/
abbrev derangement (derF : α → α) : Val α → Val α := valMap derF

theorem derangement_contents (derF : α → α) (n : α) :
    derangement derF (contents n) = contents (derF n) := rfl

/-- Derangement recurrence: D(n) = (n-1)(D(n-1) + D(n-2)). Contents arithmetic. -/
theorem derangement_recurrence (mulF addF : α → α → α) (n_minus_1 dn1 dn2 : α) :
    mul mulF (contents n_minus_1) (add addF (contents dn1) (contents dn2)) =
    contents (mulF n_minus_1 (addF dn1 dn2)) := rfl

-- ============================================================================
-- Graph: Trees
-- ============================================================================

/-- Cayley's formula: number of labeled trees on n vertices = n^(n-2). -/
theorem cayley_contents (powF : α → α → α) (n n_minus_2 : α) :
    mul powF (contents n) (contents n_minus_2) = contents (powF n n_minus_2) := rfl

/-- Tree: a connected acyclic graph. Edge count = vertices - 1. -/
theorem tree_edges (addF : α → α → α) (negF : α → α) (v one : α) :
    add addF (contents v) (contents (negF one)) = contents (addF v (negF one)) := rfl

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

theorem matchingSize_contents (matchF : α → α) (g : α) :
    matchingSize matchF (contents g) = contents (matchF g) := rfl

-- ============================================================================
-- Graph: Spanning Trees
-- ============================================================================

/-- Kirchhoff's theorem: number of spanning trees via matrix tree theorem. -/
abbrev spanTreeCount (detF : α → α) : Val α → Val α := valMap detF

theorem spanTreeCount_contents (detF : α → α) (laplacian : α) :
    spanTreeCount detF (contents laplacian) = contents (detF laplacian) := rfl

-- ============================================================================
-- Graph: Flows and Cuts
-- ============================================================================

/-- Max flow = min cut. Both sides are contents. -/
theorem max_flow_min_cut (flow cut : α) (h : flow = cut) :
    (contents flow : Val α) = contents cut := by rw [h]

-- ============================================================================
-- Lattice Paths
-- ============================================================================

/-- Lattice path count: paths from (0,0) to (m,n). -/
theorem lattice_path_contents (pathCountF : α → α → α) (m n : α) :
    mul pathCountF (contents m) (contents n) = contents (pathCountF m n) := rfl

-- ============================================================================
-- Multinomial Coefficients
-- ============================================================================

/-- Multinomial coefficient: n! / (k₁! · k₂! · ... · kₘ!). A valMap. -/
abbrev multinomial (multiF : α → α) : Val α → Val α := valMap multiF

theorem multinomial_contents (multiF : α → α) (args : α) :
    multinomial multiF (contents args) = contents (multiF args) := rfl

-- ============================================================================
-- Möbius Function
-- ============================================================================

/-- Möbius function on a poset: μ(x,y). -/
def mobiusVal (mobiusF : α → α → α) (x y : α) : Val α :=
  contents (mobiusF x y)

/-- Möbius inversion: f(x) = Σ g(y)·μ(y,x). Contents arithmetic. -/
theorem mobius_inversion_step (mulF : α → α → α) (gy myx : α) :
    mul mulF (contents gy) (contents myx) = contents (mulF gy myx) := rfl

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

/-- Second moment method: variance bound implies existence. -/
theorem second_moment_contents (mulF : α → α → α) (invF : α → α) (eX2 eX : α) :
    mul mulF (contents eX2) (inv invF (contents eX)) =
    contents (mulF eX2 (invF eX)) := rfl

end Val
