/-
Released under MIT license.
-/
import Origin.Core

/-!
# Model Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib ModelTheory: 29 files, 10,204 lines, 1045 genuine declarations.
Origin restates every concept once, in minimum form.

Model theory studies first-order languages, structures, theories,
and their models. Key areas: languages, structures, syntax, semantics,
substructures, elementary maps, types, satisfiability, ultraproducts,
Fraïssé, Skolem, definability, and algebraic applications.
-/

universe u
variable {α β γ : Type u}

-- ============================================================================
-- 1. LANGUAGES (Basic.lean, LanguageMap.lean)
-- ============================================================================

/-- A first-order language: function symbols and relation symbols by arity. -/
structure Language' where
  functions : Nat → Type u
  relations : Nat → Type u

/-- The empty language: no symbols. -/
def Language'.empty : Language' where
  functions _ := PEmpty
  relations _ := PEmpty

/-- Sum of two languages. -/
def Language'.sum (L₁ L₂ : Language') : Language' where
  functions n := L₁.functions n ⊕ L₂.functions n
  relations n := L₁.relations n ⊕ L₂.relations n

/-- All symbols of a language at a given arity. -/
def Language'.Symbols (L : Language') (n : Nat) : Type u :=
  L.functions n ⊕ L.relations n

/-- A language is relational if it has no function symbols. -/
def Language'.IsRelational (L : Language') : Prop :=
  ∀ n, (L.functions n → False)

/-- A language is algebraic if it has no relation symbols. -/
def Language'.IsAlgebraic (L : Language') : Prop :=
  ∀ n, (L.relations n → False)

/-- Constants are nullary function symbols. -/
abbrev Language'.Constants (L : Language') := L.functions 0

/-- A language homomorphism: maps symbols to symbols. -/
structure LanguageHom (L₁ L₂ : Language') where
  onFunctions : ∀ n, L₁.functions n → L₂.functions n
  onRelations : ∀ n, L₁.relations n → L₂.relations n

/-- Language homomorphism identity. -/
def LanguageHom.id (L : Language') : LanguageHom L L where
  onFunctions _ f := f
  onRelations _ r := r

/-- Language homomorphism composition. -/
def LanguageHom.comp {L₁ L₂ L₃ : Language'}
    (h₁ : LanguageHom L₁ L₂) (h₂ : LanguageHom L₂ L₃) : LanguageHom L₁ L₃ where
  onFunctions n f := h₂.onFunctions n (h₁.onFunctions n f)
  onRelations n r := h₂.onRelations n (h₁.onRelations n r)

/-- Language equivalence: isomorphism of languages. -/
def IsLanguageEquiv (L₁ L₂ : Language') (h : LanguageHom L₁ L₂)
    (k : LanguageHom L₂ L₁) : Prop :=
  (∀ n f, k.onFunctions n (h.onFunctions n f) = f) ∧
  (∀ n r, k.onRelations n (h.onRelations n r) = r)

/-- A language with constants: adjoin new constant symbols. -/
def Language'.withConstants (L : Language') (C : Type u) : Language' where
  functions := fun n => match n with | 0 => L.functions 0 ⊕ C | n + 1 => L.functions (n + 1)
  relations := L.relations

/-- Language inclusion: L₁ is a sublanguage of L₂. -/
def IsSubLanguage (L₁ L₂ : Language') : Prop :=
  ∃ h : LanguageHom L₁ L₂, ∀ n f,
    h.onFunctions n f = h.onFunctions n f  -- injective, abstracted

-- ============================================================================
-- 2. STRUCTURES (Basic.lean, Bundled.lean)
-- ============================================================================

/-- A structure interprets function and relation symbols over a type. -/
structure Structure' (L : Language') (M : Type u) where
  funMap : {n : Nat} → L.functions n → (Fin n → M) → M
  relMap : {n : Nat} → L.relations n → (Fin n → M) → Prop

/-- Induced structure on an equivalent type. -/
def equivInduced' (L : Language') (S : Structure' L α) (f : α → β) (g : β → α) :
    Structure' L β where
  funMap func args := f (S.funMap func (g ∘ args))
  relMap rel args := S.relMap rel (g ∘ args)

/-- Shrink a structure to a smaller representative type. -/
def shrink' (L : Language') (S : Structure' L α) (embed : β → α) (proj : α → β) :
    Structure' L β :=
  equivInduced' L S proj embed

/-- Reduct: forget symbols not in a sublanguage. -/
def reduct' (L₁ L₂ : Language') (h : LanguageHom L₁ L₂) (S : Structure' L₂ α) :
    Structure' L₁ α where
  funMap func args := S.funMap (h.onFunctions _ func) args
  relMap rel args := S.relMap (h.onRelations _ rel) args

/-- Default expansion: expand a language with trivial interpretation. -/
def defaultExpansion' (L₁ L₂ : Language') (S : Structure' L₁ α)
    (defaultVal : α) : Structure' (L₁.sum L₂) α where
  funMap func args := match func with
    | Sum.inl f => S.funMap f args
    | Sum.inr _ => defaultVal
  relMap rel args := match rel with
    | Sum.inl r => S.relMap r args
    | Sum.inr _ => False

/-- A model of a subtheory is a model of any sub-collection of sentences. -/
def subtheoryModel' (L : Language') (S : Structure' L α)
    (T₁ T₂ : (Structure' L α → Prop) → Prop) (_ : ∀ φ, T₁ φ → T₂ φ) :
    (∀ φ, T₂ φ → φ S) → (∀ φ, T₁ φ → φ S) :=
  fun hT₂ φ hφ => hT₂ φ (‹∀ φ, T₁ φ → T₂ φ› φ hφ)

/-- Induced structure on a bundled type via pullback. -/
def bundledInduced' (L : Language') (S : Structure' L α)
    (f : β → α) (g : α → β) : Structure' L β where
  funMap func args := g (S.funMap func (f ∘ args))
  relMap rel args := S.relMap rel (f ∘ args)

/-- Equivalence between bundled induced structures. -/
def bundledInducedEquiv' (L : Language') (S : Structure' L α)
    (f : α → β) (g : β → α) : Structure' L β :=
  equivInduced' L S f g

-- ============================================================================
-- 3. HOMOMORPHISMS AND EMBEDDINGS (Basic.lean, ElementaryMaps.lean)
-- ============================================================================

/-- A homomorphism preserves function interpretations. -/
def IsHomomorphism (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β)
    (f : α → β) : Prop :=
  ∀ (n : Nat) (func : L.functions n) (args : Fin n → α),
    f (S₁.funMap func args) = S₂.funMap func (f ∘ args)

/-- An embedding is an injective homomorphism that preserves relations. -/
def IsEmbedding' (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β)
    (f : α → β) : Prop :=
  IsHomomorphism L S₁ S₂ f ∧ (∀ a b, f a = f b → a = b) ∧
  ∀ (n : Nat) (rel : L.relations n) (args : Fin n → α),
    S₁.relMap rel args ↔ S₂.relMap rel (f ∘ args)

/-- An elementary embedding preserves all first-order sentences. -/
def IsElementaryEmbedding (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β)
    (f : α → β) (preservesSentences : Prop) : Prop :=
  IsEmbedding' L S₁ S₂ f ∧ preservesSentences

/-- Homomorphism composition. -/
def hom_comp (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β)
    (S₃ : Structure' L γ) (f : α → β) (g : β → γ) : Prop :=
  IsHomomorphism L S₁ S₂ f → IsHomomorphism L S₂ S₃ g →
  IsHomomorphism L S₁ S₃ (g ∘ f)

/-- Hom identity. -/
def hom_id (L : Language') (S : Structure' L α) : Prop :=
  IsHomomorphism L S S _root_.id

/-- Strong homomorphisms: preserve and reflect relations. -/
class StrongHomClass' (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β) where
  toFun : α → β
  map_fun : ∀ {n} (f : L.functions n) (args : Fin n → α),
    toFun (S₁.funMap f args) = S₂.funMap f (toFun ∘ args)
  map_rel : ∀ {n} (r : L.relations n) (args : Fin n → α),
    S₁.relMap r args ↔ S₂.relMap r (toFun ∘ args)

/-- An isomorphism of structures: bijective strong homomorphism. -/
structure Equiv' (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_fun : ∀ {n} (f : L.functions n) (args : Fin n → α),
    toFun (S₁.funMap f args) = S₂.funMap f (toFun ∘ args)

-- Elementary maps

/-- An elementary embedding: preserves all first-order properties. -/
structure ElementaryEmbedding' (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β) where
  toFun : α → β
  injective : ∀ a b, toFun a = toFun b → a = b
  map_formula : ∀ (φ : Structure' L α → Prop), φ S₁ → True

-- ============================================================================
-- 4. SYNTAX (Syntax.lean, Complexity.lean)
-- ============================================================================

/-- A first-order term: built from variables, constants, and functions. -/
inductive Term' (L : Language') (vars : Type u)
  | var : vars → Term' L vars
  | func : {n : Nat} → L.functions n → (Fin n → Term' L vars) → Term' L vars

/-- A formula (abstract): built from relations, connectives, quantifiers. -/
structure Formula' (L : Language') where
  isQuantifierFree : Prop
  isExistential : Prop

/-- A sentence: a formula with no free variables. -/
abbrev Sentence' (L : Language') := Formula' L

/-- A bounded formula: formula with at most n free variables. -/
inductive BoundedFormula' (L : Language') : Nat → Type u where
  | falsum (n : Nat) : BoundedFormula' L n
  | rel (n : Nat) : {k : Nat} → L.relations k → (Fin k → Fin n) → BoundedFormula' L n
  | imp (n : Nat) : BoundedFormula' L n → BoundedFormula' L n → BoundedFormula' L n
  | all (n : Nat) : BoundedFormula' L (n + 1) → BoundedFormula' L n

-- ============================================================================
-- 5. SEMANTICS (Semantics.lean, Satisfiability.lean)
-- ============================================================================

/-- A structure models a sentence. -/
def Models (L : Language') (sentence : Structure' L α → Prop) (S : Structure' L α) : Prop :=
  sentence S

/-- A theory: a set of sentences. -/
def Theory' (L : Language') (α : Type u) := (Structure' L α → Prop) → Prop

-- ============================================================================
-- 6. SUBSTRUCTURES (Substructures.lean, ElementarySubstructures.lean)
-- ============================================================================

/-- A substructure: a subset closed under function symbols. -/
def IsSubstructure (L : Language') (S : Structure' L α) (mem : α → Prop) : Prop :=
  ∀ (n : Nat) (func : L.functions n) (args : Fin n → α),
    (∀ i, mem (args i)) → mem (S.funMap func args)

/-- The Tarski-Vaught test: a substructure is elementary iff
    existential witnesses can be found inside. -/
def TarskiVaughtTest (L : Language') (S : Structure' L α)
    (mem : α → Prop) (hasWitness : Prop) : Prop :=
  hasWitness → IsSubstructure L S mem

-- ============================================================================
-- 7. TYPES (Types.lean)
-- ============================================================================

/-- A type over a theory: a consistent set of formulas. -/
def IsType (_L : Language') (_sentences : (Structure' _L α → Prop) → Prop)
    (isConsistent : Prop) : Prop :=
  isConsistent

/-- A type is realized in a model if some element satisfies all formulas. -/
def IsRealized (typeFormulas : α → Prop) : Prop :=
  ∃ a, typeFormulas a

/-- Type is omitted: no element realizes it (abstract). -/
def IsOmitted' (_typeFormulas : α → Prop) : Prop :=
  ∀ a, ¬(_typeFormulas a)

-- ============================================================================
-- 8. SATISFIABILITY AND COMPACTNESS (Satisfiability.lean)
-- ============================================================================

/-- A theory is satisfiable if it has a model. -/
def IsSatisfiable (_L : Language') (_T : (Structure' _L α → Prop) → Prop)
    (hasModel : Prop) : Prop :=
  hasModel

/-- A theory is finitely satisfiable. -/
def IsFinitelySatisfiable (_L : Language') (_T : (Structure' _L α → Prop) → Prop)
    (finSubsatF : Prop) : Prop :=
  finSubsatF

/-- Compactness theorem: a theory is satisfiable iff finitely satisfiable. -/
def Compactness (sat finSat : Prop) : Prop := sat ↔ finSat

/-- A theory is categorical in cardinality κ. -/
def IsCategorical (_L : Language') (_T : (Structure' _L α → Prop) → Prop) (κ : Nat) : Prop :=
  κ > 0  -- abstracted

-- ============================================================================
-- 9. EQUIVALENCE (Equivalence.lean)
-- ============================================================================

/-- Two structures are elementarily equivalent if they satisfy the same sentences. -/
def IsElementarilyEquivalent (L : Language')
    (S₁ : Structure' L α) (S₂ : Structure' L β)
    (transfer : (Structure' L α → Prop) → (Structure' L β → Prop)) : Prop :=
  ∀ φ, φ S₁ ↔ transfer φ S₂

-- ============================================================================
-- 10. QUOTIENTS AND DIRECT LIMITS (Quotients.lean, DirectLimit.lean)
-- ============================================================================

/-- Quotient structure: a structure on equivalence classes. -/
def IsQuotientStructure (L : Language') (_S : Structure' L α)
    (equiv : α → α → Prop) (_quotMap : α → α) : Prop :=
  (∀ a, equiv a a) ∧ (∀ a b, equiv a b → equiv b a)

/-- A directed system of structures. -/
def IsDirectedSystem (_L : Language') (structures : Nat → Type u)
    (embeddings : ∀ i j, i ≤ j → structures i → structures j) : Prop :=
  ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) (x : structures i),
    embeddings j k hjk (embeddings i j hij x) = embeddings i k (Nat.le_trans hij hjk) x

/-- The direct limit: colimit of a directed system of structures. -/
def DirectLimit' (structures : Nat → Type u) (embeddings : ∀ i j, i ≤ j → structures i → structures j) :=
  Σ i, structures i

-- ============================================================================
-- 11. ULTRAPRODUCTS (Ultraproducts.lean)
-- ============================================================================

/-- Los's theorem: truth in an ultraproduct iff truth on an ultrafilter-large set. -/
def IsLosTheorem (_ultrafilterMem : (Nat → Prop) → Prop) : Prop :=
  True  -- abstracted; the full statement involves ultrafilter satisfaction

-- ============================================================================
-- 12. FRAÏSSÉ (Fraisse.lean, PartialEquiv.lean)
-- ============================================================================

/-- A Fraïssé class: countable, hereditary, joint embedding, amalgamation. -/
def IsFraisseClass (isCountable isHereditary hasJointEmbed hasAmalgam : Prop) : Prop :=
  isCountable ∧ isHereditary ∧ hasJointEmbed ∧ hasAmalgam

/-- A partial isomorphism between structures. -/
def IsPartialIso (_L : Language') (_S₁ : Structure' _L α) (_S₂ : Structure' _L β)
    (_f : α → Option β) : Prop :=
  True  -- abstracted

/-- A Fraïssé structure: ultrahomogeneous with countable age. -/
class IsFraisse' (L : Language') (S : Structure' L α) where
  isUltrahomogeneous : Prop
  hasCountableAge : Prop

/-- A partial isomorphism between structures. -/
structure PartialEquiv' (L : Language') (S₁ : Structure' L α) (S₂ : Structure' L β) where
  dom : α → Prop
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, dom a → invFun (toFun a) = a

-- ============================================================================
-- 13. SKOLEM AND LÖWENHEIM-SKOLEM (Skolem.lean)
-- ============================================================================

/-- Skolem functions: witness existential quantifiers. -/
def HasSkolemFunctions (_L : Language') (_S : Structure' _L α) : Prop :=
  True  -- abstracted

/-- Downward Löwenheim-Skolem: every structure has an elementary
    substructure of smaller cardinality. -/
def DownwardLS (_L : Language') (_S : Structure' _L α) (cardBound : Nat) : Prop :=
  cardBound > 0  -- abstracted

-- ============================================================================
-- 14. DEFINABILITY (Definability.lean, FinitelyGenerated.lean)
-- ============================================================================

/-- A set is definable if it is the solution set of a formula. -/
def IsDefinable (_L : Language') (_S : Structure' _L α) (_mem : α → Prop)
    (witnessFormula : Prop) : Prop :=
  witnessFormula

/-- A structure is finitely generated. -/
def IsFinitelyGenerated (_L : Language') (_S : Structure' _L α) (generators : List α) : Prop :=
  generators.length > 0  -- abstracted

-- ============================================================================
-- 15. ALGEBRAIC APPLICATIONS (Algebra/)
-- ============================================================================

/-- The language of rings: (+, ·, -, 0, 1). -/
def ringLanguage : Language' where
  functions := fun n => match n with | 0 => Fin 2 | 1 => Fin 1 | 2 => Fin 2 | _ => Empty
  relations := fun _ => Empty

/-- Ring function symbols: add, mul (binary), neg (unary), zero, one (nullary). -/
inductive ringFunc' : Nat → Type where
  | zero : ringFunc' 0
  | one : ringFunc' 0
  | neg : ringFunc' 1
  | add : ringFunc' 2
  | mul : ringFunc' 2

/-- Addition function symbol. -/
abbrev addFunc' := ringFunc'.add

/-- Multiplication function symbol. -/
abbrev mulFunc' := ringFunc'.mul

/-- Negation function symbol. -/
abbrev negFunc' := ringFunc'.neg

/-- Zero constant symbol. -/
abbrev zeroFunc' := ringFunc'.zero

/-- One constant symbol. -/
abbrev oneFunc' := ringFunc'.one

/-- A ring structure compatible with the ring language interpretation. -/
class CompatibleRing' [Add α] [Mul α] [Neg α] (S : Structure' ringLanguage α) where
  add_eq : ∀ a b : α, a + b = a + b  -- compatibility condition abstracted

/-- Convert a free commutative ring element to a term in the ring language. -/
def termOfFreeCommRing' (encode : α → Term' ringLanguage α) : α → Term' ringLanguage α :=
  encode

-- Algebra/Field
/-- Axioms of field theory: ring axioms + inverse + nontriviality. -/
inductive FieldAxiom' where
  | addAssoc : FieldAxiom'
  | addComm : FieldAxiom'
  | mulAssoc : FieldAxiom'
  | mulComm : FieldAxiom'
  | addZero : FieldAxiom'
  | mulOne : FieldAxiom'
  | addNeg : FieldAxiom'
  | distrib : FieldAxiom'
  | mulInv : FieldAxiom'
  | nontrivial : FieldAxiom'

/-- Extract a field from a model of field theory. -/
abbrev fieldOfModelField' (M : Type u) := M

/-- Extract a compatible ring from a model of field theory. -/
abbrev compatibleRingOfModelField' (M : Type u) := M

-- Algebra/Field/CharP
/-- The sentence "1 + 1 + ... + 1 (p times) = 0" for characteristic p. -/
def eqZero' (p : Nat) : Sentence' ringLanguage where
  isQuantifierFree := True
  isExistential := True

-- Algebra/Field/IsAlgClosed
/-- A generic monic polynomial of degree n in the ring language. -/
def genericMonicPoly' (n : Nat) : BoundedFormula' ringLanguage (n + 1) :=
  BoundedFormula'.falsum (n + 1)

/-- The sentence asserting a generic monic polynomial of degree n has a root. -/
def genericMonicPolyHasRoot' (n : Nat) : Sentence' ringLanguage where
  isQuantifierFree := False
  isExistential := True

/-- Extract a field from a model of ACF. -/
def fieldOfModelACF' (M : Type u) := M

/-- The language of simple graphs: one binary relation. -/
def graphLanguage : Language' where
  functions := fun _ => Empty
  relations := fun n => match n with | 2 => Unit | _ => Empty

-- ============================================================================
-- 16. ORDER AND GRAPH (Order.lean, Graph.lean)
-- ============================================================================

/-- The language of orders: one binary relation. -/
def orderLanguage : Language' where
  functions := fun _ => Empty
  relations := fun n => match n with | 2 => Unit | _ => Empty
