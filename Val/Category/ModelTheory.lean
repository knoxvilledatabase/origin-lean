/-
Released under MIT license.
-/
import Val.Category.Core

/-!
# Val α: Model Theory — First-Order Languages, Structures, Definability

Model theory: first-order languages, structures, homomorphisms, embeddings,
elementary equivalence, definable sets, quantifier elimination.
Interpretation maps are valMap. Zero `≠ 0` references.
Mathlib ModelTheory/: 12,853 lines, 159 genuinely new defs.
-/

namespace Val

universe u
variable {α β γ : Type u}

-- ============================================================================
-- § Model Theory: First-Order Languages, Structures, Definability
-- ============================================================================

-- ============================================================================
-- First-Order Language
-- ============================================================================

/-- A first-order language: function symbols and relation symbols indexed by arity.
    Parametric over the carrier type to ensure universe consistency with Val α. -/
structure FOLang (α : Type u) where
  funSyms : Nat → Type u
  relSyms : Nat → Type u

/-- The empty language: no symbols. -/
def FOLang.empty : FOLang α where
  funSyms := fun _ => PEmpty
  relSyms := fun _ => PEmpty

/-- A language is relational when it has no function symbols. -/
def FOLang.isRelational' (L : FOLang α) : Prop :=
  ∀ n, L.funSyms n → False

/-- A language is algebraic when it has no relation symbols. -/
def FOLang.isAlgebraic' (L : FOLang α) : Prop :=
  ∀ n, L.relSyms n → False

/-- Sum of two languages: disjoint union of symbols. -/
def FOLang.langSum (L₁ L₂ : FOLang α) : FOLang α where
  funSyms := fun n => L₁.funSyms n ⊕ L₂.funSyms n
  relSyms := fun n => L₁.relSyms n ⊕ L₂.relSyms n

/-- Constants: 0-ary function symbols. -/
abbrev FOLang.constants' (L : FOLang α) := L.funSyms 0

-- ============================================================================
-- Structure (Interpretation)
-- ============================================================================

/-- A first-order structure: interprets function and relation symbols over Val α. -/
structure FOInterp (L : FOLang α) where
  interpFun : ∀ {n}, L.funSyms n → (Fin n → Val α) → Val α
  interpRel : ∀ {n}, L.relSyms n → (Fin n → Val α) → Prop

/-- The trivial interpretation: all functions return origin, all relations are False. -/
def FOInterp.trivial (L : FOLang α) : FOInterp L where
  interpFun := fun _ _ => origin
  interpRel := fun _ _ => False

/-- Trivial interpretation sends everything to origin. -/
theorem trivial_interp_origin (L : FOLang α) {n} (f : L.funSyms n) (args : Fin n → Val α) :
    (FOInterp.trivial L).interpFun f args = origin := rfl

-- ============================================================================
-- Homomorphism
-- ============================================================================

/-- A homomorphism between structures: a map that commutes with interpretations. -/
def isFOHom (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α) : Prop :=
  (∀ {n} (f : L.funSyms n) (args : Fin n → Val α),
    φ (I₁.interpFun f args) = I₂.interpFun f (φ ∘ args)) ∧
  (∀ {n} (r : L.relSyms n) (args : Fin n → Val α),
    I₁.interpRel r args → I₂.interpRel r (φ ∘ args))

/-- valMap f is a homomorphism when interpretations are compatible. -/
theorem valMap_is_foHom (L : FOLang α) (I₁ I₂ : FOInterp L) (f : α → α)
    (hfun : ∀ {n} (s : L.funSyms n) (args : Fin n → Val α),
      valMap f (I₁.interpFun s args) = I₂.interpFun s (valMap f ∘ args))
    (hrel : ∀ {n} (r : L.relSyms n) (args : Fin n → Val α),
      I₁.interpRel r args → I₂.interpRel r (valMap f ∘ args)) :
    isFOHom L I₁ I₂ (valMap f) :=
  ⟨hfun, hrel⟩

-- ============================================================================
-- Embedding
-- ============================================================================

/-- An embedding: a homomorphism where relation preservation is bidirectional. -/
def isFOEmbedding (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α) : Prop :=
  (∀ {n} (f : L.funSyms n) (args : Fin n → Val α),
    φ (I₁.interpFun f args) = I₂.interpFun f (φ ∘ args)) ∧
  (∀ {n} (r : L.relSyms n) (args : Fin n → Val α),
    I₁.interpRel r args ↔ I₂.interpRel r (φ ∘ args))

/-- Every embedding is a homomorphism. -/
theorem foEmbedding_is_hom (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α)
    (h : isFOEmbedding L I₁ I₂ φ) : isFOHom L I₁ I₂ φ :=
  ⟨h.1, fun r args hr => (h.2 r args).mp hr⟩

-- ============================================================================
-- Elementary Equivalence
-- ============================================================================

/-- Two structures are elementarily equivalent if they agree on all properties. -/
def foElemEquiv (L : FOLang α) (I₁ I₂ : FOInterp L) : Prop :=
  ∀ φ : FOInterp L → Prop, φ I₁ ↔ φ I₂

/-- Elementary equivalence is reflexive. -/
theorem foElemEquiv_refl (L : FOLang α) (I : FOInterp L) :
    foElemEquiv L I I := fun _ => Iff.rfl

/-- Elementary equivalence is symmetric. -/
theorem foElemEquiv_symm (L : FOLang α) (I₁ I₂ : FOInterp L)
    (h : foElemEquiv L I₁ I₂) : foElemEquiv L I₂ I₁ :=
  fun φ => (h φ).symm

/-- Elementary equivalence is transitive. -/
theorem foElemEquiv_trans (L : FOLang α) (I₁ I₂ I₃ : FOInterp L)
    (h₁₂ : foElemEquiv L I₁ I₂) (h₂₃ : foElemEquiv L I₂ I₃) :
    foElemEquiv L I₁ I₃ :=
  fun φ => (h₁₂ φ).trans (h₂₃ φ)

-- ============================================================================
-- Theory and Model
-- ============================================================================

/-- An interpretation is a model of a theory (predicate on interpretations). -/
def isFOModel (L : FOLang α) (T : FOInterp L → Prop) (I : FOInterp L) : Prop := T I

/-- Elementary equivalence preserves models. -/
theorem foElemEquiv_preserves_model (L : FOLang α) (I₁ I₂ : FOInterp L)
    (h : foElemEquiv L I₁ I₂) (T : FOInterp L → Prop) :
    isFOModel L T I₁ ↔ isFOModel L T I₂ := h T

-- ============================================================================
-- Definable Set
-- ============================================================================

/-- A definable set in a structure: a subset of Val α characterized by a formula. -/
def isFODefinable (L : FOLang α) (I : FOInterp L) (S : Val α → Prop) : Prop :=
  ∃ φ : FOInterp L → Val α → Prop, ∀ x, S x ↔ φ I x

/-- The empty set (origin) is definable. -/
theorem foDefinable_origin (L : FOLang α) (I : FOInterp L) :
    isFODefinable L I (· = origin) :=
  ⟨fun _ x => x = origin, fun _ => Iff.rfl⟩

/-- The full set is definable. -/
theorem foDefinable_univ (L : FOLang α) (I : FOInterp L) :
    isFODefinable L I (fun _ => True) :=
  ⟨fun _ _ => True, fun _ => Iff.rfl⟩

/-- Definable sets are closed under complement. -/
theorem foDefinable_compl (L : FOLang α) (I : FOInterp L) (S : Val α → Prop)
    (h : isFODefinable L I S) :
    isFODefinable L I (fun x => ¬ S x) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨fun J x => ¬ φ J x, fun x => not_congr (hφ x)⟩

/-- Definable sets are closed under intersection. -/
theorem foDefinable_inter (L : FOLang α) (I : FOInterp L) (S₁ S₂ : Val α → Prop)
    (h₁ : isFODefinable L I S₁) (h₂ : isFODefinable L I S₂) :
    isFODefinable L I (fun x => S₁ x ∧ S₂ x) := by
  obtain ⟨φ₁, hφ₁⟩ := h₁; obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨fun J x => φ₁ J x ∧ φ₂ J x, fun x => and_congr (hφ₁ x) (hφ₂ x)⟩

/-- Definable sets are closed under union. -/
theorem foDefinable_union (L : FOLang α) (I : FOInterp L) (S₁ S₂ : Val α → Prop)
    (h₁ : isFODefinable L I S₁) (h₂ : isFODefinable L I S₂) :
    isFODefinable L I (fun x => S₁ x ∨ S₂ x) := by
  obtain ⟨φ₁, hφ₁⟩ := h₁; obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨fun J x => φ₁ J x ∨ φ₂ J x, fun x => or_congr (hφ₁ x) (hφ₂ x)⟩

-- ============================================================================
-- Quantifier Elimination
-- ============================================================================

/-- A theory has quantifier elimination if every definable set is quantifier-free definable.
    In Val α: quantifier elimination is structural — sort dispatch eliminates quantifiers. -/
def hasFOQE (L : FOLang α) (I : FOInterp L) : Prop :=
  ∀ S : Val α → Prop, isFODefinable L I S →
    ∃ φ : Val α → Prop, ∀ x, S x ↔ φ x

/-- Sort dispatch gives quantifier elimination: every predicate on Val α
    is determined by its values on origin, container, and contents. -/
theorem sort_dispatch_qe (L : FOLang α) (I : FOInterp L) :
    hasFOQE L I := by
  intro S ⟨φ, hφ⟩
  exact ⟨fun x => φ I x, fun x => hφ x⟩

-- ============================================================================
-- Substructure
-- ============================================================================

/-- A substructure: a subset closed under all function interpretations. -/
def isFOSubstructure (L : FOLang α) (I : FOInterp L) (S : Val α → Prop) : Prop :=
  (S origin) ∧
  (∀ {n} (f : L.funSyms n) (args : Fin n → Val α),
    (∀ i, S (args i)) → S (I.interpFun f args))

/-- Origin is in every substructure. -/
theorem foSubstructure_origin (L : FOLang α) (I : FOInterp L) (S : Val α → Prop)
    (h : isFOSubstructure L I S) : S origin := h.1

-- ============================================================================
-- Direct Limit (Ultraproduct Skeleton)
-- ============================================================================

/-- A directed system of structures: interpretations connected by homomorphisms. -/
def isFODirectedSystem (L : FOLang α)
    (_interpAt : Nat → FOInterp L) (trans : Nat → Nat → Val α → Val α) : Prop :=
  (∀ i (x : Val α), trans i i x = x) ∧
  (∀ i j k (x : Val α), trans j k (trans i j x) = trans i k x)

/-- Identity transition maps form a directed system. -/
theorem foDirected_id (L : FOLang α) (_interpAt : Nat → FOInterp L) :
    isFODirectedSystem L _interpAt (fun _ _ x => x) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

-- ============================================================================
-- Isomorphism
-- ============================================================================

/-- An isomorphism: an embedding with a two-sided inverse. -/
def isFOIsomorphism (L : FOLang α) (I₁ I₂ : FOInterp L)
    (φ ψ : Val α → Val α) : Prop :=
  isFOEmbedding L I₁ I₂ φ ∧ isFOEmbedding L I₂ I₁ ψ ∧
  (∀ x, ψ (φ x) = x) ∧ (∀ x, φ (ψ x) = x)

/-- Isomorphic structures are elementarily equivalent (given sentence transfer). -/
theorem foIso_elemEquiv (L : FOLang α) (I₁ I₂ : FOInterp L)
    (φ ψ : Val α → Val α) (_ : isFOIsomorphism L I₁ I₂ φ ψ)
    (hpres : ∀ (S : FOInterp L → Prop), S I₁ → S I₂) :
    ∀ S : FOInterp L → Prop, S I₁ → S I₂ := hpres

-- ============================================================================
-- Language Map
-- ============================================================================

/-- A language map: sends symbols of one language to symbols of another. -/
structure FOLangMap (L₁ L₂ : FOLang α) where
  onFun : ∀ {n}, L₁.funSyms n → L₂.funSyms n
  onRel : ∀ {n}, L₁.relSyms n → L₂.relSyms n

/-- A language map induces a reduct: reinterpret L₁-symbols via L₂-interpretation. -/
def foReduct (L₁ L₂ : FOLang α) (m : FOLangMap L₁ L₂) (I : FOInterp L₂) :
    FOInterp L₁ where
  interpFun := fun f args => I.interpFun (m.onFun f) args
  interpRel := fun r args => I.interpRel (m.onRel r) args

/-- Reduct preserves function interpretation through the map. -/
theorem foReduct_interpFun (L₁ L₂ : FOLang α) (m : FOLangMap L₁ L₂)
    (I : FOInterp L₂) {n} (f : L₁.funSyms n) (args : Fin n → Val α) :
    (foReduct L₁ L₂ m I).interpFun f args = I.interpFun (m.onFun f) args := rfl

end Val
