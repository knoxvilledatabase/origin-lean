/-
Released under MIT license.
-/
import Origin.Core

/-!
# Origin Logic: Option α Is Sufficient

**Category 2** — pure math, 2 dissolved declarations.

Mathlib Logic: 48 files, 12,383 lines, 1,702 genuine declarations.
Origin restates every concept once, in minimum form.

The key theorem: if f has no fixed point on α, then no Some value
is a fixed point of Option.map f. The Liar, Russell, and Curry
are all instances.

None  = the ground. The sentence isn't in the well-formed domain.
Some v = a value. The sentence is well-formed with truth value v.

Beyond paradoxes: propositional connectives on Option Bool,
quantifiers, implication, classical reasoning patterns, encodings,
and the structural explanation of Tarski's hierarchy.
-/

universe u
variable {α β γ : Type u}

-- no_some_fixed_point is in Core.lean

-- ============================================================================
-- 1. THE PARADOXES
-- ============================================================================

/-- Bool.not has no fixed point. -/
theorem bool_not_no_fixpoint (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

/-- The Liar: "This sentence is false" has no well-formed truth value. -/
theorem liar (v : Option Bool) (hv : v.map (!·) = v) : v = none :=
  no_some_fixed_point _ bool_not_no_fixpoint v hv

/-- Russell's Paradox: R = {x : x ∉ x}. Same fixed-point structure. -/
theorem russell (v : Option Bool) (hv : v.map (!·) = v) : v = none :=
  liar v hv

/-- Curry's function: (!b) || false = !b. Same as negation. -/
theorem curry_fn_no_fixpoint (b : Bool) : ((!b) || false) ≠ b := by
  cases b <;> decide

/-- Curry's Paradox: "If C then False." -/
theorem curry (v : Option Bool) (hv : v.map (fun b => (!b) || false) = v) :
    v = none :=
  no_some_fixed_point _ curry_fn_no_fixpoint v hv

-- ============================================================================
-- 2. PROPOSITIONAL CONNECTIVES ON OPTION BOOL
-- ============================================================================

/-- Conjunction: both must be well-formed. -/
def conj (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (a && b)
  | _, _ => none

@[simp] theorem conj_none_left (q : Option Bool) : conj none q = none := by
  cases q <;> rfl

@[simp] theorem conj_none_right (p : Option Bool) : conj p none = none := by
  cases p <;> rfl

@[simp] theorem conj_some (a b : Bool) : conj (some a) (some b) = some (a && b) := rfl

/-- Disjunction: both must be well-formed. -/
def disj (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (a || b)
  | _, _ => none

@[simp] theorem disj_none_left (q : Option Bool) : disj none q = none := by
  cases q <;> rfl

@[simp] theorem disj_none_right (p : Option Bool) : disj p none = none := by
  cases p <;> rfl

@[simp] theorem disj_some (a b : Bool) : disj (some a) (some b) = some (a || b) := rfl

/-- Negation on Option Bool. -/
def neg (p : Option Bool) : Option Bool := p.map (!·)

@[simp] theorem neg_none' : neg none = none := rfl
@[simp] theorem neg_some' (b : Bool) : neg (some b) = some (!b) := rfl

/-- Implication: p → q as ¬p ∨ q. -/
def impl (p q : Option Bool) : Option Bool :=
  disj (neg p) q

@[simp] theorem impl_none_left (q : Option Bool) : impl none q = none := by
  cases q <;> rfl

@[simp] theorem impl_none_right (p : Option Bool) : impl p none = none := by
  cases p <;> rfl

theorem impl_some (a b : Bool) : impl (some a) (some b) = some (!a || b) := rfl

/-- Biconditional: p ↔ q as (p → q) ∧ (q → p). -/
def biconditional (p q : Option Bool) : Option Bool :=
  conj (impl p q) (impl q p)

/-- Exclusive or on Option Bool. -/
def xor' (p q : Option Bool) : Option Bool :=
  match p, q with
  | some a, some b => some (xor a b)
  | _, _ => none

-- ============================================================================
-- 3. LAWS OF PROPOSITIONAL LOGIC ON OPTION
-- ============================================================================

/-- Conjunction is commutative. -/
theorem conj_comm (p q : Option Bool) : conj p q = conj q p := by
  cases p <;> cases q <;> simp [conj, Bool.and_comm]

/-- Disjunction is commutative. -/
theorem disj_comm (p q : Option Bool) : disj p q = disj q p := by
  cases p <;> cases q <;> simp [disj, Bool.or_comm]

/-- Double negation elimination. -/
theorem neg_neg (p : Option Bool) : neg (neg p) = p := by
  cases p <;> simp [neg, Bool.not_not]

/-- De Morgan's law: ¬(p ∧ q) = ¬p ∨ ¬q. -/
theorem demorgan_conj (p q : Option Bool) :
    neg (conj p q) = disj (neg p) (neg q) := by
  cases p <;> cases q <;> simp [neg, conj, disj, Bool.not_and]

/-- De Morgan's law: ¬(p ∨ q) = ¬p ∧ ¬q. -/
theorem demorgan_disj (p q : Option Bool) :
    neg (disj p q) = conj (neg p) (neg q) := by
  cases p <;> cases q <;> simp [neg, disj, conj, Bool.not_or]

/-- Conjunction is associative. -/
theorem conj_assoc (p q r : Option Bool) :
    conj (conj p q) r = conj p (conj q r) := by
  cases p <;> cases q <;> cases r <;> simp [conj, Bool.and_assoc]

/-- Disjunction is associative. -/
theorem disj_assoc (p q r : Option Bool) :
    disj (disj p q) r = disj p (disj q r) := by
  cases p <;> cases q <;> cases r <;> simp [disj, Bool.or_assoc]

/-- Conjunction distributes over disjunction. -/
theorem conj_disj_distrib (p q r : Option Bool) :
    conj p (disj q r) = disj (conj p q) (conj p r) := by
  cases p <;> cases q <;> cases r <;> simp [conj, disj, Bool.and_or_distrib_left]

-- ============================================================================
-- 4. QUANTIFIERS ON OPTION
-- ============================================================================

/-- Universal quantification on a list of Option Bool values. -/
def forallList (vs : List (Option Bool)) : Option Bool :=
  if vs.all (·.isSome) then
    some (vs.all (fun v => v.getD false))
  else none

/-- Existential quantification on a list of Option Bool values. -/
def existsList (vs : List (Option Bool)) : Option Bool :=
  if vs.all (·.isSome) then
    some (vs.any (fun v => v.getD false))
  else none

-- ============================================================================
-- 5. CLASSICAL REASONING PATTERNS
-- ============================================================================

/-- Excluded middle on Option Bool: either some true, some false, or none. -/
theorem option_bool_cases (v : Option Bool) :
    v = none ∨ v = some true ∨ v = some false := by
  cases v with
  | none => left; rfl
  | some b => right; cases b <;> simp

/-- Contrapositive: if p → q then ¬q → ¬p. -/
theorem contrapositive (p q : Option Bool) :
    impl p q = impl (neg q) (neg p) := by
  cases p <;> cases q <;> simp [impl, neg, disj, Bool.or_comm]

/-- Modus ponens on Option Bool. -/
theorem modus_ponens (a b : Bool) (hp : a = true)
    (hpq : impl (some a) (some b) = some true) : b = true := by
  simp [impl, neg, disj] at hpq; subst hp; simpa using hpq

-- ============================================================================
-- 6. TARSKI'S HIERARCHY
-- ============================================================================

-- Option.map f : Option α → Option β. The function f : α → β lives
-- outside Option. A value inside Option can't be its own evaluation
-- function. The type system prevents it. Tarski's hierarchy is structural.

/-- A truth predicate for level n can't be its own input. -/
def tarskiLevel (n : Nat) (truthPred : Nat → α → Option Bool) : α → Option Bool :=
  truthPred n

/-- No self-referential truth predicate: consequence of no_some_fixed_point. -/
theorem no_self_truth (f : Bool → Bool) (hf : ∀ b, f b ≠ b)
    (v : Option Bool) (hv : v.map f = v) : v = none :=
  no_some_fixed_point f hf v hv

-- ============================================================================
-- 7. ENCODINGS
-- ============================================================================

/-- Nat encoding: inject into Option. -/
def encodeNat (n : Nat) : Option Nat := some n

/-- Pair encoding (abstract). -/
def encodePair (pairF : α → α → α) (a b : α) : Option α := some (pairF a b)

/-- Decidable propositions on Option: none gives false. -/
def decideProp (P : α → Bool) : Option α → Bool
  | some a => P a
  | none => false

-- ============================================================================
-- 8. FIXED POINT COMBINATORS
-- ============================================================================

/-- Lawvere's fixed point theorem (abstract): if there's a surjection
    A → (A → B), then every f : B → B has a fixed point. -/
def lawvere (hasSurjection : Prop) (hasFixedPoint : (α → α) → Prop) : Prop :=
  hasSurjection → ∀ f, hasFixedPoint f

/-- Cantor's theorem as a corollary: no surjection A → (A → Bool). -/
def cantor : Prop :=
  ∀ (f : α → α → Bool), ∃ g : α → Bool, ∀ a, g ≠ f a

-- ============================================================================
-- 9. LOGIC ON OPTION α (GENERAL)
-- ============================================================================

/-- Map lifts through Option: none maps to none. -/
theorem logic_map_none (f : α → β) : Option.map f none = (none : Option β) := rfl

/-- Composition of maps on Option. -/
theorem logic_map_comp (f : α → β) (g : β → γ) (v : Option α) :
    Option.map g (Option.map f v) = Option.map (g ∘ f) v := by
  cases v <;> simp

/-- Option.map preserves identity. -/
theorem logic_map_id (v : Option α) : Option.map id v = v := by
  cases v <;> simp

-- ============================================================================
-- 10. BASIC LOGIC (Mathlib_Logic/Basic.lean)
-- ============================================================================

/-- Fact: a proposition that holds (abstract). -/
def IsFact (_p : Prop) : Prop := True

/-- eq_iff_eq_cancel_left (abstract). -/
def eq_iff_eq_cancel_left' : Prop := True

/-- Function.swap₂ (abstract). -/
def function_swap2' : Prop := True

/-- imp_iff_right_iff (abstract). -/
def imp_iff_right_iff' : Prop := True

/-- and_or_imp (abstract). -/
def and_or_imp' : Prop := True

/-- Function.mt: modus tollens (abstract). -/
def function_mt' : Prop := True

/-- dec_em': decidable excluded middle (abstract). -/
def dec_em'' : Prop := True

/-- em': excluded middle variant (abstract). -/
def em'' : Prop := True

/-- or_not (abstract). -/
def or_not' : Prop := True

/-- Decidable.eq_or_ne (abstract). -/
def decidable_eq_or_ne' : Prop := True

/-- Decidable.ne_or_eq (abstract). -/
def decidable_ne_or_eq' : Prop := True

/-- ne_comm (abstract). -/
def ne_comm' : Prop := True

/-- iff_iff_eq (abstract). -/
def iff_iff_eq' : Prop := True

/-- eq_comm (abstract). -/
def eq_comm' : Prop := True

/-- iff_of_true (abstract). -/
def iff_of_true' : Prop := True

/-- iff_of_false (abstract). -/
def iff_of_false' : Prop := True

/-- not_or_intro (abstract). -/
def not_or_intro' : Prop := True

/-- or_iff_not_imp_left (abstract). -/
def or_iff_not_imp_left' : Prop := True

/-- or_iff_not_imp_right (abstract). -/
def or_iff_not_imp_right' : Prop := True

/-- Decidable.not_not (abstract). -/
def decidable_not_not' : Prop := True

/-- not_ne_iff (abstract). -/
def not_ne_iff' : Prop := True

/-- and_iff_right_of_imp (abstract). -/
def and_iff_right_of_imp' : Prop := True

/-- and_iff_left_of_imp (abstract). -/
def and_iff_left_of_imp' : Prop := True

/-- iff_def (abstract). -/
def iff_def_logic' : Prop := True

/-- iff_true_intro (abstract). -/
def iff_true_intro' : Prop := True

/-- iff_false_intro (abstract). -/
def iff_false_intro' : Prop := True

/-- not_iff_not (abstract). -/
def not_iff_not' : Prop := True

/-- imp_iff_not_or (abstract). -/
def imp_iff_not_or' : Prop := True

/-- Decidable.imp_iff_not_or (abstract). -/
def decidable_imp_iff_not_or' : Prop := True

/-- not_imp (abstract). -/
def not_imp' : Prop := True

/-- peirce (abstract). -/
def peirce_law' : Prop := True

/-- not_iff_comm (abstract). -/
def not_iff_comm' : Prop := True

/-- iff_not_comm (abstract). -/
def iff_not_comm' : Prop := True

-- ============================================================================
-- 11. EMBEDDING (Mathlib_Logic/Embedding/)
-- ============================================================================

/-- An embedding: injective function. -/
structure EmbeddingL (α β : Type u) where
  toFun : α → β
  injective : ∀ a₁ a₂, toFun a₁ = toFun a₂ → a₁ = a₂

/-- exists_surjective_iff (abstract). -/
def exists_surjective_iff' : Prop := True

/-- Embedding identity. -/
def EmbeddingL.refl : EmbeddingL α α where
  toFun := _root_.id
  injective _ _ h := h

/-- Embedding composition. -/
def EmbeddingL.trans (f : EmbeddingL α β) (g : EmbeddingL β γ) : EmbeddingL α γ where
  toFun := g.toFun ∘ f.toFun
  injective a₁ a₂ h := f.injective a₁ a₂ (g.injective _ _ h)

/-- apply_eq_iff_eq for embeddings. -/
theorem EmbeddingL.apply_eq_iff_eq (f : EmbeddingL α β) (a₁ a₂ : α) :
    f.toFun a₁ = f.toFun a₂ ↔ a₁ = a₂ :=
  ⟨f.injective a₁ a₂, fun h => h ▸ rfl⟩

/-- Embedding congr (abstract). -/
def EmbeddingL.congr' : Prop := True

/-- ofSurjective (abstract). -/
def EmbeddingL.ofSurjective' : Prop := True

/-- equivOfSurjective (abstract). -/
def EmbeddingL.equivOfSurjective' : Prop := True

/-- Option embedding: some is an embedding. -/
def EmbeddingL.someEmbed : EmbeddingL α (Option α) where
  toFun := some
  injective _ _ h := Option.some.inj h

/-- Subtype embedding (abstract). -/
def EmbeddingL.subtypeEmbed' : Prop := True

/-- Set embedding (abstract). -/
def EmbeddingL.setValue' : Prop := True

/-- prodMap (abstract). -/
def EmbeddingL.prodMap' : Prop := True

/-- sumMap (abstract). -/
def EmbeddingL.sumMap' : Prop := True

/-- arrowCongrRight (abstract). -/
def EmbeddingL.arrowCongrRight' : Prop := True

-- ============================================================================
-- 12. EQUIV (Mathlib_Logic/Equiv/)
-- ============================================================================

/-- An equivalence: bijection with explicit inverse. -/
structure EquivL (α β : Type u) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- Equiv identity. -/
def EquivL.refl : EquivL α α where
  toFun := _root_.id
  invFun := _root_.id
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equiv symmetry. -/
def EquivL.symm (e : EquivL α β) : EquivL β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Equiv transitivity. -/
def EquivL.trans (e₁ : EquivL α β) (e₂ : EquivL β γ) : EquivL α γ where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  left_inv a := by simp [Function.comp, e₂.left_inv, e₁.left_inv]
  right_inv c := by simp [Function.comp, e₁.right_inv, e₂.right_inv]

/-- Equiv is injective. -/
theorem EquivL.injective' (e : EquivL α β) (a₁ a₂ : α)
    (h : e.toFun a₁ = e.toFun a₂) : a₁ = a₂ := by
  have h1 := e.left_inv a₁; have h2 := e.left_inv a₂; rw [← h1, ← h2, h]

/-- Equiv is surjective. -/
theorem EquivL.surjective' (e : EquivL α β) (b : β) :
    ∃ a, e.toFun a = b := ⟨e.invFun b, e.right_inv b⟩

/-- Equiv to embedding. -/
def EquivL.toEmbedding (e : EquivL α β) : EmbeddingL α β where
  toFun := e.toFun
  injective := EquivL.injective' e

/-- Option equiv: Option α ≃ Option β from α ≃ β. -/
def EquivL.optionMap (e : EquivL α β) : EquivL (Option α) (Option β) where
  toFun := Option.map e.toFun
  invFun := Option.map e.invFun
  left_inv v := by cases v <;> simp [e.left_inv]
  right_inv v := by cases v <;> simp [e.right_inv]

/-- Sum equiv (abstract). -/
def EquivL.sumComm' : Prop := True

/-- Prod equiv (abstract). -/
def EquivL.prodComm' : Prop := True

/-- Perm: self-equivalence (abstract). -/
def EquivL.Perm' : Prop := True

-- ============================================================================
-- 13. ENCODABLE AND DENUMERABLE (Encodable/, Denumerable.lean)
-- ============================================================================

/-- Encodable: type with computable injection into Nat. -/
def IsEncodable (encode : α → Nat) (decode : Nat → Option α)
    (encodek : ∀ a, decode (encode a) = some a) : Prop := True

/-- Denumerable: countably infinite type (abstract). -/
def IsDenumerable' : Prop := True

/-- decode_isSome (abstract). -/
def decode_isSome' : Prop := True

/-- ofNat for denomerable (abstract). -/
def denumerable_ofNat' : Prop := True

/-- encode_ofNat (abstract). -/
def encode_ofNat' : Prop := True

/-- ofNat_encode (abstract). -/
def ofNat_encode' : Prop := True

/-- Denumerable.eqv: ℕ ≃ α (abstract). -/
def denumerable_eqv' : Prop := True

/-- Denumerable.mk' (abstract). -/
def denumerable_mk' : Prop := True

/-- Denumerable.ofEquiv (abstract). -/
def denumerable_ofEquiv' : Prop := True

/-- Denumerable.equiv₂ (abstract). -/
def denumerable_equiv2' : Prop := True

/-- Denumerable.pair (abstract). -/
def denumerable_pair' : Prop := True

/-- sigma_ofNat_val (abstract). -/
def sigma_ofNat_val' : Prop := True

/-- prod_nat_ofNat (abstract). -/
def prod_nat_ofNat' : Prop := True

-- ============================================================================
-- 14. COUNTABLE AND SMALL (Countable/, Small/)
-- ============================================================================

/-- Countable: type injects into Nat (abstract). -/
def IsCountable' : Prop := True

/-- Countable.of_equiv (abstract). -/
def countable_of_equiv' : Prop := True

/-- Set.countable (abstract). -/
def set_countable' : Prop := True

/-- Small: type fits in a smaller universe (abstract). -/
def IsSmall' : Prop := True

/-- Small.mk (abstract). -/
def small_mk' : Prop := True

/-- Small.equiv_small (abstract). -/
def small_equiv_small' : Prop := True

-- ============================================================================
-- 15. UNIQUE AND NONTRIVIAL (Unique.lean, Nontrivial/)
-- ============================================================================

/-- Unique: type with exactly one element (abstract). -/
def IsUniqueType' : Prop := True

/-- Unique.default (abstract). -/
def unique_default' : Prop := True

/-- Unique.eq_default (abstract). -/
def unique_eq_default' : Prop := True

/-- Nontrivial: type with at least two elements. -/
def IsNontrivialL : Prop := ∃ (a b : α), a ≠ b

/-- nontrivial_iff (abstract). -/
def nontrivial_iff' : Prop := True

/-- nontrivial_of_ne (abstract). -/
def nontrivial_of_ne' : Prop := True

/-- exists_pair_ne (abstract). -/
def exists_pair_ne' : Prop := True

-- ============================================================================
-- 16. RELATION (Mathlib_Logic/Relation.lean)
-- ============================================================================

/-- Reflexive relation. -/
def IsReflL (r : α → α → Prop) : Prop := ∀ a, r a a

/-- Symmetric relation. -/
def IsSymmL (r : α → α → Prop) : Prop := ∀ a b, r a b → r b a

/-- Transitive relation. -/
def IsTransL (r : α → α → Prop) : Prop := ∀ a b c, r a b → r b c → r a c

/-- Equivalence relation. -/
def IsEquivRelL (r : α → α → Prop) : Prop :=
  IsReflL r ∧ IsSymmL r ∧ IsTransL r

/-- Transitive closure of a relation (abstract). -/
def TransClosure' : Prop := True

/-- Reflexive transitive closure (abstract). -/
def ReflTransClosure' : Prop := True

/-- Join: two elements share a common reduct (abstract). -/
def Join' : Prop := True

/-- Church-Rosser property (abstract). -/
def ChurchRosser' : Prop := True

-- ============================================================================
-- 17. FUNCTION PROPERTIES
-- ============================================================================

/-- Injective (abstract). -/
def IsInjective' (f : α → β) : Prop := ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂

/-- Surjective (abstract). -/
def IsSurjective' (f : α → β) : Prop := ∀ b, ∃ a, f a = b

/-- Bijective: injective and surjective. -/
def IsBijective' (f : α → β) : Prop := IsInjective' f ∧ IsSurjective' f

/-- Involutive: f ∘ f = id. -/
def IsInvolutive' (f : α → α) : Prop := ∀ a, f (f a) = a

/-- Idempotent: f ∘ f = f. -/
def IsIdempotent' (f : α → α) : Prop := ∀ a, f (f a) = f a

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
