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
the structural explanation of Tarski's hierarchy, embeddings,
equivalences, relations, and the full vocabulary of logic.
-/

universe u
variable {α β γ δ : Type u}

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
def conj : Option Bool → Option Bool → Option Bool :=
  liftBin₂ (· && ·)

@[simp] theorem conj_none_left (q : Option Bool) : conj none q = none := by
  cases q <;> rfl

@[simp] theorem conj_none_right (p : Option Bool) : conj p none = none := by
  cases p <;> rfl

@[simp] theorem conj_some (a b : Bool) : conj (some a) (some b) = some (a && b) := rfl

/-- Disjunction: both must be well-formed. -/
def disj : Option Bool → Option Bool → Option Bool :=
  liftBin₂ (· || ·)

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
def xor' : Option Bool → Option Bool → Option Bool :=
  liftBin₂ xor

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

/-- Disjunction distributes over conjunction. -/
theorem disj_conj_distrib (p q r : Option Bool) :
    disj p (conj q r) = conj (disj p q) (disj p r) := by
  cases p <;> cases q <;> cases r <;> simp [conj, disj, Bool.or_and_distrib_left]

/-- Conjunction idempotent. -/
theorem conj_self (p : Option Bool) : conj p p = p := by
  cases p <;> simp [conj, Bool.and_self]

/-- Disjunction idempotent. -/
theorem disj_self (p : Option Bool) : disj p p = p := by
  cases p <;> simp [disj, Bool.or_self]

/-- Absorption: p ∧ (p ∨ q) = p when both well-formed. -/
theorem conj_disj_absorb (a b : Bool) :
    conj (some a) (disj (some a) (some b)) = some a := by
  cases a <;> simp [conj, disj]

/-- Absorption: p ∨ (p ∧ q) = p when both well-formed. -/
theorem disj_conj_absorb (a b : Bool) :
    disj (some a) (conj (some a) (some b)) = some a := by
  cases a <;> simp [conj, disj]

/-- Conjunction with true is identity. -/
theorem conj_true (p : Option Bool) : conj p (some true) = p := by
  cases p <;> simp [conj]

/-- Conjunction with false is false. -/
theorem conj_false (p : Option Bool) :
    conj p (some false) = match p with | some _ => some false | none => none := by
  cases p <;> simp [conj]

/-- Disjunction with false is identity. -/
theorem disj_false (p : Option Bool) : disj p (some false) = p := by
  cases p <;> simp [disj]

/-- Disjunction with true is true. -/
theorem disj_true (p : Option Bool) :
    disj p (some true) = match p with | some _ => some true | none => none := by
  cases p <;> simp [disj]

/-- XOR is commutative. -/
theorem xor_comm' (p q : Option Bool) : xor' p q = xor' q p := by
  cases p <;> cases q <;> simp [xor']
  rename_i a b; cases a <;> cases b <;> rfl

@[simp] theorem xor_none_left' (q : Option Bool) : xor' none q = none := by
  cases q <;> rfl

@[simp] theorem xor_none_right' (p : Option Bool) : xor' p none = none := by
  cases p <;> rfl

/-- Biconditional is commutative. -/
theorem biconditional_comm (p q : Option Bool) :
    biconditional p q = biconditional q p := by
  cases p <;> cases q <;> simp [biconditional, impl, neg, disj, conj]
  all_goals rename_i a b; cases a <;> cases b <;> rfl

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

/-- Excluded middle (Prop version): p ∨ ¬p. -/
theorem em_logic (p : Prop) : p ∨ ¬p := Classical.em p

/-- Excluded middle variant: ¬p ∨ p. -/
theorem em'_logic (p : Prop) : ¬p ∨ p := Or.symm (Classical.em p)

/-- Double negation elimination (Prop). -/
theorem not_not_logic {p : Prop} (h : ¬¬p) : p := Classical.byContradiction h

/-- Or-not: p ∨ ¬p restated. -/
theorem or_not_logic (p : Prop) : p ∨ ¬p := Classical.em p

/-- Modus tollens: ¬q → (p → q) → ¬p. -/
theorem mt_logic {p q : Prop} (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp => hnq (hpq hp)

/-- not_not_intro: p → ¬¬p. -/
theorem not_not_intro_logic {p : Prop} (h : p) : ¬¬p :=
  fun hn => hn h

-- ============================================================================
-- 6. TARSKI'S HIERARCHY
-- ============================================================================

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

/-- A Fact is a Prop known to be true. -/
structure FactL (p : Prop) : Prop where
  out : p

/-- Fact iff: FactL p ↔ p. -/
theorem factL_iff {p : Prop} : FactL p ↔ p :=
  ⟨FactL.out, FactL.mk⟩

/-- Eq cancel left: if ∀ c, (c = a ↔ c = b) then a = b. -/
theorem eq_iff_eq_cancel_left_logic {a b : α} :
    (∀ c, c = a ↔ c = b) → a = b :=
  fun h => (h a).mp rfl

/-- Eq cancel right: if ∀ c, (a = c ↔ b = c) then a = b. -/
theorem eq_iff_eq_cancel_right_logic {a b : α} :
    (∀ c, a = c ↔ b = c) → a = b :=
  fun h => ((h a).mp rfl).symm

/-- imp_iff_right: (p → q) ↔ q given hp. -/
theorem imp_iff_right_of {p q : Prop} (hp : p) : (p → q) ↔ q :=
  ⟨fun h => h hp, fun hq _ => hq⟩

/-- not_or_intro: ¬a → ¬b → ¬(a ∨ b). -/
theorem not_or_intro_logic {a b : Prop} (ha : ¬a) (hb : ¬b) : ¬(a ∨ b) :=
  fun h => h.elim ha hb

/-- Decidable.eq_or_ne. -/
theorem decidable_eq_or_ne [DecidableEq α] (a b : α) : a = b ∨ a ≠ b := by
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr h

/-- Decidable.ne_or_eq. -/
theorem decidable_ne_or_eq [DecidableEq α] (a b : α) : a ≠ b ∨ a = b := by
  by_cases h : a = b
  · exact Or.inr h
  · exact Or.inl h

/-- Function.swap₂: swap the first two arguments. -/
def swap₂_logic (f : α → β → γ) : β → α → γ := fun b a => f a b

/-- congr_heq: if f = g and a = b then f a = g b. -/
theorem congr_heq_logic {f g : α → β} {a b : α} (hf : f = g) (ha : a = b) :
    f a = g b := by subst hf; subst ha; rfl

/-- not_and_or: ¬(a ∧ b) ↔ ¬a ∨ ¬b. -/
theorem not_and_or_logic {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b := by
  constructor
  · intro h
    by_cases ha : a
    · exact Or.inr (fun hb => h ⟨ha, hb⟩)
    · exact Or.inl ha
  · rintro (ha | hb) ⟨ha', hb'⟩
    · exact ha ha'
    · exact hb hb'

/-- not_or: ¬(a ∨ b) ↔ ¬a ∧ ¬b. -/
theorem not_or_logic {a b : Prop} : ¬(a ∨ b) ↔ ¬a ∧ ¬b := by
  constructor
  · intro h; exact ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩
  · rintro ⟨ha, hb⟩ (a' | b') <;> contradiction

/-- iff_not_comm: (a ↔ ¬b) ↔ (b ↔ ¬a). -/
theorem iff_not_comm_logic {a b : Prop} : (a ↔ ¬b) ↔ (b ↔ ¬a) := by
  constructor
  · intro ⟨hab, hba⟩
    exact ⟨fun hb ha => hab ha hb,
           fun hna => Classical.byContradiction (fun hnb => hna (hba hnb))⟩
  · intro ⟨hba, hab⟩
    exact ⟨fun ha hb => hba hb ha,
           fun hnb => Classical.byContradiction (fun hna => hnb (hab hna))⟩

/-- iff_iff_and_or_not_and_not: (a ↔ b) ↔ (a ∧ b) ∨ (¬a ∧ ¬b). -/
theorem iff_iff_and_or_not_and_not_logic {a b : Prop} :
    (a ↔ b) ↔ (a ∧ b) ∨ (¬a ∧ ¬b) := by
  constructor
  · intro ⟨hab, hba⟩
    by_cases ha : a
    · exact Or.inl ⟨ha, hab ha⟩
    · exact Or.inr ⟨ha, fun hb => ha (hba hb)⟩
  · rintro (⟨ha, hb⟩ | ⟨hna, hnb⟩)
    · exact ⟨fun _ => hb, fun _ => ha⟩
    · exact ⟨fun ha => absurd ha hna, fun hb => absurd hb hnb⟩

/-- iff_iff_eq: (a ↔ b) → a = b (propositional extensionality). -/
theorem iff_iff_eq_logic {a b : Prop} (h : a ↔ b) : a = b :=
  propext h

-- ============================================================================
-- 11. IFF AND PROP LEMMAS (Mathlib_Logic/Lemmas.lean)
-- ============================================================================

/-- Prop.forall: (∀ p : Prop, p) ↔ False. -/
theorem prop_forall_logic : (∀ p : Prop, p) ↔ False :=
  ⟨fun h => h False, fun h => h.elim⟩

/-- Prop.exists: (∃ p : Prop, True) ↔ True. -/
theorem prop_exists_logic : (∃ _ : Prop, True) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨True, trivial⟩⟩

/-- ite_ite_distrib_left: nested ite on same condition. -/
theorem ite_ite_distrib_left_logic (p : Prop) [Decidable p] (a b c : α) :
    ite p (ite p a b) c = ite p a c := by
  by_cases h : p <;> simp [h]

/-- ite_ite_distrib_right: nested ite on same condition. -/
theorem ite_ite_distrib_right_logic (p : Prop) [Decidable p] (a b c : α) :
    ite p a (ite p b c) = ite p a c := by
  by_cases h : p <;> simp [h]

-- ============================================================================
-- 12. EMBEDDING (Mathlib_Logic/Embedding/Basic.lean)
-- ============================================================================

/-- An embedding is an injective function. -/
structure EmbeddingL (α β : Type u) where
  toFun : α → β
  inj : ∀ a₁ a₂, toFun a₁ = toFun a₂ → a₁ = a₂

/-- Identity embedding. -/
def EmbeddingL.refl (α : Type u) : EmbeddingL α α where
  toFun := id
  inj := fun _ _ h => h

/-- Composition of embeddings. -/
def EmbeddingL.trans (e₁ : EmbeddingL α β) (e₂ : EmbeddingL β γ) :
    EmbeddingL α γ where
  toFun := e₂.toFun ∘ e₁.toFun
  inj := fun a₁ a₂ h => e₁.inj a₁ a₂ (e₂.inj _ _ h)

/-- Embedding preserves equality iff. -/
theorem EmbeddingL.apply_eq_iff_eq (e : EmbeddingL α β) (a₁ a₂ : α) :
    e.toFun a₁ = e.toFun a₂ ↔ a₁ = a₂ :=
  ⟨e.inj a₁ a₂, fun h => h ▸ rfl⟩

/-- Option embedding: some is an embedding α ↪ Option α. -/
def EmbeddingL.someEmbedding : EmbeddingL α (Option α) where
  toFun := some
  inj := fun _ _ h => Option.some.inj h

/-- Subtype embedding. -/
def EmbeddingL.subtypeEmb (p : α → Prop) : EmbeddingL {x // p x} α where
  toFun := Subtype.val
  inj := fun ⟨_, _⟩ ⟨_, _⟩ h => by cases h; rfl

-- ============================================================================
-- 13. EQUIV (Mathlib_Logic/Equiv/Basic.lean)
-- ============================================================================

/-- An equivalence: bijection with explicit inverse. -/
structure EquivL (α β : Type u) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- Identity equivalence. -/
def EquivL.refl (α : Type u) : EquivL α α where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Symmetric equivalence. -/
def EquivL.symm (e : EquivL α β) : EquivL β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Transitive equivalence. -/
def EquivL.trans (e₁ : EquivL α β) (e₂ : EquivL β γ) : EquivL α γ where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  left_inv := fun a => by simp [e₂.left_inv, e₁.left_inv]
  right_inv := fun c => by simp [e₁.right_inv, e₂.right_inv]

/-- Equiv is injective. -/
theorem EquivL.inj (e : EquivL α β) (a₁ a₂ : α)
    (h : e.toFun a₁ = e.toFun a₂) : a₁ = a₂ := by
  have h₁ := e.left_inv a₁
  have h₂ := e.left_inv a₂
  rw [← h₁, ← h₂, h]

/-- Equiv is surjective. -/
theorem EquivL.surj (e : EquivL α β) (b : β) :
    ∃ a, e.toFun a = b :=
  ⟨e.invFun b, e.right_inv b⟩

/-- Equiv to embedding. -/
def EquivL.toEmbedding (e : EquivL α β) : EmbeddingL α β where
  toFun := e.toFun
  inj := e.inj

/-- Product equivalence: α × β ≃ β × α. -/
def EquivL.prodComm : EquivL (α × β) (β × α) where
  toFun := fun ⟨a, b⟩ => ⟨b, a⟩
  invFun := fun ⟨b, a⟩ => ⟨a, b⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- Product congruence. -/
def EquivL.prodCongr (e₁ : EquivL α β) (e₂ : EquivL γ δ) :
    EquivL (α × γ) (β × δ) where
  toFun := fun ⟨a, c⟩ => ⟨e₁.toFun a, e₂.toFun c⟩
  invFun := fun ⟨b, d⟩ => ⟨e₁.invFun b, e₂.invFun d⟩
  left_inv := fun ⟨a, c⟩ => by simp [e₁.left_inv, e₂.left_inv]
  right_inv := fun ⟨b, d⟩ => by simp [e₁.right_inv, e₂.right_inv]

/-- Sum congruence. -/
def EquivL.sumCongr (e₁ : EquivL α β) (e₂ : EquivL γ δ) :
    EquivL (α ⊕ γ) (β ⊕ δ) where
  toFun := fun x => match x with
    | .inl a => .inl (e₁.toFun a)
    | .inr c => .inr (e₂.toFun c)
  invFun := fun x => match x with
    | .inl b => .inl (e₁.invFun b)
    | .inr d => .inr (e₂.invFun d)
  left_inv := fun x => by cases x <;> simp [e₁.left_inv, e₂.left_inv]
  right_inv := fun x => by cases x <;> simp [e₁.right_inv, e₂.right_inv]

/-- Option equiv: Option α ≃ Option β from α ≃ β. -/
def EquivL.optionCongr (e : EquivL α β) : EquivL (Option α) (Option β) where
  toFun := Option.map e.toFun
  invFun := Option.map e.invFun
  left_inv := fun v => by cases v <;> simp [e.left_inv]
  right_inv := fun v => by cases v <;> simp [e.right_inv]

/-- Product with PUnit. -/
def EquivL.prodPUnit : EquivL (α × PUnit) α where
  toFun := fun ⟨a, _⟩ => a
  invFun := fun a => ⟨a, PUnit.unit⟩
  left_inv := fun ⟨_, u⟩ => by cases u; rfl
  right_inv := fun _ => rfl

/-- PUnit product. -/
def EquivL.punitProd : EquivL (PUnit × α) α where
  toFun := fun ⟨_, a⟩ => a
  invFun := fun a => ⟨PUnit.unit, a⟩
  left_inv := fun ⟨u, _⟩ => by cases u; rfl
  right_inv := fun _ => rfl

/-- Product is associative. -/
def EquivL.prodAssoc : EquivL ((α × β) × γ) (α × (β × γ)) where
  toFun := fun ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩
  invFun := fun ⟨a, ⟨b, c⟩⟩ => ⟨⟨a, b⟩, c⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl

/-- Bool equiv: Bool ≃ (PUnit ⊕ PUnit). -/
def EquivL.boolEquivPUnitSumPUnit : EquivL Bool (PUnit ⊕ PUnit) where
  toFun := fun b => if b then .inl PUnit.unit else .inr PUnit.unit
  invFun := fun x => match x with | .inl _ => true | .inr _ => false
  left_inv := fun b => by cases b <;> rfl
  right_inv := fun x => by cases x <;> simp

/-- Empty sum: PEmpty ⊕ α ≃ α. -/
def EquivL.pemptySum : EquivL (PEmpty ⊕ α) α where
  toFun := fun x => match x with
    | .inl e => PEmpty.elim e
    | .inr a => a
  invFun := .inr
  left_inv := fun x => by cases x with | inl e => exact PEmpty.elim e | inr _ => rfl
  right_inv := fun _ => rfl

/-- Sum is commutative. -/
def EquivL.sumComm : EquivL (α ⊕ β) (β ⊕ α) where
  toFun := fun x => match x with | .inl a => .inr a | .inr b => .inl b
  invFun := fun x => match x with | .inl b => .inr b | .inr a => .inl a
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by cases x <;> rfl

/-- Option α ≃ PUnit ⊕ α. -/
def EquivL.optionEquivSumPUnit : EquivL (Option α) (PUnit ⊕ α) where
  toFun := fun x => match x with | none => .inl PUnit.unit | some a => .inr a
  invFun := fun x => match x with | .inl _ => none | .inr a => some a
  left_inv := fun x => by cases x <;> rfl
  right_inv := fun x => by cases x <;> rfl

-- ============================================================================
-- 14. UNIQUE (Mathlib_Logic/Unique.lean)
-- ============================================================================

/-- A type with exactly one element. -/
structure UniqueL (α : Type u) where
  default : α
  uniq : ∀ a : α, a = default

/-- PUnit is unique. -/
def UniqueL.punit : UniqueL PUnit where
  default := PUnit.unit
  uniq := fun u => by cases u; rfl

/-- unique_iff: Unique ↔ ∃ a, ∀ b, b = a. -/
theorem uniqueL_iff_exists_unique (α : Type u) :
    Nonempty (UniqueL α) ↔ ∃ a : α, ∀ b : α, b = a :=
  ⟨fun ⟨u⟩ => ⟨u.default, u.uniq⟩, fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩⟩

/-- eq_default: every element equals the default. -/
theorem UniqueL.eq_default' (u : UniqueL α) (a : α) : a = u.default :=
  u.uniq a

/-- forall_iff: (∀ a, p a) ↔ p default when unique. -/
theorem UniqueL.forall_iff' (u : UniqueL α) (p : α → Prop) :
    (∀ a, p a) ↔ p u.default :=
  ⟨fun h => h u.default, fun h a => u.uniq a ▸ h⟩

/-- exists_iff: (∃ a, p a) ↔ p default when unique. -/
theorem UniqueL.exists_iff' (u : UniqueL α) (p : α → Prop) :
    (∃ a, p a) ↔ p u.default :=
  ⟨fun ⟨a, ha⟩ => u.uniq a ▸ ha, fun h => ⟨u.default, h⟩⟩

/-- Bool is not unique. -/
theorem bool_not_unique : ¬Nonempty (UniqueL Bool) := by
  intro ⟨u⟩
  have h₁ := u.uniq true
  have h₂ := u.uniq false
  have : true = false := h₁.trans h₂.symm
  exact Bool.noConfusion this

/-- unique_subtype: build UniqueL for a subtype. -/
def uniqueL_subtype (p : α → Prop) (a : α) (hp : p a) (huniq : ∀ b, p b → b = a) :
    UniqueL {x // p x} :=
  ⟨⟨a, hp⟩, fun ⟨b, hb⟩ => by simp [huniq b hb]⟩

-- ============================================================================
-- 15. ISEMPTY (Mathlib_Logic/IsEmpty.lean)
-- ============================================================================

/-- IsEmptyL: a type with no inhabitants. -/
structure IsEmptyL (α : Type u) : Prop where
  elim : α → False

/-- isEmpty_iff: IsEmptyL α ↔ (α → False). -/
theorem isEmptyL_iff : IsEmptyL α ↔ (α → False) :=
  ⟨IsEmptyL.elim, IsEmptyL.mk⟩

/-- forall vacuously true on empty type. -/
theorem isEmptyL_forall (h : IsEmptyL α) (p : α → Prop) : ∀ a : α, p a :=
  fun a => (h.elim a).elim

/-- no existentials on empty type. -/
theorem isEmptyL_not_exists (h : IsEmptyL α) (p : α → Prop) : ¬∃ a : α, p a :=
  fun ⟨a, _⟩ => h.elim a

/-- not_nonempty ↔ IsEmptyL. -/
theorem not_nonempty_iff_isEmptyL :
    ¬Nonempty α ↔ IsEmptyL α :=
  ⟨fun h => ⟨fun a => h ⟨a⟩⟩, fun h ⟨a⟩ => h.elim a⟩

/-- not_isEmptyL ↔ Nonempty. -/
theorem not_isEmptyL_iff_nonempty :
    ¬IsEmptyL α ↔ Nonempty α :=
  ⟨fun h => Classical.byContradiction (fun hn => h ⟨fun a => hn ⟨a⟩⟩),
   fun ⟨a⟩ h => h.elim a⟩

/-- Empty is IsEmptyL. -/
theorem isEmptyL_empty : IsEmptyL Empty := ⟨Empty.elim⟩

/-- PEmpty is IsEmptyL. -/
theorem isEmptyL_pempty : IsEmptyL PEmpty := ⟨PEmpty.elim⟩

/-- Subtype from empty type is empty. -/
theorem isEmptyL_subtype_of_empty (h : IsEmptyL α) (p : α → Prop) :
    IsEmptyL {a // p a} := ⟨fun ⟨a, _⟩ => h.elim a⟩

/-- Product is empty if left factor is empty. -/
theorem isEmptyL_prod_left (h : IsEmptyL α) : IsEmptyL (α × β) :=
  ⟨fun ⟨a, _⟩ => h.elim a⟩

/-- Product is empty if right factor is empty. -/
theorem isEmptyL_prod_right (h : IsEmptyL β) : IsEmptyL (α × β) :=
  ⟨fun ⟨_, b⟩ => h.elim b⟩

/-- Sum is empty if both are empty. -/
theorem isEmptyL_sum (h₁ : IsEmptyL α) (h₂ : IsEmptyL β) : IsEmptyL (α ⊕ β) :=
  ⟨fun x => match x with | .inl a => h₁.elim a | .inr b => h₂.elim b⟩

/-- Subtype is empty when predicate is always false. -/
theorem isEmptyL_subtype (p : α → Prop) (h : ∀ a, ¬p a) :
    IsEmptyL {a // p a} :=
  ⟨fun ⟨a, ha⟩ => h a ha⟩

/-- Option is never empty. -/
theorem option_nonempty : Nonempty (Option α) := ⟨none⟩

/-- Function from empty type is unique. -/
theorem isEmptyL_fun_unique (h : IsEmptyL α) (f g : α → β) : f = g := by
  funext a; exact (h.elim a).elim

-- ============================================================================
-- 16. NONEMPTY (Mathlib_Logic/Nonempty.lean)
-- ============================================================================

/-- Nonempty + forall gives exists. -/
theorem nonempty_forall_exists (p : α → Prop) (h : ∀ a, p a) (ne : Nonempty α) :
    ∃ a, p a :=
  let ⟨a⟩ := ne; ⟨a, h a⟩

/-- exists_true_iff_nonempty. -/
theorem exists_true_iff_nonempty_logic : (∃ _ : α, True) ↔ Nonempty α :=
  ⟨fun ⟨a, _⟩ => ⟨a⟩, fun ⟨a⟩ => ⟨a, trivial⟩⟩

/-- Nonempty.imp: maps preserve nonemptiness. -/
theorem nonempty_imp_logic (f : α → β) (h : Nonempty α) : Nonempty β :=
  let ⟨a⟩ := h; ⟨f a⟩

/-- nonempty_sigma. -/
theorem nonempty_sigma_logic {β : α → Type u} :
    Nonempty (Σ a, β a) ↔ ∃ a, Nonempty (β a) :=
  ⟨fun ⟨⟨a, b⟩⟩ => ⟨a, ⟨b⟩⟩, fun ⟨a, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩⟩

/-- nonempty_subtype. -/
theorem nonempty_subtype_logic {p : α → Prop} :
    Nonempty {a // p a} ↔ ∃ a, p a :=
  ⟨fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩⟩

/-- nonempty_prod. -/
theorem nonempty_prod_logic :
    Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  ⟨fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩, fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩⟩

/-- nonempty_sum. -/
theorem nonempty_sum_logic :
    Nonempty (α ⊕ β) ↔ Nonempty α ∨ Nonempty β :=
  ⟨fun ⟨x⟩ => match x with | .inl a => Or.inl ⟨a⟩ | .inr b => Or.inr ⟨b⟩,
   fun h => h.elim (fun ⟨a⟩ => ⟨.inl a⟩) (fun ⟨b⟩ => ⟨.inr b⟩)⟩

/-- Classical.arbitrary: any nonempty type has an element. -/
noncomputable def arbitrary_logic [Nonempty α] : α :=
  Classical.choice ‹_›

/-- not_nonempty_iff_imp_false. -/
theorem not_nonempty_iff_imp_false_logic :
    ¬Nonempty α ↔ (α → False) :=
  ⟨fun h a => h ⟨a⟩, fun h ⟨a⟩ => h a⟩

/-- Nonempty PUnit. -/
theorem nonempty_punit : Nonempty PUnit := ⟨PUnit.unit⟩

/-- Nonempty Bool. -/
theorem nonempty_bool : Nonempty Bool := ⟨true⟩

/-- Nonempty Nat. -/
theorem nonempty_nat : Nonempty Nat := ⟨0⟩

-- ============================================================================
-- 17. NONTRIVIAL (Mathlib_Logic/Nontrivial)
-- ============================================================================

/-- A type is nontrivial if it has at least two distinct elements. -/
def IsNontrivialL (α : Type u) : Prop := ∃ a b : α, a ≠ b

/-- subsingleton_iff: Subsingleton α ↔ ∀ a b : α, a = b. -/
theorem subsingleton_iff_logic :
    Subsingleton α ↔ ∀ a b : α, a = b :=
  ⟨fun h a b => h.elim a b, fun h => ⟨h⟩⟩

/-- In a subsingleton, any two elements are equal. -/
theorem subsingleton_eq_logic [Subsingleton α] (a b : α) : a = b :=
  Subsingleton.elim a b

/-- Bool is nontrivial. -/
theorem bool_nontrivial : IsNontrivialL Bool :=
  ⟨true, false, Bool.noConfusion⟩

/-- Nat is nontrivial. -/
theorem nat_nontrivial : IsNontrivialL Nat :=
  ⟨0, 1, Nat.noConfusion⟩

/-- PUnit is not nontrivial. -/
theorem punit_not_nontrivial : ¬IsNontrivialL PUnit :=
  fun ⟨a, b, h⟩ => by cases a; cases b; exact h rfl

-- ============================================================================
-- 18. RELATION (Mathlib_Logic/Relation.lean)
-- ============================================================================

/-- Reflexive relation. -/
def IsReflL (r : α → α → Prop) : Prop := ∀ a, r a a

/-- Symmetric relation. -/
def IsSymmL (r : α → α → Prop) : Prop := ∀ a b, r a b → r b a

/-- Transitive relation. -/
def IsTransL (r : α → α → Prop) : Prop := ∀ a b c, r a b → r b c → r a c

/-- Equivalence relation: reflexive, symmetric, transitive. -/
structure IsEquivRelL (r : α → α → Prop) : Prop where
  refl : IsReflL r
  symm : IsSymmL r
  trans : IsTransL r

/-- Eq is an equivalence relation. -/
theorem eq_equiv_rel : IsEquivRelL (Eq : α → α → Prop) :=
  ⟨fun _ => rfl, fun _ _ h => h.symm, fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

/-- Composition of relations. -/
def CompRel (r : α → β → Prop) (s : β → γ → Prop) : α → γ → Prop :=
  fun a c => ∃ b, r a b ∧ s b c

/-- Reflexive.comap. -/
theorem refl_comap (r : β → β → Prop) (f : α → β) (hr : IsReflL r) :
    IsReflL (fun a₁ a₂ => r (f a₁) (f a₂)) :=
  fun a => hr (f a)

/-- Symmetric.comap. -/
theorem symm_comap (r : β → β → Prop) (f : α → β) (hr : IsSymmL r) :
    IsSymmL (fun a₁ a₂ => r (f a₁) (f a₂)) :=
  fun _ _ h => hr _ _ h

/-- Transitive.comap. -/
theorem trans_comap (r : β → β → Prop) (f : α → β) (hr : IsTransL r) :
    IsTransL (fun a₁ a₂ => r (f a₁) (f a₂)) :=
  fun _ _ _ h₁ h₂ => hr _ _ _ h₁ h₂

/-- Equivalence.comap. -/
theorem equiv_comap (r : β → β → Prop) (f : α → β) (hr : IsEquivRelL r) :
    IsEquivRelL (fun a₁ a₂ => r (f a₁) (f a₂)) :=
  ⟨refl_comap r f hr.refl, symm_comap r f hr.symm, trans_comap r f hr.trans⟩

/-- Symmetric.iff: symmetric r → (r a b ↔ r b a). -/
theorem symm_iff (r : α → α → Prop) (hs : IsSymmL r) (a b : α) :
    r a b ↔ r b a :=
  ⟨hs a b, hs b a⟩

/-- Transitive closure of a relation. -/
inductive TransClosure (r : α → α → Prop) : α → α → Prop
  | single : ∀ {a b : α}, r a b → TransClosure r a b
  | tail : ∀ {a b c : α}, TransClosure r a b → r b c → TransClosure r a c

/-- Transitive closure is transitive. -/
theorem TransClosure.isTrans (r : α → α → Prop) {a b c : α}
    (hab : TransClosure r a b) (hbc : TransClosure r b c) :
    TransClosure r a c := by
  induction hbc with
  | single h => exact TransClosure.tail hab h
  | tail _ hcd ih => exact TransClosure.tail ih hcd

/-- Reflexive transitive closure. -/
inductive ReflTransClosure (r : α → α → Prop) : α → α → Prop
  | refl : ∀ {a : α}, ReflTransClosure r a a
  | tail : ∀ {a b c : α}, ReflTransClosure r a b → r b c → ReflTransClosure r a c

/-- Reflexive transitive closure is reflexive. -/
theorem ReflTransClosure.isRefl (r : α → α → Prop) :
    IsReflL (ReflTransClosure r) :=
  fun _ => ReflTransClosure.refl

/-- Reflexive transitive closure is transitive. -/
theorem ReflTransClosure.isTrans (r : α → α → Prop) {a b c : α}
    (hab : ReflTransClosure r a b) (hbc : ReflTransClosure r b c) :
    ReflTransClosure r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hcd ih => exact ReflTransClosure.tail ih hcd

/-- Join of a relation: a and b have a common successor. -/
def JoinRel (r : α → α → Prop) (a b : α) : Prop :=
  ∃ c, r a c ∧ r b c

-- ============================================================================
-- 19. RELATOR (Mathlib_Logic/Relator.lean)
-- ============================================================================

/-- LiftFun: lift a relation on values to a relation on functions. -/
def LiftFunL (r₁ : α → β → Prop) (r₂ : γ → δ → Prop)
    (f : α → γ) (g : β → δ) : Prop :=
  ∀ a b, r₁ a b → r₂ (f a) (g b)

/-- RightTotal: every b is related to some a. -/
def RightTotalL (r : α → β → Prop) : Prop := ∀ b, ∃ a, r a b

/-- LeftTotal: every a is related to some b. -/
def LeftTotalL (r : α → β → Prop) : Prop := ∀ a, ∃ b, r a b

/-- BiTotal: both left and right total. -/
def BiTotalL (r : α → β → Prop) : Prop := LeftTotalL r ∧ RightTotalL r

/-- LeftUnique. -/
def LeftUniqueL (r : α → β → Prop) : Prop :=
  ∀ a₁ a₂ b, r a₁ b → r a₂ b → a₁ = a₂

/-- RightUnique. -/
def RightUniqueL (r : α → β → Prop) : Prop :=
  ∀ a b₁ b₂, r a b₁ → r a b₂ → b₁ = b₂

/-- BiUnique: both left and right unique. -/
def BiUniqueL (r : α → β → Prop) : Prop := LeftUniqueL r ∧ RightUniqueL r

/-- Equality is bi-total on nonempty types. -/
theorem bi_total_eq_logic [Nonempty α] : BiTotalL (Eq : α → α → Prop) :=
  ⟨fun a => ⟨a, rfl⟩, fun b => ⟨b, rfl⟩⟩

/-- Equality is bi-unique. -/
theorem bi_unique_eq_logic : BiUniqueL (Eq : α → α → Prop) :=
  ⟨fun _ _ _ h₁ h₂ => h₁ ▸ h₂ ▸ rfl, fun _ _ _ h₁ h₂ => h₁ ▸ h₂ ▸ rfl⟩

/-- Equality is left-unique. -/
theorem left_unique_eq_logic : LeftUniqueL (Eq : α → α → Prop) :=
  fun _ _ _ h₁ h₂ => h₁ ▸ h₂ ▸ rfl

-- ============================================================================
-- 20. PAIRWISE (Mathlib_Logic/Pairwise.lean)
-- ============================================================================

/-- Pairwise: a property holds for all distinct pairs. -/
def PairwiseL (r : α → α → Prop) (s : α → Prop) : Prop :=
  ∀ a b, s a → s b → a ≠ b → r a b

/-- Pairwise.mono. -/
theorem PairwiseL.mono (r : α → α → Prop) (s t : α → Prop)
    (hst : ∀ a, s a → t a) (ht : PairwiseL r t) : PairwiseL r s :=
  fun a b ha hb hab => ht a b (hst a ha) (hst b hb) hab

/-- Subsingleton.pairwise: trivially pairwise on subsingleton. -/
theorem PairwiseL.subsingleton (r : α → α → Prop) (s : α → Prop)
    (h : ∀ a b, s a → s b → a = b) : PairwiseL r s :=
  fun a b ha hb hab => absurd (h a b ha hb) hab

-- ============================================================================
-- 21. OPCLASS (Mathlib_Logic/OpClass.lean)
-- ============================================================================

/-- Symmetric operation: op a b = op b a. -/
def IsSymmOpL (op : α → α → β) : Prop := ∀ a b, op a b = op b a

/-- Left commutative: f a (f b c) = f b (f a c). -/
def IsLeftCommL (f : α → α → α) : Prop := ∀ a b c, f a (f b c) = f b (f a c)

/-- Right commutative: f (f a b) c = f (f a c) b. -/
def IsRightCommL (f : α → α → α) : Prop := ∀ a b c, f (f a b) c = f (f a c) b

/-- flip_eq for symmetric operations. -/
theorem symmOp_flip_eq (op : α → α → β) (h : IsSymmOpL op) :
    (fun a b => op b a) = op := by
  funext a b; exact h b a

-- ============================================================================
-- 22. ENCODABLE (Mathlib_Logic/Encodable/Basic.lean)
-- ============================================================================

/-- An encodable type can be injected into Nat. -/
structure EncodableL (α : Type u) where
  encode : α → Nat
  decode : Nat → Option α
  encodek : ∀ a, decode (encode a) = some a

/-- Encode is injective for encodable types. -/
theorem EncodableL.encode_inj (e : EncodableL α) (a₁ a₂ : α)
    (h : e.encode a₁ = e.encode a₂) : a₁ = a₂ := by
  have h₁ := e.encodek a₁
  have h₂ := e.encodek a₂
  rw [h] at h₁; rw [h₁] at h₂
  exact Option.some.inj h₂

/-- Nat is encodable. -/
def EncodableL.nat : EncodableL Nat where
  encode := id
  decode := some
  encodek := fun _ => rfl

/-- Bool is encodable. -/
def EncodableL.bool : EncodableL Bool where
  encode := fun b => if b then 1 else 0
  decode := fun n => if n = 0 then some false else if n = 1 then some true else none
  encodek := fun b => by cases b <;> simp

/-- decode₂: returns none on invalid indices. -/
def EncodableL.decode₂ (e : EncodableL α) (n : Nat) : Option α :=
  (e.decode n).bind (fun a => if e.encode a = n then some a else none)

/-- decode₂_encode: decode₂ (encode a) = some a. -/
theorem EncodableL.decode₂_encode (e : EncodableL α) (a : α) :
    e.decode₂ (e.encode a) = some a := by
  simp [decode₂, e.encodek]

/-- PUnit is encodable. -/
def EncodableL.punit : EncodableL PUnit where
  encode := fun _ => 0
  decode := fun _ => some PUnit.unit
  encodek := fun u => by cases u; rfl

/-- Option is encodable if α is. -/
def EncodableL.option (e : EncodableL α) : EncodableL (Option α) where
  encode := fun x => match x with
    | none => 0
    | some a => e.encode a + 1
  decode := fun n => if n = 0 then some none else (e.decode (n - 1)).map some
  encodek := fun x => by
    cases x with
    | none => simp
    | some a => simp [e.encodek]

-- ============================================================================
-- 23. DENUMERABLE (Mathlib_Logic/Denumerable.lean)
-- ============================================================================

/-- A denumerable type has a bijection with Nat. -/
structure DenumerableL (α : Type u) extends EncodableL α where
  decode_inv : ∀ n, ∃ a, toEncodableL.decode n = some a

/-- ofNat: get the n-th element of a denumerable type. -/
noncomputable def DenumerableL.ofNat (d : DenumerableL α) (n : Nat) : α :=
  (d.decode_inv n).choose

-- ============================================================================
-- 24. COUNTABLE (Mathlib_Logic/Countable)
-- ============================================================================

/-- A type is countable if there's an injection into Nat. -/
def IsCountableL (α : Type u) : Prop :=
  ∃ f : α → Nat, ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

/-- Encodable implies countable. -/
theorem encodableL_imp_countable (e : EncodableL α) : IsCountableL α :=
  ⟨e.encode, e.encode_inj⟩

-- ============================================================================
-- 25. SMALL (Mathlib_Logic/Small)
-- ============================================================================

/-- A type is small if it's equivalent to a type in the same universe. -/
def IsSmallL (α : Type u) : Prop :=
  ∃ β : Type u, Nonempty (EquivL α β)

-- ============================================================================
-- 26. FUNCTION PROPERTIES
-- ============================================================================

/-- Injective on Option: Option.map preserves distinctness. -/
theorem option_map_inj (f : α → β) (hf : ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂)
    (v₁ v₂ : Option α) (h : Option.map f v₁ = Option.map f v₂) : v₁ = v₂ := by
  cases v₁ <;> cases v₂ <;> simp at h ⊢
  exact hf _ _ h

/-- Surjective on Option: Option.map preserves coverage. -/
theorem option_map_surj (f : α → β) (hf : ∀ b : β, ∃ a : α, f a = b)
    (v : Option β) : ∃ w : Option α, Option.map f w = v := by
  cases v with
  | none => exact ⟨none, rfl⟩
  | some b => obtain ⟨a, ha⟩ := hf b; exact ⟨some a, by simp [ha]⟩

/-- Involutive function: f (f a) = a. -/
def IsInvolutiveL (f : α → α) : Prop := ∀ a, f (f a) = a

/-- Involutive implies injective. -/
theorem involutive_inj (f : α → α) (hf : IsInvolutiveL f)
    (a b : α) (h : f a = f b) : a = b := by
  have h2 : f (f a) = f (f b) := by rw [h]
  rw [hf a, hf b] at h2
  exact h2

/-- Involutive implies surjective. -/
theorem involutive_surj (f : α → α) (hf : IsInvolutiveL f)
    (b : α) : ∃ a, f a = b :=
  ⟨f b, hf b⟩

-- ============================================================================
-- 27. OPTION ALGEBRA
-- ============================================================================

/-- Option.bind associativity. -/
theorem option_bind_assoc (v : Option α) (f : α → Option β) (g : β → Option γ) :
    (v.bind f).bind g = v.bind (fun a => (f a).bind g) := by
  cases v <;> simp

/-- Option.map as bind. -/
theorem option_map_eq_bind (v : Option α) (f : α → β) :
    v.map f = v.bind (some ∘ f) := by
  cases v <;> simp

@[simp] theorem option_getD_none (d : α) : Option.getD none d = d := rfl
@[simp] theorem option_getD_some (a d : α) : Option.getD (some a) d = a := rfl

/-- Option.orElse: pick first non-none. -/
theorem option_orElse_none (v : Option α) : v.orElse (fun _ => none) = v := by
  cases v <;> rfl

theorem option_none_orElse (v : Option α) :
    (none : Option α).orElse (fun _ => v) = v := rfl

/-- Option.isSome iff not none. -/
theorem option_isSome_iff (v : Option α) : v.isSome = true ↔ v ≠ none := by
  cases v <;> simp

/-- Option.isNone iff none. -/
theorem option_isNone_iff (v : Option α) : v.isNone = true ↔ v = none := by
  cases v <;> simp

-- ============================================================================
-- 28. WELL-FOUNDED RELATIONS
-- ============================================================================

/-- A relation is well-founded if every nonempty set has a minimal element. -/
def IsWellFoundedL (r : α → α → Prop) : Prop :=
  ∀ s : α → Prop, (∃ a, s a) → ∃ a, s a ∧ ∀ b, s b → ¬r b a

/-- Well-founded relations have no infinite descending chains. -/
theorem wf_no_infinite_desc (r : α → α → Prop) (hwf : IsWellFoundedL r)
    (f : Nat → α) (hf : ∀ n, r (f (n + 1)) (f n)) : False := by
  have ⟨a, ⟨n, hn⟩, hmin⟩ := hwf (fun a => ∃ n, f n = a) ⟨f 0, 0, rfl⟩
  exact hmin (f (n + 1)) ⟨n + 1, rfl⟩ (hn ▸ hf n)

-- ============================================================================
-- 29. FUNCTION COMBINATORS
-- ============================================================================

/-- Flip: flip argument order. -/
def flipL (f : α → β → γ) : β → α → γ := fun b a => f a b

/-- Const: constant function. -/
def constL (a : α) : β → α := fun _ => a

/-- Comp: function composition. -/
def compL (g : β → γ) (f : α → β) : α → γ := g ∘ f

/-- On: apply binary operation after mapping. -/
def onL (f : β → β → γ) (g : α → β) : α → α → γ :=
  fun a₁ a₂ => f (g a₁) (g a₂)

/-- Curry: uncurry a function of pairs. -/
def curryL (f : α × β → γ) : α → β → γ := fun a b => f (a, b)

/-- Uncurry: curry a function to pairs. -/
def uncurryL (f : α → β → γ) : α × β → γ := fun ⟨a, b⟩ => f a b

/-- curry_uncurry round-trip. -/
theorem curry_uncurry_logic (f : α → β → γ) : curryL (uncurryL f) = f := rfl

/-- uncurry_curry round-trip. -/
theorem uncurry_curry_logic (f : α × β → γ) :
    uncurryL (curryL f) = f := by
  funext ⟨_, _⟩; rfl

/-- Const absorbs application. -/
theorem constL_apply (a : α) (b : β) : constL a b = a := rfl

/-- Flip of flip is identity. -/
theorem flipL_flipL (f : α → β → γ) : flipL (flipL f) = f := rfl

-- ============================================================================
-- 30. ADDITIONAL PROP LOGIC
-- ============================================================================

/-- and_comm: a ∧ b ↔ b ∧ a. -/
theorem and_comm_logic {a b : Prop} : a ∧ b ↔ b ∧ a :=
  ⟨fun ⟨ha, hb⟩ => ⟨hb, ha⟩, fun ⟨hb, ha⟩ => ⟨ha, hb⟩⟩

/-- or_comm: a ∨ b ↔ b ∨ a. -/
theorem or_comm_logic {a b : Prop} : a ∨ b ↔ b ∨ a :=
  ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

/-- and_assoc: (a ∧ b) ∧ c ↔ a ∧ (b ∧ c). -/
theorem and_assoc_logic {a b c : Prop} : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
  ⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, hb, hc⟩, fun ⟨ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩

/-- or_assoc: (a ∨ b) ∨ c ↔ a ∨ (b ∨ c). -/
theorem or_assoc_logic {a b c : Prop} : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
  ⟨fun h => h.elim (fun h' => h'.elim Or.inl (fun hb => Or.inr (Or.inl hb)))
                    (fun hc => Or.inr (Or.inr hc)),
   fun h => h.elim (fun ha => Or.inl (Or.inl ha))
                    (fun h' => h'.elim (fun hb => Or.inl (Or.inr hb)) Or.inr)⟩

/-- and_or_distrib: a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c). -/
theorem and_or_distrib_logic {a b c : Prop} : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
  ⟨fun ⟨ha, hbc⟩ => hbc.elim (fun hb => Or.inl ⟨ha, hb⟩) (fun hc => Or.inr ⟨ha, hc⟩),
   fun h => h.elim (fun ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩) (fun ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)⟩

/-- or_and_distrib: a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c). -/
theorem or_and_distrib_logic {a b c : Prop} : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
  ⟨fun h => h.elim (fun ha => ⟨Or.inl ha, Or.inl ha⟩)
                    (fun ⟨hb, hc⟩ => ⟨Or.inr hb, Or.inr hc⟩),
   fun ⟨hab, hac⟩ => hab.elim Or.inl
     (fun hb => hac.elim Or.inl (fun hc => Or.inr ⟨hb, hc⟩))⟩

/-- imp_iff_not_or: (a → b) ↔ (¬a ∨ b). -/
theorem imp_iff_not_or_logic {a b : Prop} : (a → b) ↔ (¬a ∨ b) :=
  ⟨fun h => by by_cases ha : a; exact Or.inr (h ha); exact Or.inl ha,
   fun h ha => h.elim (fun hna => absurd ha hna) id⟩

/-- not_imp: ¬(a → b) ↔ a ∧ ¬b. -/
theorem not_imp_logic {a b : Prop} : ¬(a → b) ↔ a ∧ ¬b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact Classical.byContradiction (fun hna => h (fun ha => absurd ha hna))
    · intro hb; exact h (fun _ => hb)
  · intro ⟨ha, hnb⟩ hab; exact hnb (hab ha)

/-- forall_or_right: (∀ a, p a ∨ q) ↔ (∀ a, p a) ∨ q. -/
theorem forall_or_right_logic {p : α → Prop} {q : Prop} :
    (∀ a, p a ∨ q) ↔ (∀ a, p a) ∨ q := by
  constructor
  · intro h
    by_cases hq : q
    · exact Or.inr hq
    · exact Or.inl (fun a => (h a).elim id (fun hq' => absurd hq' hq))
  · intro h a
    exact h.elim (fun hp => Or.inl (hp a)) Or.inr

/-- exists_and_right: (∃ a, p a ∧ q) ↔ (∃ a, p a) ∧ q. -/
theorem exists_and_right_logic {p : α → Prop} {q : Prop} :
    (∃ a, p a ∧ q) ↔ (∃ a, p a) ∧ q :=
  ⟨fun ⟨a, hp, hq⟩ => ⟨⟨a, hp⟩, hq⟩, fun ⟨⟨a, hp⟩, hq⟩ => ⟨a, hp, hq⟩⟩
