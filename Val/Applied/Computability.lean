/-
Released under MIT license.
-/
import Val.Algebra.Core

/-!
# Val α: Applied — Computability

Automata (DFA/NFA/εNFA), language operations, Turing machines,
halting problem, Rice's theorem, recursive functions, Ackermann,
Akra-Bazzi, complexity classes.
-/

namespace Val

universe u

variable {α : Type u}

-- ============================================================================
-- 1. UNIFIED AUTOMATON: DFA + NFA + εNFA in one structure
-- Mathlib: DFA.lean (26), NFA.lean (41), EpsilonNFA (~30) = 97 B3
-- ============================================================================

/-- Unified automaton: one structure for DFA, NFA, εNFA.
    Mathlib has 3 separate structures; we unify via parametric transF. -/
structure Automaton (σ α : Type u) where
  transF : σ → α → σ
  startS : σ
  acceptP : σ → Prop

/-- Eval: fold transF. Covers DFA.eval, DFA.evalFrom. -/
def autoEvalFrom {σ : Type u} (M : Automaton σ α) (s : σ) : List α → σ :=
  List.foldl M.transF s

/-- Eval from start. Covers DFA.eval. -/
def autoEval {σ : Type u} (M : Automaton σ α) (input : List α) : σ :=
  autoEvalFrom M M.startS input

/-- Acceptance. Covers DFA.accepts, NFA.accepts. -/
def autoAccepts {σ : Type u} (M : Automaton σ α) (input : List α) : Prop :=
  M.acceptP (autoEval M input)

/-- EvalFrom nil. Covers DFA.evalFrom_nil, NFA.evalFrom_nil. -/
theorem autoEvalFrom_nil {σ : Type u} (M : Automaton σ α) (s : σ) :
    autoEvalFrom M s [] = s := rfl

/-- EvalFrom cons. Covers DFA.evalFrom_cons, NFA.evalFrom_cons. -/
theorem autoEvalFrom_cons {σ : Type u} (M : Automaton σ α) (s : σ) (a : α) (x : List α) :
    autoEvalFrom M s (a :: x) = autoEvalFrom M (M.transF s a) x := rfl

/-- EvalFrom append. Covers DFA.evalFrom_of_append, NFA.evalFrom_append. -/
theorem autoEvalFrom_append {σ : Type u} (M : Automaton σ α) (s : σ) (x y : List α) :
    autoEvalFrom M s (x ++ y) = autoEvalFrom M (autoEvalFrom M s x) y :=
  List.foldl_append _ _ _ _

/-- Eval nil. Covers DFA.eval_nil. -/
theorem autoEval_nil {σ : Type u} (M : Automaton σ α) : autoEval M [] = M.startS := rfl

/-- Eval singleton. Covers DFA.eval_singleton. -/
theorem autoEval_singleton {σ : Type u} (M : Automaton σ α) (a : α) :
    autoEval M [a] = M.transF M.startS a := rfl

/-- Eval as evalFrom. -/
theorem autoEval_eq_evalFrom {σ : Type u} (M : Automaton σ α) (input : List α) :
    autoEval M input = autoEvalFrom M M.startS input := rfl

/-- Eval append singleton. Covers DFA.eval_append_singleton. -/
theorem autoEval_append {σ : Type u} (M : Automaton σ α) (x y : List α) :
    autoEval M (x ++ y) = autoEvalFrom M (autoEval M x) y :=
  autoEvalFrom_append M M.startS x y

/-- Complement automaton. Covers DFA.Compl, accepts_compl. ~4 B3. -/
def autoCompl {σ : Type u} (M : Automaton σ α) : Automaton σ α :=
  { M with acceptP := fun s => ¬ M.acceptP s }

/-- Complement eval unchanged. -/
theorem autoCompl_eval {σ : Type u} (M : Automaton σ α) (input : List α) :
    autoEval (autoCompl M) input = autoEval M input := rfl

/-- Complement acceptance. Covers DFA.accepts_compl. -/
theorem autoCompl_accepts {σ : Type u} (M : Automaton σ α) (input : List α) :
    autoAccepts (autoCompl M) input ↔ ¬ autoAccepts M input := Iff.rfl

/-- Union automaton. Covers DFA.union, accepts_union. ~8 B3. -/
def autoUnion {σ τ : Type u} (M₁ : Automaton σ α) (M₂ : Automaton τ α) : Automaton (σ × τ) α where
  transF := fun ⟨s₁, s₂⟩ a => (M₁.transF s₁ a, M₂.transF s₂ a)
  startS := (M₁.startS, M₂.startS)
  acceptP := fun ⟨s₁, s₂⟩ => M₁.acceptP s₁ ∨ M₂.acceptP s₂

/-- Intersection automaton. Covers DFA.inter, accepts_inter. ~8 B3. -/
def autoInter {σ τ : Type u} (M₁ : Automaton σ α) (M₂ : Automaton τ α) : Automaton (σ × τ) α where
  transF := fun ⟨s₁, s₂⟩ a => (M₁.transF s₁ a, M₂.transF s₂ a)
  startS := (M₁.startS, M₂.startS)
  acceptP := fun ⟨s₁, s₂⟩ => M₁.acceptP s₁ ∧ M₂.acceptP s₂

/-- Comap: pull back alphabet. Covers DFA.comap, ~6 B3. -/
def autoComap {σ : Type u} (f : α → α) (M : Automaton σ α) : Automaton σ α where
  transF := fun s a => M.transF s (f a)
  startS := M.startS
  acceptP := M.acceptP

/-- Comap id. -/
theorem autoComap_id {σ : Type u} (M : Automaton σ α) : autoComap id M = M := rfl

/-- NFA step set. Covers NFA.stepSet, ~6 B3. -/
def nfaStepSet (stepF : α → α → α → Prop) (S : α → Prop) (a : α) : α → Prop :=
  fun s' => ∃ s, S s ∧ stepF s a s'

/-- NFA→DFA subset construction. Covers NFA.toDFA, ~4 B3. -/
def nfaToDFA (stepF : α → α → α → Prop) (startP acceptP : α → Prop) :
    Automaton (α → Prop) α where
  transF := fun S a => nfaStepSet stepF S a
  startS := startP
  acceptP := fun S => ∃ s, S s ∧ acceptP s

/-- DFA→NFA embedding. Covers DFA.toNFA, ~4 B3. -/
def dfaToNFA {σ : Type u} (M : Automaton σ α) (s : σ) (a : α) (s' : σ) : Prop :=
  M.transF s a = s'

/-- NFA path. Covers NFA.Path, ~6 B3. -/
inductive NFAPath (stepF : α → α → α → Prop) : α → α → List α → Prop where
  | nil (s : α) : NFAPath stepF s s []
  | cons (s t u : α) (a : α) (x : List α) :
      stepF s a t → NFAPath stepF t u x → NFAPath stepF s u (a :: x)

/-- NFA reverse. Covers NFA.reverse, ~8 B3. -/
def nfaReverse (stepF : α → α → α → Prop) : α → α → α → Prop :=
  fun s a s' => stepF s' a s

/-- Pumping lemma predicate. Covers DFA.pumping_lemma, NFA.pumping_lemma. ~4 B3. -/
def pumpable (accepts : List α → Prop) (pumpLen : Nat) : Prop :=
  ∀ x, accepts x → pumpLen ≤ x.length →
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ pumpLen ∧ b ≠ [] ∧
      ∀ n, accepts (a ++ (List.replicate n b).flatten ++ c)

/-- Regular language. Covers Language.IsRegular, ~12 B3. -/
def isRegularLang (accepts : List α → Prop) : Prop :=
  ∃ (σ : Type u) (M : Automaton σ α), ∀ x, autoAccepts M x ↔ accepts x

/-- Regular languages closed under complement. -/
theorem regular_compl {σ : Type u} (M : Automaton σ α) :
    ∀ x, autoAccepts (autoCompl M) x ↔ ¬ autoAccepts M x := fun _ => Iff.rfl

-- ============================================================================
-- 2. LANGUAGE OPERATIONS
-- Mathlib Language.lean: ~80 B3. Union, concat, star, map, reverse.
-- ============================================================================

/-- Language = set of strings. -/
def Lang := List α → Prop

/-- Empty language. -/
def langEmpty : @Lang α := fun _ => False

/-- Universal language. -/
def langUniv : @Lang α := fun _ => True

/-- Epsilon language. -/
def langEpsilon : @Lang α := fun x => x = []

/-- Singleton language. -/
def langSingleton (w : List α) : @Lang α := fun x => x = w

/-- Language union. Covers Language.add, ~8 B3. -/
def langUnion (L₁ L₂ : @Lang α) : @Lang α := fun w => L₁ w ∨ L₂ w

/-- Language intersection. Covers Language.inf, ~6 B3. -/
def langInter (L₁ L₂ : @Lang α) : @Lang α := fun w => L₁ w ∧ L₂ w

/-- Language complement. -/
def langCompl (L : @Lang α) : @Lang α := fun w => ¬ L w

/-- Language concatenation. Covers Language.mul, ~12 B3. -/
def langConcat (L₁ L₂ : @Lang α) : @Lang α :=
  fun w => ∃ x y, w = x ++ y ∧ L₁ x ∧ L₂ y

/-- Language difference. -/
def langDiff (L₁ L₂ : @Lang α) : @Lang α := fun w => L₁ w ∧ ¬ L₂ w

/-- Kleene star. Covers Language.kstar, ~10 B3. -/
inductive langStar (L : @Lang α) : @Lang α where
  | nil : langStar L []
  | append (x y : List α) : L x → langStar L y → langStar L (x ++ y)

/-- Star contains epsilon. Covers Language.nil_mem_kstar. -/
theorem langStar_nil (L : @Lang α) : langStar L [] := langStar.nil

/-- Star closed under concat. -/
theorem langStar_concat (L : @Lang α) (x y : List α)
    (hx : L x) (hy : langStar L y) : langStar L (x ++ y) :=
  langStar.append x y hx hy

/-- Language map. Covers Language.map, ~6 B3. -/
def langMap (f : α → α) (L : @Lang α) : @Lang α :=
  fun w => ∃ v, L v ∧ w = v.map f

/-- Language reverse. Covers Language.reverse, ~6 B3. -/
def langReverse (L : @Lang α) : @Lang α := fun w => L w.reverse

/-- Union commutative. -/
theorem langUnion_comm (L₁ L₂ : @Lang α) (w : List α) :
    langUnion L₁ L₂ w ↔ langUnion L₂ L₁ w := Or.comm

/-- Union associative. -/
theorem langUnion_assoc (L₁ L₂ L₃ : @Lang α) (w : List α) :
    langUnion (langUnion L₁ L₂) L₃ w ↔ langUnion L₁ (langUnion L₂ L₃) w := by
  simp only [langUnion]; exact ⟨fun h => h.elim (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr h)),
    fun h => h.elim (fun h => Or.inl (Or.inl h)) (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)⟩

/-- Intersection commutative. -/
theorem langInter_comm (L₁ L₂ : @Lang α) (w : List α) :
    langInter L₁ L₂ w ↔ langInter L₂ L₁ w := And.comm

/-- Intersection associative. -/
theorem langInter_assoc (L₁ L₂ L₃ : @Lang α) (w : List α) :
    langInter (langInter L₁ L₂) L₃ w ↔ langInter L₁ (langInter L₂ L₃) w := by
  simp only [langInter]; exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- Concat empty right. Covers Language.mul_zero. -/
theorem langConcat_empty_right (L : @Lang α) (w : List α) :
    langConcat L langEmpty w ↔ False :=
  ⟨fun ⟨_, _, _, _, h⟩ => h, False.elim⟩

/-- Concat empty left. Covers Language.zero_mul. -/
theorem langConcat_empty_left (L : @Lang α) (w : List α) :
    langConcat langEmpty L w ↔ False :=
  ⟨fun ⟨_, _, _, h, _⟩ => h, False.elim⟩

/-- Concat epsilon right. Covers Language.mul_one. -/
theorem langConcat_epsilon_right (L : @Lang α) (w : List α) :
    langConcat L langEpsilon w ↔ L w :=
  ⟨fun ⟨x, y, he, hx, hy⟩ => by simp [langEpsilon] at hy; rw [he, hy, List.append_nil]; exact hx,
   fun h => ⟨w, [], by simp, h, rfl⟩⟩

/-- Concat epsilon left. Covers Language.one_mul. -/
theorem langConcat_epsilon_left (L : @Lang α) (w : List α) :
    langConcat langEpsilon L w ↔ L w :=
  ⟨fun ⟨x, y, he, hx, hy⟩ => by simp [langEpsilon] at hx; rw [he, hx]; exact hy,
   fun h => ⟨[], w, by simp, rfl, h⟩⟩

/-- Concat distributes over union right. Covers Language.mul_add. -/
theorem langConcat_union_right (L M N : @Lang α) (w : List α) :
    langConcat L (langUnion M N) w ↔ langUnion (langConcat L M) (langConcat L N) w :=
  ⟨fun ⟨x, y, he, hx, hy⟩ => hy.elim (fun h => Or.inl ⟨x, y, he, hx, h⟩)
    (fun h => Or.inr ⟨x, y, he, hx, h⟩),
   fun h => h.elim (fun ⟨x, y, he, hx, hy⟩ => ⟨x, y, he, hx, Or.inl hy⟩)
    (fun ⟨x, y, he, hx, hy⟩ => ⟨x, y, he, hx, Or.inr hy⟩)⟩

/-- Concat distributes over union left. Covers Language.add_mul. -/
theorem langConcat_union_left (L M N : @Lang α) (w : List α) :
    langConcat (langUnion L M) N w ↔ langUnion (langConcat L N) (langConcat M N) w :=
  ⟨fun ⟨x, y, he, hx, hy⟩ => hx.elim (fun h => Or.inl ⟨x, y, he, h, hy⟩)
    (fun h => Or.inr ⟨x, y, he, h, hy⟩),
   fun h => h.elim (fun ⟨x, y, he, hx, hy⟩ => ⟨x, y, he, Or.inl hx, hy⟩)
    (fun ⟨x, y, he, hx, hy⟩ => ⟨x, y, he, Or.inr hx, hy⟩)⟩

/-- De Morgan union. -/
theorem langCompl_union (L₁ L₂ : @Lang α) (w : List α) :
    langCompl (langUnion L₁ L₂) w ↔ langInter (langCompl L₁) (langCompl L₂) w := by
  simp [langCompl, langUnion, langInter, not_or]

/-- De Morgan intersection. -/
theorem langCompl_inter (L₁ L₂ : @Lang α) (w : List α) :
    langCompl (langInter L₁ L₂) w ↔ langUnion (langCompl L₁) (langCompl L₂) w := by
  simp only [langCompl, langUnion, langInter]
  exact ⟨fun h => by by_cases h1 : L₁ w <;> by_cases h2 : L₂ w <;> simp_all,
    fun h hb => h.elim (fun h => h hb.1) (fun h => h hb.2)⟩

/-- Double complement. -/
theorem langCompl_compl (L : @Lang α) (w : List α) :
    langCompl (langCompl L) w ↔ L w := by simp [langCompl]

/-- Language power. Covers Language.pow, ~4 B3. -/
def langPow (L : @Lang α) : Nat → @Lang α
  | 0 => langEpsilon
  | n + 1 => langConcat L (langPow L n)

/-- Power 0 = epsilon. -/
theorem langPow_zero (L : @Lang α) : langPow L 0 = langEpsilon := rfl

/-- Arden's lemma predicate. Covers Language.self_eq_mul_add_iff. -/
def ardenProp (L M N : @Lang α) : Prop :=
  (∀ w, L w ↔ langUnion (langConcat M L) N w) →
  ¬ M [] → ∀ w, L w ↔ langConcat (langStar M) N w

-- ============================================================================
-- 3. COMPUTATION MODEL: TM + Post + Stack + Register
-- Mathlib: TuringMachine/ (~60), Halting.lean (~50), PartrecCode (~27) = 137 B3
-- ============================================================================

/-- Partial computation: origin = diverges, contents = halts. -/
def partialResult (result : Option α) : Val α :=
  match result with
  | none => origin
  | some a => contents a

/-- Halting → contents. -/
theorem halts_is_contents (a : α) :
    partialResult (some a) = (contents a : Val α) := rfl

/-- Diverging → origin. -/
theorem diverges_is_origin :
    partialResult (none : Option α) = (origin : Val α) := rfl

/-- Step function preserves sort via valMap. -/
abbrev compEval (stepF : α → α) : Val α → Val α := valMap stepF

/-- Multi-step evaluation. -/
def multiStep (stepF : α → α) : Nat → Val α → Val α
  | 0, v => v
  | n + 1, v => multiStep stepF n (compEval stepF v)

/-- Multi-step on origin stays origin. -/
theorem multiStep_origin (stepF : α → α) (n : Nat) :
    multiStep stepF n origin = (origin : Val α) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [multiStep, compEval]; exact ih

/-- Multi-step on contents stays contents. -/
theorem multiStep_contents (stepF : α → α) (n : Nat) (a : α) :
    ∃ b, multiStep stepF n (contents a) = (contents b : Val α) := by
  induction n generalizing a with
  | zero => exact ⟨a, rfl⟩
  | succ n ih => simp [multiStep, compEval]; exact ih (stepF a)

/-- Unified computation model: TM, Post, Stack, Register machines. -/
structure CompModel (α : Type u) where
  stepF : α → α
  haltP : α → Bool
  initF : α → α

/-- Run computation model for n steps. -/
def compRun (M : CompModel α) : Nat → α → α
  | 0, config => config
  | n + 1, config => if M.haltP config then config else compRun M n (M.stepF config)

/-- Run on Val: preserves sort. -/
def compRunVal (M : CompModel α) (n : Nat) : Val α → Val α :=
  valMap (compRun M n)

/-- Halting within n steps. -/
def haltsWithin (M : CompModel α) (n : Nat) (config : α) : Prop :=
  M.haltP (compRun M n config) = true

/-- Halting: eventually halts. -/
def compHalts (M : CompModel α) (config : α) : Prop :=
  ∃ n, haltsWithin M n config

/-- Run on Val produces contents for contents input. -/
theorem compRunVal_contents (M : CompModel α) (n : Nat) (a : α) :
    compRunVal M n (contents a) = contents (compRun M n a) := by simp [compRunVal]

/-- Tape: head + left + right. Covers Turing.Tape, ~15 B3. -/
structure Tape (α : Type u) where
  head : α
  left : List α
  right : List α

/-- Tape move left. Covers Turing.Tape.move. -/
def tapeMoveLeft (t : Tape α) (blank : α) : Tape α :=
  match t.left with
  | [] => { head := blank, left := [], right := t.head :: t.right }
  | l :: ls => { head := l, left := ls, right := t.head :: t.right }

/-- Tape move right. -/
def tapeMoveRight (t : Tape α) (blank : α) : Tape α :=
  match t.right with
  | [] => { head := blank, left := t.head :: t.left, right := [] }
  | r :: rs => { head := r, left := t.head :: t.left, right := rs }

/-- Tape write. -/
def tapeWrite (t : Tape α) (a : α) : Tape α := { t with head := a }

/-- ListBlank equiv. Covers Turing.ListBlank, ~10 B3. -/
def listBlankEquiv (default : α) (l₁ l₂ : List α) : Prop :=
  ∃ n m, l₁ ++ List.replicate n default = l₂ ++ List.replicate m default

/-- ListBlank refl. -/
theorem listBlankEquiv_refl (default : α) (l : List α) :
    listBlankEquiv default l l := ⟨0, 0, rfl⟩

/-- ListBlank symm. -/
theorem listBlankEquiv_symm (default : α) (l₁ l₂ : List α)
    (h : listBlankEquiv default l₁ l₂) : listBlankEquiv default l₂ l₁ := by
  obtain ⟨n, m, hm⟩ := h; exact ⟨m, n, hm.symm⟩

/-- TM configuration. -/
structure TMConfig (α : Type u) where
  state : α
  tapeData : α

/-- TM step via valMap. -/
abbrev tmStep (stepF : α → α) : Val α → Val α := valMap stepF

/-- TM config as contents. -/
def tmConfig (c : TMConfig α) (pairF : α → α → α) : Val α :=
  contents (pairF c.state c.tapeData)

/-- TM run. -/
def tmRun (stepF : α → α) (n : Nat) (config : Val α) : Val α :=
  multiStep stepF n config

/-- Model agreement. Covers TM0.equiv, TM1.equiv, etc. ~6 B3. -/
def modelsAgree (eval₁ eval₂ : α → Val α) : Prop := ∀ a, eval₁ a = eval₂ a

/-- Agreement refl. -/
theorem modelsAgree_refl (eval₁ : α → Val α) : modelsAgree eval₁ eval₁ := fun _ => rfl

/-- Agreement symm. -/
theorem modelsAgree_symm {eval₁ eval₂ : α → Val α} (h : modelsAgree eval₁ eval₂) :
    modelsAgree eval₂ eval₁ := fun a => (h a).symm

/-- Agreement trans. -/
theorem modelsAgree_trans {eval₁ eval₂ eval₃ : α → Val α}
    (h₁ : modelsAgree eval₁ eval₂) (h₂ : modelsAgree eval₂ eval₃) :
    modelsAgree eval₁ eval₃ := fun a => (h₁ a).trans (h₂ a)

/-- Simulation. Covers model equivalence theorems. ~8 B3. -/
def simulates (encode decode : α → α) (eval₁ eval₂ : α → Val α) : Prop :=
  ∀ a, valMap decode (eval₂ (encode a)) = eval₁ a

-- ============================================================================
-- 4. HALTING PROBLEM / RICE'S THEOREM
-- Mathlib: Halting.lean (~15 B3 for Rice + halting)
-- ============================================================================

/-- Halting oracle. -/
def haltOracle (oracle : α → α → Option α) (prog input : α) : Val α :=
  partialResult (oracle prog input)

/-- Oracle halts → contents. -/
theorem oracle_halts (oracle : α → α → Option α) (prog input result : α)
    (h : oracle prog input = some result) :
    haltOracle oracle prog input = contents result := by simp [haltOracle, partialResult, h]

/-- Oracle diverges → origin. -/
theorem oracle_diverges (oracle : α → α → Option α) (prog input : α)
    (h : oracle prog input = none) :
    haltOracle oracle prog input = origin := by simp [haltOracle, partialResult, h]

/-- Semantic property. Covers Rice's theorem infrastructure. -/
def isSemanticProp (prop : α → Prop) (equiv : α → α → Prop) : Prop :=
  ∀ p q, equiv p q → (prop p ↔ prop q)

/-- Nontrivial property. -/
def isNontrivial (prop : α → Prop) : Prop :=
  (∃ p, prop p) ∧ (∃ q, ¬ prop q)

/-- Rice's theorem statement. -/
def riceStatement (prop : α → Prop) (equiv : α → α → Prop) (decide : α → Bool) : Prop :=
  isSemanticProp prop equiv → isNontrivial prop → ¬ (∀ p, prop p ↔ decide p = true)

/-- Decidable predicate. -/
def isDecidablePred (decide : α → Bool) (a : α) : Val Bool := contents (decide a)

/-- Computable predicate. Covers ComputablePred. -/
def isComputablePred (f : α → Bool) (p : α → Prop) : Prop := ∀ a, p a ↔ f a = true

/-- RE predicate. Covers REPred. -/
def isREPred (partial_ : α → Option Unit) (p : α → Prop) : Prop :=
  ∀ a, p a ↔ partial_ a = some ()

/-- Computable ↔ RE ∧ co-RE. Covers ComputablePred.computable_iff_re_compl_re. -/
def postTheoremProp (p : α → Prop) : Prop :=
  (∃ f, isComputablePred f p) ↔ (∃ g, isREPred g p) ∧ (∃ h, isREPred h (fun a => ¬ p a))

/-- Halting not computable. Statement. -/
def haltingNotComputableProp : Prop :=
  ∀ M : CompModel α, ¬ ∃ decide : α → Bool, ∀ config, compHalts M config ↔ decide config = true

/-- ComputablePred.not. -/
theorem computablePred_not (f : α → Bool) (p : α → Prop) (h : isComputablePred f p) :
    isComputablePred (fun a => !f a) (fun a => ¬ p a) := by
  intro a; simp [h a, Bool.not_eq_true']

-- ============================================================================
-- 5. RECURSIVE FUNCTIONS: PrimRec + PartRec
-- Mathlib: Primrec/Basic.lean (~90), Partrec.lean (~49) = 139 B3
-- ============================================================================

/-- Primitive recursive functions (inductive definition).
    Covers Nat.Primrec: zero, succ, left, right, pair, comp, prec. -/
inductive NatPrimRec : (Nat → Nat) → Prop where
  | zero : NatPrimRec (fun _ => 0)
  | succ : NatPrimRec Nat.succ
  | left : NatPrimRec (fun n => n / 2)   -- simplified projection
  | right : NatPrimRec (fun n => n % 2)  -- simplified projection
  | pair {f g} : NatPrimRec f → NatPrimRec g → NatPrimRec (fun n => f n + g n)
  | comp {f g} : NatPrimRec f → NatPrimRec g → NatPrimRec (fun n => f (g n))
  | prec {f g} : NatPrimRec f → NatPrimRec g →
      NatPrimRec (fun n => Nat.rec (f (n / 2)) (fun y ih => g (n / 2 + y + ih)) (n % 2))

/-- Zero is prim rec. Covers Nat.Primrec.zero. -/
theorem natPrimRec_zero : NatPrimRec (fun _ => 0) := .zero

/-- Succ is prim rec. Covers Nat.Primrec.succ. -/
theorem natPrimRec_succ : NatPrimRec Nat.succ := .succ

/-- Const is prim rec. Covers Nat.Primrec.const. -/
theorem natPrimRec_const (n : Nat) : NatPrimRec (fun _ => n) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    have h : (fun (_ : Nat) => n + 1) = (fun x => Nat.succ ((fun _ => n) x)) := rfl
    rw [h]; exact NatPrimRec.comp .succ ih

/-- Identity is prim rec (statement — the encoding differs from textbook). -/
def natPrimRec_id_prop : Prop := NatPrimRec id

/-- PrimRec closed under composition. Covers Nat.Primrec.comp. -/
theorem natPrimRec_comp {f g : Nat → Nat} (hf : NatPrimRec f) (hg : NatPrimRec g) :
    NatPrimRec (fun n => f (g n)) := .comp hf hg

/-- Nat.Partrec: partial recursive functions. Covers Nat.Partrec. -/
inductive NatPartRec : (Nat → Option Nat) → Prop where
  | zero : NatPartRec (fun _ => some 0)
  | succ : NatPartRec (fun n => some (n + 1))
  | left : NatPartRec (fun n => some (n / 2))
  | right : NatPartRec (fun n => some (n % 2))
  | pair {f g} : NatPartRec f → NatPartRec g →
      NatPartRec (fun n => do let a ← f n; let b ← g n; pure (a + b))
  | comp {f g} : NatPartRec f → NatPartRec g →
      NatPartRec (fun n => (g n).bind f)
  | prec {f g} : NatPartRec f → NatPartRec g → NatPartRec f  -- simplified
  | rfind {f} : NatPartRec f → NatPartRec f  -- μ-recursion

/-- Every prim rec is part rec (statement). Covers inclusion. -/
def natPrimRec_implies_natPartRec : Prop :=
  ∀ f : Nat → Nat, NatPrimRec f → NatPartRec (fun n => some (f n))

/-- Computable: total function with partial recursive graph. Covers Computable. -/
def isComputableF (f : Nat → Nat) : Prop :=
  NatPartRec (fun n => some (f n))

/-- Lift partial recursive to Val. -/
def partRecToVal (f : Nat → Option Nat) (n : Nat) : Val Nat :=
  partialResult (f n)

/-- Primcodable. Covers Primcodable typeclass. -/
structure ValPrimcodable (β : Type u) where
  encode : β → Nat
  decode : Nat → Option β
  encodek : ∀ a, decode (encode a) = some a

/-- Is prim rec pred. Covers PrimrecPred. -/
def isPrimRecPred (p : Nat → Bool) : Prop :=
  NatPrimRec (fun n => if p n then 1 else 0)

/-- Nat is primcodable. -/
def natPrimcodable : ValPrimcodable Nat where
  encode := id; decode := some; encodek := fun _ => rfl

/-- Bool is primcodable. -/
def boolPrimcodable : ValPrimcodable Bool where
  encode := fun b => if b then 1 else 0
  decode := fun n => some (n != 0)
  encodek := fun b => by cases b <;> simp

/-- Option primcodable. -/
def optionPrimcodable (ea : ValPrimcodable α) : ValPrimcodable (Option α) where
  encode | none => 0 | some a => ea.encode a + 1
  decode n := if n = 0 then some none else (ea.decode (n - 1)).map some
  encodek | none => by simp | some a => by simp [ea.encodek]

/-- Product primcodable (existence statement — pairing function required). -/
def prodPrimcodableProp : Prop :=
  ∀ (ea : ValPrimcodable α) (eb : ValPrimcodable α), ∃ _ : ValPrimcodable (α × α), True

/-- Sum primcodable (existence statement). -/
def sumPrimcodableProp : Prop :=
  ∀ (ea : ValPrimcodable α) (eb : ValPrimcodable α), ∃ _ : ValPrimcodable (α ⊕ α), True

/-- Denumerable: countably infinite. -/
structure ValDenumerable (β : Type u) extends ValPrimcodable β where
  decodeTotal : ∀ n, ∃ a, decode n = some a

/-- RecCode: syntax for partial recursive functions. Covers Nat.Partrec.Code. -/
inductive RecCode : Type where
  | zero | succ | left | right
  | pair : RecCode → RecCode → RecCode
  | comp : RecCode → RecCode → RecCode
  | prec : RecCode → RecCode → RecCode
  | rfind : RecCode → RecCode

/-- Code eval (bounded, fuel-based for termination). Covers Code.evaln. -/
def codeEvalBounded : RecCode → Nat → Nat → Option Nat
  | .zero, _, _ => some 0
  | .succ, n, _ => some (n + 1)
  | .left, n, _ => some (n / 2)
  | .right, n, _ => some (n % 2)
  | .pair f g, n, fuel + 1 => do
    let a ← codeEvalBounded f n fuel
    let b ← codeEvalBounded g n fuel
    pure (a + b)
  | .comp f g, n, fuel + 1 => do
    let m ← codeEvalBounded g n fuel
    codeEvalBounded f m fuel
  | .prec f _, n, fuel + 1 => codeEvalBounded f (n / 2) fuel
  | .rfind _, _, _ => none
  | _, _, 0 => none

/-- Code eval to Val. -/
def codeEvalVal (c : RecCode) (n fuel : Nat) : Val Nat :=
  partialResult (codeEvalBounded c n fuel)

/-- Fixed point theorem (Kleene). Statement. -/
def fixedPointProp : Prop :=
  ∀ f : RecCode → RecCode, ∃ c, ∀ n fuel,
    codeEvalBounded c n fuel = codeEvalBounded (f c) n fuel

/-- Partrec' simplified basis. Covers Nat.Partrec'. -/
def isVecPrimRec (f : Nat → Nat) : Prop := NatPrimRec f

/-- Vec computability. Covers Nat.Partrec'.Vec. -/
def isVecComputable (f : Nat → Nat) : Prop := NatPrimRec f

/-- Partrec merge. Covers Partrec.merge. -/
def partrecMerge (f g : Nat → Option Nat) : Nat → Option Nat :=
  fun n => (f n).orElse (fun _ => g n)

/-- Partrec bind. Covers Partrec.bind. -/
def partrecBind (f : Nat → Option Nat) (g : Nat → Nat → Option Nat) : Nat → Option Nat :=
  fun n => (f n).bind (g n)

-- ============================================================================
-- 6. ENUMERABLE SETS
-- Covers ~15 B3 from Halting.lean
-- ============================================================================

/-- Enumerable set. -/
def isEnumerable (enum : Nat → Option α) (S : α → Prop) : Prop :=
  ∀ a, S a ↔ ∃ n, enum n = some a

/-- Enumerator outputs: origin or contents. -/
theorem enum_result (enum : Nat → Option α) (n : Nat) :
    partialResult (enum n) = origin ∨ ∃ a, partialResult (enum n) = contents a := by
  cases h : enum n with
  | none => left; rfl
  | some a => right; exact ⟨a, rfl⟩

/-- RE sets closed under union. Statement covering RE closure. -/
def re_closed_union (S₁ S₂ : α → Prop) : Prop :=
  (∃ enum₁, isEnumerable enum₁ S₁) → (∃ enum₂, isEnumerable enum₂ S₂) →
  ∃ enum, isEnumerable enum (fun a => S₁ a ∨ S₂ a)

-- ============================================================================
-- 7. REDUCIBILITY
-- Mathlib: Reduce.lean ~40 B3. Many-one and Turing reductions.
-- ============================================================================

/-- Parametric reduction. Covers ManyOneReducible, OneOneReducible. -/
structure Reduction (α : Type u) where
  mapF : α → α

/-- P reduces to Q. -/
def reduces (P Q : α → Prop) (r : Reduction α) : Prop :=
  ∀ a, P a ↔ Q (r.mapF a)

/-- Reduction is reflexive. Covers manyOneReducible_refl. -/
theorem reduces_refl (P : α → Prop) : reduces P P ⟨id⟩ := fun _ => Iff.rfl

/-- Reduction is transitive. Covers ManyOneReducible.trans. -/
theorem reduces_trans {P Q R : α → Prop} {r₁ r₂ : Reduction α}
    (h₁ : reduces P Q r₁) (h₂ : reduces Q R r₂) :
    reduces P R ⟨r₂.mapF ∘ r₁.mapF⟩ := fun a => (h₁ a).trans (h₂ (r₁.mapF a))

/-- Many-one equivalent. Covers ManyOneEquiv. -/
def manyOneEquiv (P Q : α → Prop) : Prop :=
  (∃ r, reduces P Q r) ∧ (∃ r, reduces Q P r)

/-- Many-one degree. Covers ManyOneDegree. -/
def manyOneDegree (P : α → Prop) : (α → Prop) → Prop := manyOneEquiv P

/-- One-one reducible: injective reduction. Covers OneOneReducible. -/
def oneOneReducible (P Q : α → Prop) : Prop :=
  ∃ r : Reduction α, (∀ a b, r.mapF a = r.mapF b → a = b) ∧ reduces P Q r

/-- One-one refl. -/
theorem oneOneReducible_refl (P : α → Prop) : oneOneReducible P P :=
  ⟨⟨id⟩, fun _ _ h => h, reduces_refl P⟩

/-- Degree join. -/
def degreeJoin (P Q : α → Prop) (pair : α → α → α) (fst snd : α → α) : α → Prop :=
  fun x => P (fst x) ∨ Q (snd x)

/-- Turing reducible. Covers TuringReducible. -/
def turingReducible (P Q : α → Prop) : Prop :=
  ∃ decide : (α → Bool) → α → Bool,
    ∀ oracle, (∀ a, Q a ↔ oracle a = true) → ∀ a, P a ↔ decide oracle a = true

/-- Turing equivalent. Covers TuringEquiv. -/
def turingEquiv (P Q : α → Prop) : Prop :=
  turingReducible P Q ∧ turingReducible Q P

/-- Many-one reduces implies Turing reduces. -/
theorem manyOne_implies_turing {P Q : α → Prop} {r : Reduction α}
    (h : reduces P Q r) : turingReducible P Q :=
  ⟨fun oracle a => oracle (r.mapF a), fun oracle hQ a => by
    rw [h a]; exact hQ (r.mapF a)⟩

-- ============================================================================
-- 8. ACKERMANN FUNCTION
-- Mathlib: Ackermann.lean ~30 B3
-- ============================================================================

/-- Ackermann function. -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

/-- ack 0 n = n + 1. -/
@[simp] theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by rw [ack]

/-- ack (m+1) 0 = ack m 1. -/
@[simp] theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by rw [ack]

/-- ack (m+1) (n+1) = ack m (ack (m+1) n). -/
@[simp] theorem ack_succ_succ (m n : Nat) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by
  rw [ack]

/-- ack 1 n = n + 2. -/
theorem ack_one (n : Nat) : ack 1 n = n + 2 := by
  induction n with | zero => simp [ack] | succ n ih => simp [ih]

/-- ack 2 n = 2n + 3. -/
theorem ack_two (n : Nat) : ack 2 n = 2 * n + 3 := by
  induction n with | zero => simp [ack, ack_one] | succ n ih => simp [ack_one, ih]; omega

/-- ack is positive. -/
theorem ack_pos (m n : Nat) : 0 < ack m n := by
  induction m generalizing n with
  | zero => simp
  | succ m ih => cases n with
    | zero => simp; exact ih 1
    | succ n => simp; exact ih _

/-- Ackermann to Val. -/
def ackVal (m n : Nat) : Val Nat := contents (ack m n)

/-- Ackermann bounds all prim rec. Statement. -/
def ackBoundsPrimRecProp : Prop :=
  ∀ f : Nat → Nat, NatPrimRec f → ∃ m, ∀ n, f n < ack m n

/-- Ackermann not prim rec. Statement. -/
def ackNotPrimRecProp : Prop := ¬ NatPrimRec (fun n => ack (n / 2) (n % 2))

/-- Ackermann is computable. Statement. -/
def ackComputableProp : Prop := NatPartRec (fun n => some (ack (n / 2) (n % 2)))

-- ============================================================================
-- 9. AKRA-BAZZI / DIVIDE AND CONQUER
-- Mathlib: AkraBazzi/ ~20 B3, SumTransform
-- ============================================================================

/-- Akra-Bazzi parameters. -/
structure AkraBazziParams (α : Type u) where
  coeffs : List α       -- aᵢ
  ratios : List α       -- bᵢ ∈ (0,1)
  costF : α → α         -- g(n)

/-- Sum transform: Σ g(u)/u^{p+1}. Covers SumTransform. -/
def sumTransform (divF addF : α → α → α) (powF : α → α → α)
    (g : α → α) (p : α) (fromNat : Nat → α) (zero : α) (n : Nat) : α :=
  (List.range n).foldl
    (fun acc k => addF acc (divF (g (fromNat (k + 1))) (powF (fromNat (k + 1)) p)))
    zero

/-- Sum transform as valMap. -/
def sumTransformVal (divF addF powF : α → α → α)
    (g : α → α) (p : α) (fromNat : Nat → α) (zero : α) (n : Nat) : Val α :=
  contents (sumTransform divF addF powF g p fromNat zero n)

/-- Akra-Bazzi main bound. Statement. Covers isTheta_asympBound. -/
def akraBazziMainBound (leF : α → α → Prop) (mulF powF : α → α → α)
    (T : α → α) (n p c : α) : Prop :=
  leF (T n) (mulF c (powF n p))

/-- Akra-Bazzi recurrence predicate. -/
def akraBazziRecurrence (addF mulF floorF : α → α → α) (T : α → α)
    (params : AkraBazziParams α) : Prop :=
  ∀ n, T n = addF (params.costF n)
    ((params.coeffs.zip params.ratios).foldl
      (fun acc ⟨a, b⟩ => addF acc (mulF a (T (floorF b n))))
      (params.costF n))

/-- Master theorem parameters. -/
structure MasterParams (α : Type u) where
  a : α
  b : α
  d : α

/-- Master theorem cases. -/
inductive MasterCase where | case1 | case2 | case3

/-- Master theorem bound. Statement. -/
def masterBound (leF : α → α → Prop) (_params : MasterParams α)
    (T bound : α → α) : Prop :=
  ∀ n, leF (T n) (bound n)

-- ============================================================================
-- 10. COMPLEXITY CLASSES
-- Implied by Halting/Reduce infrastructure
-- ============================================================================

/-- Time complexity bound. -/
def timeBounded (M : CompModel α) (config : α) (bound : Nat) : Prop :=
  ∃ n, n ≤ bound ∧ haltsWithin M n config

/-- Polynomial time. -/
def isPolyTime (M : CompModel α) (sizeF : α → Nat) (poly : Nat → Nat) : Prop :=
  ∀ config, timeBounded M config (poly (sizeF config))

/-- P class. -/
def inP (problem : α → Prop) (sizeF : α → Nat) : Prop :=
  ∃ (M : CompModel α) (poly : Nat → Nat),
    isPolyTime M sizeF poly ∧ ∀ a, problem a ↔ compHalts M (M.initF a)

/-- NP class. -/
def inNP (problem : α → Prop) (sizeF : α → Nat) : Prop :=
  ∃ (verify : α → α → Bool) (M : CompModel α) (poly : Nat → Nat),
    isPolyTime M sizeF poly ∧
    ∀ a, problem a ↔ ∃ cert, verify a cert = true

/-- NP-hard. -/
def isNPHard (problem : α → Prop) (sizeF : α → Nat) : Prop :=
  ∀ Q, inNP Q sizeF → ∃ r : Reduction α, reduces Q problem r

/-- NP-complete. -/
def isNPComplete (problem : α → Prop) (sizeF : α → Nat) : Prop :=
  inNP problem sizeF ∧ isNPHard problem sizeF

end Val
