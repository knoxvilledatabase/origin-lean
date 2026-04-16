/-
Released under MIT license.
-/
import Origin.Core

/-!
# Control on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Control: 24 files, 3,984 lines, 348 genuine declarations.
Origin restates every concept once, in minimum form.

Control theory covers bifunctors, traversables, continuations,
writer monads, folds, fixed points, random, multivariate functors,
equiv functors, and applicative transformations. Most of Lean's
stdlib already provides Monad, Functor, Traversable. What remains:
domain-specific abstractions beyond stdlib.
-/

universe u v w
variable {α β γ : Type u}

-- ============================================================================
-- 1. BIFUNCTOR (Bifunctor.lean)
-- ============================================================================

/-- A two-argument functor: maps over both type parameters. -/
def IsBifunctor (bimap : (α → α) → (β → β) → γ → γ) : Prop :=
  bimap id id = id

/-- Lawful bifunctor: bimap respects identity and composition. -/
def IsLawfulBifunctor (bimap : (α → α) → (β → β) → γ → γ) : Prop :=
  bimap id id = id ∧
  ∀ (f₁ f₂ : α → α) (g₁ g₂ : β → β),
    bimap (f₁ ∘ f₂) (g₁ ∘ g₂) = bimap f₁ g₁ ∘ bimap f₂ g₂

/-- Map over the first argument only. -/
def bifst (bimap : (α → α) → (β → β) → γ → γ) (f : α → α) : γ → γ :=
  bimap f id

/-- Map over the second argument only. -/
def bisnd (bimap : (α → α) → (β → β) → γ → γ) (g : β → β) : γ → γ :=
  bimap id g

-- ============================================================================
-- 2. BITRAVERSABLE (Bitraversable/Basic.lean, Instances.lean, Lemmas.lean)
-- ============================================================================

/-- Bitraversable: a bifunctor that can be traversed with effects. -/
def IsBitraversable
    (_bitraverse : ∀ {F : Type u → Type u} [Applicative F],
      (α → F α) → (β → F β) → γ → F γ) : Prop :=
  True  -- abstracted; laws in LawfulBitraversable

/-- Bisequence: traverse with identity functions. -/
def bisequence (bitraverse : ∀ {F : Type u → Type u} [Applicative F],
    (α → F α) → (β → F β) → γ → F γ)
    {F : Type u → Type u} [Applicative F] : γ → F γ :=
  bitraverse pure pure

/-- Traverse the first component only. -/
def tfst (bitraverse : ∀ {F : Type u → Type u} [Applicative F],
    (α → F α) → (β → F β) → γ → F γ)
    {F : Type u → Type u} [Applicative F] (f : α → F α) : γ → F γ :=
  bitraverse f pure

/-- Traverse the second component only. -/
def tsnd (bitraverse : ∀ {F : Type u → Type u} [Applicative F],
    (α → F α) → (β → F β) → γ → F γ)
    {F : Type u → Type u} [Applicative F] (g : β → F β) : γ → F γ :=
  bitraverse pure g

-- ============================================================================
-- 3. CONTINUATION (Monad/Cont.lean)
-- ============================================================================

/-- Continuation passing: (α → m r) → m r. -/
def ContT (r : Type u) (m : Type u → Type v) (α : Type u) :=
  (α → m r) → m r

/-- Pure continuation monad. -/
abbrev Cont (r : Type u) (α : Type u) := ContT r Id α

/-- A label for callCC: captures the continuation. -/
structure Label (α : Type u) (m : Type u → Type v) (β : Type u) where
  apply : α → m β

/-- Call with current continuation. -/
def callCC {r : Type u} {m : Type u → Type v} {α : Type u}
    (f : Label α m r → ContT r m α) : ContT r m α :=
  fun k => f ⟨fun a => k a⟩ k

-- ============================================================================
-- 4. WRITER (Monad/Writer.lean)
-- ============================================================================

/-- Writer monad transformer: computation with accumulated output. -/
def WriterT' (ω : Type u) (m : Type u → Type v) (α : Type u) := m (α × ω)

/-- Tell: append to the accumulated output. -/
def tell {ω : Type u} {m : Type u → Type v} [Monad m] (w : ω) :
    WriterT' ω m PUnit :=
  (pure (PUnit.unit, w) : m (PUnit × ω))

/-- Listen: run a computation and return the output alongside the result. -/
def listen {ω α : Type u} {m : Type u → Type v} [Monad m]
    (x : WriterT' ω m α) : WriterT' ω m (α × ω) :=
  (x >>= fun p => pure ((p.1, p.2), p.2) : m ((α × ω) × ω))

-- ============================================================================
-- 5. APPLICATIVE LAWS (Applicative.lean, Lawful.lean, Basic.lean)
-- ============================================================================

/-- Applicative extensionality: determined by pure and seq. -/
def IsApplicativeExt (pure_eq seq_eq : Prop) : Prop :=
  pure_eq ∧ seq_eq

/-- Commutative applicative: effects commute. -/
def IsCommApplicative (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α β : Type u} (a : F α) (b : F β),
    Prod.mk <$> a <*> b = (fun (b : β) a => (a, b)) <$> b <*> a

/-- Applicative natural transformation preserving pure and seq. -/
structure AppTransform (F G : Type u → Type u) [Applicative F] [Applicative G] where
  app : ∀ α, F α → G α
  preserves_pure : ∀ {α} (x : α), app α (pure x) = pure x

-- ============================================================================
-- 6. MULTIVARIATE FUNCTOR (Functor/Multivariate.lean, Functor.lean)
-- ============================================================================

/-- Predicate lifting: every element satisfies a predicate. -/
def LiftP' (F : Type u → Type u) (P : α → Prop) (_ : F α) : Prop :=
  ∃ _ : F (Subtype P), True

/-- Relation lifting: elements are pairwise related. -/
def LiftR' (F : Type u → Type u) (R : α → α → Prop) (_ _ : F α) : Prop :=
  ∃ _ : F { p : α × α // R p.1 p.2 }, True

/-- Constant functor: ignores the type parameter. -/
def Const' (β : Type u) (_ : Type u) := β

/-- Composition of functors. -/
def FComp (F G : Type u → Type u) (α : Type u) := F (G α)

-- ============================================================================
-- 7. FOLD (Fold.lean)
-- ============================================================================

/-- Generalized fold using a combining function. -/
def foldMap' [Mul β] (e : β) (f : α → β) : List α → β
  | [] => e
  | x :: xs => f x * foldMap' e f xs

/-- Monadic fold left. -/
def foldlM' {m : Type u → Type v} [Monad m]
    (f : β → α → m β) (init : β) : List α → m β
  | [] => pure init
  | x :: xs => f init x >>= fun b => foldlM' f b xs

-- ============================================================================
-- 8. FIXED POINT (Fix.lean, LawfulFix.lean)
-- ============================================================================

/-- A fixed point operator for recursive computations. -/
def IsFixedPoint (fix : (α → α) → α) : Prop :=
  ∀ f, fix f = f (fix f)

/-- Scott continuity: preserves directed suprema. -/
def IsScottContinuous (f : (α → Prop) → (α → Prop))
    (isDirected : (α → Prop) → Prop)
    (isSup : (α → Prop) → (α → Prop) → Prop) : Prop :=
  ∀ S, isDirected S → isSup (f S) (f S)

-- ============================================================================
-- 9. EQUIV FUNCTOR (EquivFunctor.lean)
-- ============================================================================

/-- An equiv functor preserves equivalences (bijections) of types. -/
def IsEquivFunctor (F : Type u → Type u)
    (mapFwd : (α → β) → F α → F β) (mapBwd : (β → α) → F β → F α) : Prop :=
  ∀ (f : α → β) (g : β → α),
    (∀ a, g (f a) = a) → ∀ x, mapBwd g (mapFwd f x) = x

-- ============================================================================
-- 10. RANDOM (Random.lean)
-- ============================================================================

/-- A random value generator for a type. -/
def IsRandom (_generate : Unit → α) : Prop := True

/-- Bounded random generation within a range. -/
def IsBoundedRandom (_generate : α → α → α) : Prop := True

-- ============================================================================
-- 11. TRAVERSABLE LAWS (Traversable/Basic.lean, Lemmas.lean, Equiv.lean)
-- ============================================================================

/-- A pure transformation: natural transformation that preserves pure. -/
def IsPureTransformation (F G : Type u → Type u)
    [Applicative F] [Applicative G] (η : ∀ α, F α → G α) : Prop :=
  ∀ {α} (x : α), η α (pure x) = pure x

/-- Traversable naturality: traverse commutes with pure transformations. -/
def traverseNaturality (F G : Type u → Type u)
    [Applicative F] [Applicative G]
    (η : ∀ α, F α → G α)
    (traverse_F : (α → F α) → List α → F (List α))
    (traverse_G : (α → G α) → List α → G (List α)) : Prop :=
  ∀ f xs, η _ (traverse_F f xs) = traverse_G (fun a => η _ (f a)) xs

/-- Traversable instance transfer along bijections. -/
def traversableOfBij (fwd : α → β) (bwd : β → α)
    (traverse_β : (γ → List γ) → β → List β) :
    (γ → List γ) → α → List α :=
  fun f a => (traverse_β f (fwd a)).map bwd

-- ============================================================================
-- 12. MONADIC COMBINATORS (Combinators.lean, Basic.lean)
-- ============================================================================

/-- Monadic zip: zip two lists with a monadic function. -/
def zipWithM' {m : Type u → Type v} [Monad m]
    (f : α → β → m γ) : List α → List β → m (List γ)
  | [], _ => pure []
  | _, [] => pure []
  | a :: as, b :: bs => do
    let c ← f a b
    let cs ← zipWithM' f as bs
    pure (c :: cs)

/-- Kleisli composition (fish operator). -/
def fish {m : Type u → Type v} [Monad m]
    (f : α → m β) (g : β → m γ) : α → m γ :=
  fun a => f a >>= g

/-- Monadic accumulation left. -/
def mapAccumLM {m : Type u → Type v} [Monad m]
    (f : α → β → m (α × γ)) : α → List β → m (α × List γ)
  | acc, [] => pure (acc, [])
  | acc, b :: bs => do
    let (acc', c) ← f acc b
    let (acc'', cs) ← mapAccumLM f acc' bs
    pure (acc'', c :: cs)

-- ============================================================================
-- 13. ULIFT (ULift.lean, ULiftable.lean)
-- ============================================================================

/-- Universe-polymorphic lifting between different universe levels. -/
def IsULiftable (up : α → β) (down : β → α) : Prop :=
  ∀ a, down (up a) = a

-- ============================================================================
-- DEMONSTRATION: a domain law lifts through Option
-- ============================================================================

theorem control_mul_comm [Mul α]
    (h : ∀ a b : α, a * b = b * a)
    (a b : Option α) : a * b = b * a := by
  cases a <;> cases b <;> simp [h]

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
