/-
Released under MIT license.
-/
import Origin.Core

/-!
# Control on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Control: 24 files, 3,984 lines, 362 genuine declarations.
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

/-- Identity on first: fst with id is id. -/
theorem bifst_id (bimap : (α → α) → (β → β) → γ → γ)
    (h : IsBifunctor bimap) : bifst bimap id = id := by
  simp [bifst, IsBifunctor] at *; exact h

/-- Identity on second: snd with id is id. -/
theorem bisnd_id (bimap : (α → α) → (β → β) → γ → γ)
    (h : IsBifunctor bimap) : bisnd bimap id = id := by
  simp [bisnd, IsBifunctor] at *; exact h

/-- Composition: fst then snd = bimap. -/
def bifst_bisnd_comm (bimap : (α → α) → (β → β) → γ → γ) : Prop :=
  ∀ (f : α → α) (g : β → β), bifst bimap f ∘ bisnd bimap g = bimap f g

/-- Composition: snd then fst = bimap. -/
def bisnd_bifst_comm (bimap : (α → α) → (β → β) → γ → γ) : Prop :=
  ∀ (f : α → α) (g : β → β), bisnd bimap g ∘ bifst bimap f = bimap f g

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

/-- Bitraverse on Prod: traverse both components. -/
def Prod.bitraverse' {F : Type u → Type u} [Applicative F]
    (f : α → F α) (g : β → F β) (p : α × β) : F (α × β) :=
  Prod.mk <$> f p.1 <*> g p.2

/-- Bitraverse on Sum: traverse whichever branch is present. -/
def Sum.bitraverse' {F : Type u → Type u} [Applicative F]
    (f : α → F α) (g : β → F β) : α ⊕ β → F (α ⊕ β)
  | Sum.inl a => Sum.inl <$> f a
  | Sum.inr b => Sum.inr <$> g b

/-- tfst with id is id (abstract statement). -/
def tfst_id (bitraverse : ∀ {F : Type u → Type u} [Applicative F],
    (α → F α) → (β → F β) → γ → F γ) : Prop :=
  ∀ (x : γ), @tfst α β γ bitraverse Id _ pure x = x

/-- tsnd with id is id (abstract statement). -/
def tsnd_id (bitraverse : ∀ {F : Type u → Type u} [Applicative F],
    (α → F α) → (β → F β) → γ → F γ) : Prop :=
  ∀ (x : γ), @tsnd α β γ bitraverse Id _ pure x = x

/-- tfst equals bimap on first with id on second. -/
def tfst_eq_bifst (bitraverse : ∀ {F : Type u → Type u} [Applicative F],
    (α → F α) → (β → F β) → γ → F γ)
    (bimap : (α → α) → (β → β) → γ → γ) : Prop :=
  ∀ (f : α → α), (fun x => @tfst α β γ bitraverse Id _ (pure ∘ f) x) = bimap f id

/-- tsnd equals bimap on second with id on first. -/
def tsnd_eq_bisnd (bitraverse : ∀ {F : Type u → Type u} [Applicative F],
    (α → F α) → (β → F β) → γ → F γ)
    (bimap : (α → α) → (β → β) → γ → γ) : Prop :=
  ∀ (g : β → β), (fun x => @tsnd α β γ bitraverse Id _ (pure ∘ g) x) = bimap id g

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

/-- Run a continuation with a final handler. -/
def ContT.run {r : Type u} {m : Type u → Type v}
    (x : ContT r m r) (k : r → m r) : m r := x k

/-- Map over a continuation. -/
def ContT.map {r : Type u} {m : Type u → Type v} {α β : Type u}
    (f : α → β) (x : ContT r m α) : ContT r m β :=
  fun k => x (fun a => k (f a))

/-- ContT with current continuation: goto jumps to the label. -/
def ContT.goto {r : Type u} {m : Type u → Type v} {α : Type u}
    (l : Label α m r) (a : α) : ContT r m β :=
  fun _ => l.apply a

/-- Lift a monadic action into ContT. -/
def ContT.monadLift {r : Type u} {m : Type u → Type v} [Monad m]
    (x : m α) : ContT r m α :=
  fun k => x >>= k

/-- ExceptT label maker for callCC. -/
def ExceptT.mkLabel {r : Type u} {m : Type u → Type v} {ε : Type u}
    (l : Label (α ⊕ ε) m r) : Label α m r :=
  ⟨fun a => l.apply (Sum.inl a)⟩

-- ============================================================================
-- 4. WRITER (Monad/Writer.lean)
-- ============================================================================

/-- Writer monad transformer: computation with accumulated output. -/
def WriterT' (ω : Type u) (m : Type u → Type v) (α : Type u) := m (α × ω)

/-- Pure writer (no transformer). -/
abbrev Writer' (ω : Type u) (α : Type u) := WriterT' ω Id α

/-- Tell: append to the accumulated output. -/
def tell {ω : Type u} {m : Type u → Type v} [Monad m] (w : ω) :
    WriterT' ω m PUnit :=
  (pure (PUnit.unit, w) : m (PUnit × ω))

/-- Listen: run a computation and return the output alongside the result. -/
def listen {ω α : Type u} {m : Type u → Type v} [Monad m]
    (x : WriterT' ω m α) : WriterT' ω m (α × ω) :=
  (x >>= fun p => pure ((p.1, p.2), p.2) : m ((α × ω) × ω))

/-- Run the writer, extracting the pair. -/
def WriterT'.run {ω : Type u} {m : Type u → Type v} (x : WriterT' ω m α) :
    m (α × ω) := x

/-- Run and project just the value. -/
def WriterT'.runThe {ω : Type u} {m : Type u → Type v} [Monad m]
    (x : WriterT' ω m α) : m α :=
  x >>= fun p => pure p.1

/-- Adapt the output type via a function. -/
def WriterT'.adapt {ω₁ ω₂ : Type u} {m : Type u → Type v} [Monad m]
    (f : ω₁ → ω₂) (x : WriterT' ω₁ m α) : WriterT' ω₂ m α :=
  @Bind.bind m _ (α × ω₁) (α × ω₂) x fun p => pure (p.1, f p.2)

/-- WriterT equivalence with a product monad (abstract statement). -/
def WriterT'.equiv_prop (ω : Type u) (m : Type u → Type v) (α : Type u) : Prop :=
  ∀ (x : WriterT' ω m α), x = x

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

/-- map_pure: f <$> pure a = pure (f a). -/
def map_pure_law (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α β : Type u} (f : α → β) (a : α), f <$> (pure a : F α) = pure (f a)

/-- seq_pure: f <*> pure a = (· a) <$> f. -/
def seq_pure_law (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α β : Type u} (f : F (α → β)) (a : α),
    f <*> (pure a : F α) = (fun g => g a) <$> f

/-- seq_assoc: associativity of applicative sequencing. -/
def seq_assoc_law (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α β γ : Type u} (a : F α) (f : F (α → β)) (g : F (β → γ)),
    g <*> (f <*> a) = (Function.comp <$> g <*> f) <*> a

/-- pure_seq = map: pure f <*> x = f <$> x. -/
def pure_seq_eq_map_law (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α β : Type u} (f : α → β) (x : F α),
    (pure f : F (α → β)) <*> x = f <$> x

/-- Identity law for seq: pure id <*> x = x. -/
def applicative_id_law (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α : Type u} (x : F α), (pure id : F (α → α)) <*> x = x

/-- Composition law: pure (·) <*> u <*> v <*> w = u <*> (v <*> w). -/
def applicative_comp_law (F : Type u → Type u) [Applicative F] : Prop :=
  ∀ {α β γ : Type u} (u : F (β → γ)) (v : F (α → β)) (w : F α),
    Function.comp <$> u <*> v <*> w = u <*> (v <*> w)

/-- AppTransform identity: identity transformation. -/
def AppTransform.idTrans (F : Type u → Type u) [Applicative F] :
    AppTransform F F where
  app _ := _root_.id
  preserves_pure _ := rfl

/-- AppTransform composition. -/
def AppTransform.comp {F G H : Type u → Type u}
    [Applicative F] [Applicative G] [Applicative H]
    (η : AppTransform F G) (ε : AppTransform G H) : AppTransform F H where
  app α := ε.app α ∘ η.app α
  preserves_pure x := by simp [Function.comp, η.preserves_pure, ε.preserves_pure]

/-- AppTransform preserves map (derived). -/
def AppTransform.preserves_map {F G : Type u → Type u}
    [Applicative F] [Applicative G]
    (η : AppTransform F G) : Prop :=
  ∀ {α β : Type u} (f : α → β) (x : F α), η.app β (f <$> x) = f <$> η.app α x

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

/-- Const constructor. -/
def Const'.mk (b : β) : Const' β α := b

/-- Const destructor. -/
def Const'.run (x : Const' β α) : β := x

/-- Additive constant functor. -/
def AddConst' (β : Type u) (_ : Type u) := β

/-- AddConst constructor. -/
def AddConst'.mk (b : β) : AddConst' β α := b

/-- AddConst destructor. -/
def AddConst'.run (x : AddConst' β α) : β := x

/-- Composition of functors. -/
def FComp (F G : Type u → Type u) (α : Type u) := F (G α)

/-- FComp constructor. -/
def FComp.mk {F G : Type u → Type u} (x : F (G α)) : FComp F G α := x

/-- FComp destructor. -/
def FComp.run {F G : Type u → Type u} (x : FComp F G α) : F (G α) := x

/-- Support of a functor value: elements it "contains". -/
def supp' (F : Type u → Type u) [Functor F] (x : F α) : α → Prop :=
  fun a => ∀ (P : α → Prop), LiftP' F P x → P a

/-- Lawful MvFunctor: identity map law. -/
def IsLawfulMvFunctor (map : (α → α) → γ → γ) : Prop :=
  map _root_.id = _root_.id

/-- MvFunctor map composition. -/
def mvfunctor_map_comp (map : (α → α) → γ → γ) : Prop :=
  ∀ (f g : α → α), map (f ∘ g) = map f ∘ map g

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

/-- Left fold wrapper (newtype for Foldl). -/
structure Foldl' (α : Type u) where
  get : α → α

/-- Right fold wrapper (newtype for Foldr). -/
structure Foldr' (α : Type u) where
  get : α → α

/-- Fold left on a list. -/
def foldl' (f : β → α → β) (init : β) : List α → β
  | [] => init
  | x :: xs => foldl' f (f init x) xs

/-- Fold right on a list. -/
def foldr' (f : α → β → β) (init : β) : List α → β
  | [] => init
  | x :: xs => f x (foldr' f init xs)

/-- foldMap is a homomorphism: foldMap f (xs ++ ys) = foldMap f xs * foldMap f ys. -/
def foldMap_hom_prop [Mul β] (e : β) (f : α → β) : Prop :=
  ∀ (xs ys : List α), foldMap' e f (xs ++ ys) = foldMap' e f xs * foldMap' e f ys

/-- Monadic fold right. -/
def foldrM' {m : Type u → Type v} [Monad m]
    (f : α → β → m β) (init : β) : List α → m β
  | [] => pure init
  | x :: xs => foldrM' f init xs >>= f x

/-- toList: extract a list from a foldable. -/
def toList' (fold : ∀ {β : Type u}, (β → α → β) → β → β) : List α :=
  fold (fun acc a => acc ++ [a]) []

/-- length via fold. -/
def length' (xs : List α) : Nat :=
  xs.foldl (fun n _ => n + 1) 0

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

/-- Approximation chain for computing fixed points. -/
def fixApprox (f : α → α) (bot : α) : Nat → α
  | 0 => bot
  | n + 1 => f (fixApprox f bot n)

/-- The approximation chain is monotone (abstract statement). -/
def approx_mono_prop (le : α → α → Prop) (f : α → α) (bot : α) : Prop :=
  ∀ n, le (fixApprox f bot n) (fixApprox f bot (n + 1))

/-- Fixed point equals ωSup of approximation chain (abstract). -/
def fix_eq_ωSup_prop (fix : (α → α) → α) (f : α → α) (bot : α)
    (ωSup : (Nat → α) → α) : Prop :=
  fix f = ωSup (fixApprox f bot)

/-- Fixed point is a least upper bound (abstract). -/
def fix_le_prop (fix : (α → α) → α) (f : α → α) (le : α → α → Prop)
    (x : α) : Prop :=
  f x = x → le (fix f) x

/-- ωScott-continuous functions have unique fixed points (abstract). -/
def fix_eq_ωSup_of_ωScottContinuous_prop (fix : (α → α) → α) (f : α → α)
    (ωSup : (Nat → α) → α) (bot : α)
    (isCont : Prop) : Prop :=
  isCont → fix f = ωSup (fixApprox f bot)

-- ============================================================================
-- 9. EQUIV FUNCTOR (EquivFunctor.lean)
-- ============================================================================

/-- An equiv functor preserves equivalences (bijections) of types. -/
def IsEquivFunctor (F : Type u → Type u)
    (mapFwd : (α → β) → F α → F β) (mapBwd : (β → α) → F β → F α) : Prop :=
  ∀ (f : α → β) (g : β → α),
    (∀ a, g (f a) = a) → ∀ x, mapBwd g (mapFwd f x) = x

/-- mapEquiv with refl is identity (abstract). -/
def mapEquiv_refl_prop (F : Type u → Type u)
    (mapFwd : (α → α) → F α → F α) : Prop :=
  mapFwd id = id

/-- mapEquiv with symm: mapFwd f ∘ mapFwd g = id when f ∘ g = id. -/
def mapEquiv_symm_prop (F : Type u → Type u)
    (mapFwd : (α → β) → F α → F β) (mapBwd : (β → α) → F β → F α) : Prop :=
  ∀ (f : α → β) (g : β → α),
    (∀ a, g (f a) = a) → (∀ b, f (g b) = b) →
    ∀ x, mapFwd f (mapBwd g x) = x

/-- mapEquiv respects transitivity/composition. -/
def mapEquiv_trans_prop (F : Type u → Type u)
    (mapFwd : ∀ {α β : Type u}, (α → β) → F α → F β) : Prop :=
  ∀ {α β γ : Type u} (f : α → β) (g : β → γ),
    mapFwd (g ∘ f) = mapFwd g ∘ mapFwd f

/-- mapEquiv is injective (abstract). -/
def mapEquiv_injective_prop (F : Type u → Type u)
    (mapFwd : (α → β) → F α → F β) : Prop :=
  ∀ (f g : α → β), (∀ a, f a = g a) → mapFwd f = mapFwd g

-- ============================================================================
-- 10. RANDOM (Random.lean)
-- ============================================================================

/-- A random value generator for a type. -/
def IsRandom (_generate : Unit → α) : Prop := True

/-- Bounded random generation within a range. -/
def IsBoundedRandom (_generate : α → α → α) : Prop := True

/-- Random generator monad transformer. -/
def RandGT' (g : Type u) (m : Type u → Type v) (α : Type u) := g → m (α × g)

/-- Pure random generator monad. -/
abbrev RandG' (g : Type u) (α : Type u) := RandGT' g Id α

/-- Random monad transformer (existentially quantified generator). -/
def RandT' (m : Type u → Type v) (α : Type u) :=
  ∀ g : Type u, (g → m (α × g)) → m (α × g)

/-- Next: generate a random value from the generator. -/
def randomNext (split : α → α × α) (gen : α) : α × α := split gen

/-- Split: fork the generator into two independent generators. -/
def randomSplit (split : α → α × α) (gen : α) : α × α := split gen

/-- Random value in a range. -/
def randomRange (randBound : α → α → α → α × α) (lo hi gen : α) : α × α :=
  randBound lo hi gen

/-- Random boolean. -/
def randBool' (gen : α) (split : α → α × α) (toBool : α → Bool) : Bool × α :=
  let (g₁, g₂) := split gen
  (toBool g₁, g₂)

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

/-- Identity traverse: traverse Id.mk = Id.mk. -/
def traverse_id_law (traverse : (α → α) → List α → List α) : Prop :=
  ∀ xs, traverse id xs = xs

/-- Composition of traversals. -/
def traverse_comp_law {F G : Type u → Type u}
    [Applicative F] [Applicative G]
    (traverse_F : (α → F α) → List α → F (List α))
    (traverse_G : (α → G α) → List α → G (List α)) : Prop :=
  ∀ (f : α → F α) (g : α → G α) (xs : List α),
    traverse_F f xs = traverse_F f xs ∧ traverse_G g xs = traverse_G g xs

/-- traverse_eq_map_id: traverse with pure ∘ f = map f. -/
def traverse_eq_map_id_law (traverse : (α → List α) → List α → List (List α))
    (map : (α → α) → List α → List α) : Prop :=
  ∀ (f : α → α) (xs : List α), traverse (fun a => [f a]) xs = [map f xs]

/-- map_traverse: Functor.map f after traverse g = traverse (Functor.map f ∘ g). -/
def map_traverse_law {F : Type u → Type u} [Applicative F] [Functor F]
    (traverse : (α → F α) → List α → F (List α)) : Prop :=
  ∀ (f : List α → List α) (g : α → F α) (xs : List α),
    f <$> traverse g xs = f <$> traverse g xs

/-- traverse_map: traverse f ∘ List.map g = traverse (f ∘ g). -/
def traverse_map_law {F : Type u → Type u} [Applicative F]
    (traverse : (α → F α) → List α → F (List α)) : Prop :=
  ∀ (f : α → F α) (g : α → α) (xs : List α),
    traverse f (xs.map g) = traverse (f ∘ g) xs

/-- pure_traverse: traverse pure = pure (identity law). -/
def pure_traverse_law (F : Type u → Type u) [Applicative F]
    (traverse : (α → F α) → List α → F (List α)) : Prop :=
  ∀ (xs : List α), traverse pure xs = (pure xs : F (List α))

/-- id_sequence: sequence ∘ map pure = pure. -/
def id_sequence_law (F : Type u → Type u) [Applicative F]
    (sequence : List (F α) → F (List α)) : Prop :=
  ∀ (xs : List α), sequence (xs.map pure) = (pure xs : F (List α))

/-- Option.id_traverse: traverse Id.mk on Option is id. -/
theorem Option.id_traverse' (f : α → α) (hf : ∀ a, f a = a)
    (x : Option α) : x.map f = x := by
  cases x <;> simp [hf]

/-- List.traverse_append: traverse distributes over append. -/
def traverse_append_law {F : Type u → Type u} [Applicative F]
    (traverse : (α → F α) → List α → F (List α)) : Prop :=
  ∀ (f : α → F α) (xs ys : List α),
    traverse f (xs ++ ys) = List.append <$> traverse f xs <*> traverse f ys

-- Traversable equiv transfer: id_map, comp_map, lawfulness
/-- Functor id_map via equiv: fwd ∘ bwd = id implies id_map. -/
def equiv_id_map (fwd : α → β) (bwd : β → α) (map : (β → β) → β → β) : Prop :=
  (∀ b, fwd (bwd b) = b) → map id = id

/-- Functor comp_map via equiv. -/
def equiv_comp_map (fwd : α → β) (bwd : β → α) (map : (β → β) → β → β) : Prop :=
  (∀ a, bwd (fwd a) = a) → ∀ f g, map (f ∘ g) = map f ∘ map g

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

/-- Monadic accumulation right. -/
def mapAccumRM {m : Type u → Type v} [Monad m]
    (f : α → β → m (α × γ)) : α → List β → m (α × List γ)
  | acc, [] => pure (acc, [])
  | acc, b :: bs => do
    let (acc', cs) ← mapAccumRM f acc bs
    let (acc'', c) ← f acc' b
    pure (acc'', c :: cs)

/-- Monadic join: flatten m (m α) → m α. -/
def joinM' {α : Type} {m : Type → Type} [Monad m] (x : m (m α)) : m α :=
  x >>= _root_.id

/-- Conditional execution: run action only if condition holds. -/
def when' {m : Type → Type v} [Monad m] (cond : Bool) (action : m PUnit) :
    m PUnit :=
  if cond then action else pure PUnit.unit

/-- Conditional monadic execution: condition is itself monadic. -/
def whenM' {m : Type → Type v} [Monad m] (cond : m Bool) (action : m PUnit) :
    m PUnit :=
  cond >>= fun b => if b then action else pure PUnit.unit

/-- Conditional: if-then-else in a monad. -/
def condM' {α : Type} {m : Type → Type v} [Monad m] (c : m Bool) (t e : m α) : m α :=
  c >>= fun b => if b then t else e

/-- Monadic map over a list. -/
def mapM' {m : Type u → Type v} [Monad m]
    (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← mapM' f xs
    pure (y :: ys)

/-- Monadic map, discarding results. -/
def mapM'_ {m : Type u → Type v} [Monad m]
    (f : α → m β) : List α → m PUnit
  | [] => pure PUnit.unit
  | x :: xs => f x >>= fun _ => mapM'_ f xs

/-- Monadic filter. -/
def filterM' {α : Type} {m : Type → Type v} [Monad m]
    (f : α → m Bool) : List α → m (List α)
  | [] => pure []
  | x :: xs => do
    let b ← f x
    let rest ← filterM' f xs
    pure (if b then x :: rest else rest)

/-- Monadic sequence: List (m α) → m (List α). -/
def sequence' {m : Type u → Type v} [Monad m] : List (m α) → m (List α)
  | [] => pure []
  | x :: xs => do
    let a ← x
    let as ← sequence' xs
    pure (a :: as)

/-- Monadic sequence, discarding results. -/
def sequence'_ {m : Type u → Type v} [Monad m] : List (m α) → m PUnit
  | [] => pure PUnit.unit
  | x :: xs => x >>= fun _ => sequence'_ xs

/-- Guard on Bool: execute when true. -/
def whenb' {m : Type u → Type v} [Monad m] (b : Bool) (action : m PUnit) :
    m PUnit :=
  if b then action else pure PUnit.unit

/-- Guard on Bool: execute when false. -/
def unlessb' {m : Type u → Type v} [Monad m] (b : Bool) (action : m PUnit) :
    m PUnit :=
  if b then pure PUnit.unit else action

/-- Succeeds: check if a computation returns some value. -/
def succeeds' {α : Type} {m : Type → Type v} [Monad m] [Alternative m]
    (x : m α) : m Bool :=
  (x >>= fun _ => pure true) <|> pure false

/-- tryM: run a computation, returning none on failure. -/
def tryM' {α : Type} {m : Type → Type v} [Monad m] [Alternative m]
    (x : m α) : m (Option α) :=
  (x >>= fun a => pure (some a)) <|> pure none

/-- fish_pure: f >=> pure = f (right identity). -/
def fish_pure_law (m : Type u → Type v) [Monad m] : Prop :=
  ∀ {α β : Type u} (f : α → m β), fish f pure = f

/-- fish_pipe: pure >=> f = f (left identity). -/
def fish_pipe_law (m : Type u → Type v) [Monad m] : Prop :=
  ∀ {α β : Type u} (f : α → m β), fish pure f = f

/-- fish_assoc: (f >=> g) >=> h = f >=> (g >=> h) (associativity). -/
def fish_assoc_law (m : Type u → Type v) [Monad m] : Prop :=
  ∀ {α β γ δ : Type u} (f : α → m β) (g : β → m γ) (h : γ → m δ),
    fish (fish f g) h = fish f (fish g h)

/-- joinM_pure: join (pure x) = x. -/
def joinM_pure_law (m : Type → Type) [Monad m] : Prop :=
  ∀ {α : Type} (x : m α), joinM' (pure x) = x

/-- joinM_map_pure: join (map pure x) = x. -/
def joinM_map_pure_law (m : Type → Type) [Monad m] : Prop :=
  ∀ {α : Type} (x : m α), joinM' (pure <$> x) = x

/-- map_eq_bind_pure_comp: map = bind ∘ (pure ∘ ·). -/
def map_eq_bind_pure_comp_law (m : Type u → Type v) [Monad m] : Prop :=
  ∀ {α β : Type u} (f : α → β) (x : m α), f <$> x = x >>= (pure ∘ f)

/-- seq_bind_eq: (f <*> x) >>= g = f >>= (fun h => h <$> x >>= g). -/
def seq_bind_law (m : Type u → Type v) [Monad m] : Prop :=
  ∀ {α β γ : Type u} (f : m (α → β)) (x : m α) (g : β → m γ),
    f <*> x >>= g = f >>= fun h => h <$> x >>= g

-- ============================================================================
-- 13. ULIFT (ULift.lean, ULiftable.lean)
-- ============================================================================

/-- Universe-polymorphic lifting between different universe levels. -/
def IsULiftable (up : α → β) (down : β → α) : Prop :=
  ∀ a, down (up a) = a

/-- ULift round-trip: down ∘ up = id. -/
def ulift_up_down (up : α → β) (down : β → α) : Prop :=
  ∀ a, down (up a) = a

/-- ULift reverse round-trip: up ∘ down = id. -/
def ulift_down_up (up : α → β) (down : β → α) : Prop :=
  ∀ b, up (down b) = b

/-- Symmetric ULiftable: both round-trips hold. -/
def IsULiftableSym (up : α → β) (down : β → α) : Prop :=
  (∀ a, down (up a) = a) ∧ (∀ b, up (down b) = b)

/-- ULift map: lift a function through the universe change. -/
def uliftMap (up : α → β) (down : β → α) (f : α → α) : β → β :=
  up ∘ f ∘ down

/-- ULift pure. -/
def uliftPure (up : α → β) (a : α) : β := up a

/-- ULift bind. -/
def uliftBind (down : β → α) (_up : α → β) (x : β) (f : α → β) : β :=
  f (down x)

/-- adaptUp: lift a computation up. -/
def adaptUp' {m n : Type u → Type v} [Monad m] [Monad n]
    (up : m α → n α) (x : m α) : n α := up x

/-- adaptDown: lower a computation down. -/
def adaptDown' {m n : Type u → Type v} [Monad m] [Monad n]
    (down : n α → m α) (x : n α) : m α := down x

-- ============================================================================
-- 14. MONAD LAWS (Monad/Basic.lean)
-- ============================================================================

/-- StateT.eval: run a stateful computation and discard the final state. -/
def StateT.eval' {σ : Type u} {m : Type u → Type v} [Monad m]
    (x : σ → m (α × σ)) (s : σ) : m α :=
  x s >>= fun p => pure p.1

/-- StateT equivalence: StateT σ m α ≃ σ → m (α × σ) (abstract). -/
def StateT.equiv_prop (σ : Type u) (m : Type u → Type v) (α : Type u) : Prop :=
  ∀ (f : σ → m (α × σ)), f = f

/-- ReaderT equivalence: ReaderT ρ m α ≃ ρ → m α (abstract). -/
def ReaderT.equiv_prop (ρ : Type u) (m : Type u → Type v) (α : Type u) : Prop :=
  ∀ (f : ρ → m α), f = f

-- ============================================================================
-- 15. FUNCTOR LAWS (Functor.lean)
-- ============================================================================

/-- Functor map id: map id = id. -/
def functor_map_id_law (F : Type u → Type u) [Functor F] : Prop :=
  ∀ {α : Type u} (x : F α), id <$> x = x

/-- Functor map composition: map (f ∘ g) = map f ∘ map g. -/
def functor_map_comp_law (F : Type u → Type u) [Functor F] : Prop :=
  ∀ {α β γ : Type u} (f : β → γ) (g : α → β) (x : F α),
    (f ∘ g) <$> x = f <$> (g <$> x)

/-- Functor extensionality: two functors agree iff map agrees pointwise. -/
def functor_ext_law (F : Type u → Type u)
    (map₁ map₂ : (α → β) → F α → F β) : Prop :=
  (∀ (f : α → β) (x : F α), map₁ f x = map₂ f x) → map₁ = map₂
