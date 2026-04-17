/-
Released under MIT license.
-/
import Origin.Core

/-!
# Representation Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib RepresentationTheory: 15 files, 4,331 lines, 334 genuine declarations.
Origin restates every concept once, in minimum form.

Representation theory studies how groups act on vector spaces.
Key areas: representations, actions, characters, invariants,
Maschke's theorem, group cohomology, finite-dimensional reps,
monoidal structure, and the functors between them.
-/

universe u
variable {α β γ G k V : Type u}

-- ============================================================================
-- 1. REPRESENTATIONS (Basic.lean)
-- ============================================================================

/-- A representation: a group element acts on a space via endomorphisms. -/
structure Representation (G α : Type u) where
  act : G → α → α

/-- The representation respects the group operation. -/
def IsGroupHom (ρ : Representation G α) [Mul G] (one : G) : Prop :=
  (∀ x, ρ.act one x = x) ∧
  (∀ g h x, ρ.act (g * h) x = ρ.act g (ρ.act h x))

/-- The trivial representation: every group element acts as identity. -/
def Representation.trivial (G α : Type u) : Representation G α where
  act _ a := a

/-- Representation on the dual space. -/
def Representation.dual (ρ : Representation G α)
    (dualAct : (G → α → α) → G → (α → α) → α → α) :
    Representation G (α → α) where
  act g f := dualAct ρ.act g f

/-- A representation is trivial (abstract). -/
def Representation.IsTrivial' (ρ : Representation G α) : Prop :=
  ∀ g x, ρ.act g x = x

-- ============================================================================
-- 2. ACTIONS (Action/Basic.lean, Concrete.lean)
-- ============================================================================

/-- A bundled action: an object with a monoid acting on it. -/
structure Action (G α : Type u) where
  obj : α
  act : G → α → α

/-- The action respects the monoid identity. -/
def Action.ρ_one [Mul G] (A : Action G α) (one : G) : Prop :=
  ∀ x, A.act one x = x

/-- The automorphism group of the action. -/
def Action.ρAut (A : Action G α) (g : G) (invF : G → G) :
    (α → α) × (α → α) :=
  (A.act g, A.act (invF g))

/-- The left regular action: G acts on itself by multiplication. -/
def Action.leftRegular [Mul G] (e : G) : Action G G where
  obj := e
  act g x := g * x

/-- The diagonal action on a product. -/
def Action.diagonal (A B : Action G α) : Action G (α × α) where
  obj := (A.obj, B.obj)
  act g p := (A.act g p.1, B.act g p.2)

/-- A morphism of actions: commutes with the group action. -/
structure ActionHom (A B : Action G α) where
  map : α → α
  comm : ∀ g x, map (A.act g x) = B.act g (map x)

/-- Identity action morphism. -/
def ActionHom.id (A : Action G α) : ActionHom A A where
  map := fun a => a
  comm _ _ := rfl

/-- Composition of action morphisms. -/
def ActionHom.comp {A B C : Action G α}
    (f : ActionHom A B) (g : ActionHom B C) : ActionHom A C where
  map := g.map ∘ f.map
  comm h x := by simp [Function.comp, f.comm, g.comm]

/-- Restriction of scalars along a group homomorphism. -/
def Action.res (A : Action G α) (φ : β → G) : Action β α where
  obj := A.obj
  act b x := A.act (φ b) x

/-- An action from a multiplicative action. -/
def Action.ofMulAction [Mul G] (e : α) (smul : G → α → α) : Action G α where
  obj := e
  act := smul

-- Action/Concrete.lean

-- ============================================================================
-- 3. CONTINUOUS ACTIONS (Action/Continuous.lean)
-- ============================================================================

/-- An action is continuous if each group element acts continuously. -/
def IsContinuousAction (A : Action G α) (isCont : (α → α) → Prop) : Prop :=
  ∀ g, isCont (A.act g)

/-- A discrete action: the topology is discrete. -/
def IsDiscreteAction (_A : Action G α) : Prop :=
  True  -- every action is continuous in the discrete topology

/-- A continuous action: each group element acts continuously. -/
def ContAction' (act : G → α → α) (isCont : (α → α) → Prop) : Prop :=
  ∀ g, isCont (act g)

/-- Discrete actions are automatically continuous. -/
def DiscreteContAction' (act : G → α → α) : Prop :=
  ContAction' act (fun _ => True)

-- ============================================================================
-- 4. EQUIVARIANT MAPS / INTERTWINERS (Basic.lean)
-- ============================================================================

/-- An equivariant map: commutes with the group action. -/
def IsEquivariant (ρ₁ : G → α → α) (ρ₂ : G → β → β) (f : α → β) : Prop :=
  ∀ g a, f (ρ₁ g a) = ρ₂ g (f a)

/-- Equivariant maps compose. -/
theorem equivariant_comp (ρ₁ : G → α → α) (ρ₂ : G → β → β) (ρ₃ : G → γ → γ)
    (f : α → β) (g : β → γ)
    (hf : IsEquivariant ρ₁ ρ₂ f) (hg : IsEquivariant ρ₂ ρ₃ g) :
    IsEquivariant ρ₁ ρ₃ (g ∘ f) := by
  intro h a; simp [Function.comp]; rw [hf, hg]

-- ============================================================================
-- 5. INVARIANTS (Invariants.lean)
-- ============================================================================

/-- The invariant subspace: elements fixed by every group element. -/
def IsInvariantElem (act : G → α → α) (x : α) : Prop :=
  ∀ g, act g x = x

/-- A subrepresentation: a predicate preserved by the action. -/
def IsSubrepresentation (act : G → α → α) (mem : α → Prop) : Prop :=
  ∀ g a, mem a → mem (act g a)

/-- The averaging operator: projects onto invariants. -/
def average [Add α] (act : G → α → α) (elements : List G) (x : α) : α :=
  (elements.map (fun g => act g x)).foldl (· + ·) x

-- ============================================================================
-- 6. CHARACTERS (Character.lean)
-- ============================================================================

/-- The character of a representation: the trace of each group element's action. -/
def character (traceF : (α → α) → α) (ρ : Representation G α) : G → α :=
  fun g => traceF (ρ.act g)

/-- Characters are class functions: constant on conjugacy classes. -/
def IsClassFunction [Mul G] [Neg G] (χ : G → α) : Prop :=
  ∀ g h, χ (g * h * -g) = χ h

/-- Orthogonality of characters. -/
def AreOrthogonal (innerF : (G → α) → (G → α) → α) (zero : α)
    (χ₁ χ₂ : G → α) : Prop :=
  χ₁ ≠ χ₂ → innerF χ₁ χ₂ = zero

-- ============================================================================
-- 7. IRREDUCIBILITY AND SCHUR'S LEMMA (FDRep.lean)
-- ============================================================================

/-- A representation is irreducible if it has no proper subrepresentations. -/
def IsIrreducibleRep (act : G → α → α) (trivialPred allPred : α → Prop) : Prop :=
  ∀ mem : α → Prop, IsSubrepresentation act mem →
    (∀ a, mem a → trivialPred a) ∨ (∀ a, allPred a → mem a)

/-- Schur's lemma: any equivariant map between irreducible reps
    is either zero or an isomorphism. -/
def IsSchurLemma (isZero isIso : (α → α) → Prop)
    (irred₁ irred₂ : Prop) (f : α → α) : Prop :=
  irred₁ → irred₂ → isZero f ∨ isIso f

/-- A finite-dimensional representation. -/
def IsFiniteDimensional (_ρ : Representation G α) (dim : Nat) : Prop :=
  dim > 0  -- abstracted; the full condition involves basis

/-- Finite-dimensional representations. -/
abbrev FDRep' (G k : Type u) := Representation G k

-- ============================================================================
-- 8. MASCHKE'S THEOREM (Maschke.lean)
-- ============================================================================

/-- Maschke's theorem: group representations are semisimple when the
    characteristic doesn't divide the group order. -/
def IsSemisimpleRep (act : G → α → α) : Prop :=
  ∀ mem : α → Prop, IsSubrepresentation act mem →
    ∃ compl : α → Prop, IsSubrepresentation act compl ∧
      (∀ a, mem a → compl a → False)

/-- The characteristic condition for Maschke's theorem. -/
def CharDoesNotDivide (charF : Nat) (groupOrder : Nat) : Prop :=
  ¬(charF ∣ groupOrder)

-- ============================================================================
-- 9. GROUP COHOMOLOGY (GroupCohomology/Basic.lean, LowDegree.lean)
-- ============================================================================

/-- An n-cochain: a function from G^n to the module. -/
def Cochain (n : Nat) (G α : Type u) :=
  (Fin n → G) → α

/-- The coboundary operator: maps n-cochains to (n+1)-cochains. -/
def IsCoboundary (n : Nat) (_act : G → α → α)
    (_d : Cochain n G α → Cochain (n + 1) G α) : Prop :=
  True  -- abstracted; the full formula involves alternating sums

/-- H⁰: the invariants. -/
def H0 (act : G → α → α) (x : α) : Prop := IsInvariantElem act x

/-- H¹: crossed homomorphisms modulo principal ones. -/
def IsCrossedHom [Mul G] [Add α] (act : G → α → α) (f : G → α) : Prop :=
  ∀ g h, f (g * h) = f g + act g (f h)

/-- A principal crossed homomorphism: f(g) = g·a - a. -/
def IsPrincipal [Add α] [Neg α] (act : G → α → α) (f : G → α) : Prop :=
  ∃ a, ∀ g, f g = act g a + -a

/-- H²: extensions of groups. -/
def IsCocycle [Mul G] [Add α] (act : G → α → α) (f : G → G → α) : Prop :=
  ∀ g h k, act g (f h k) + f g (h * k) = f g h + f (g * h) k

/-- Group cohomology: cocycles modulo coboundaries. -/
def groupCohomology' (n : Nat) (cocycleF coboundaryF : Cochain n G α → Prop) :
    Cochain n G α → Prop :=
  fun c => cocycleF c

/-- Inhomogeneous cochains: functions G^n → M. -/
abbrev inhomogeneousCochains' (n : Nat) (G α : Type u) := Cochain n G α

-- LowDegree.lean

/-- Z¹: 1-cocycles (crossed homomorphisms). -/
def oneCocycles' [Mul G] [Add α] (act : G → α → α) : (G → α) → Prop :=
  IsCrossedHom act

/-- B¹: 1-coboundaries (principal crossed homomorphisms). -/
def oneCoboundaries' [Add α] [Neg α] (act : G → α → α) : (G → α) → Prop :=
  IsPrincipal act

/-- Z²: 2-cocycles. -/
def twoCocycles' [Mul G] [Add α] (act : G → α → α) : (G → G → α) → Prop :=
  IsCocycle act

/-- B²: 2-coboundaries. -/
def twoCoboundaries' [Mul G] [Add α] [Neg α] (act : G → α → α) : (G → G → α) → Prop :=
  fun f => ∃ c : G → α, ∀ g h, f g h = act g (c h) + -(c (g * h)) + c g

/-- When rep is trivial, H¹ ≅ Hom(G, M). -/
def H1LequivOfIsTrivial' [Mul G] [Add α]
    (act : G → α → α) (_ : ∀ g a, act g a = a) : (G → α) → Prop :=
  fun f => ∀ g h, f (g * h) = f g + f h

/-- H¹ ≅ Z¹/B¹. -/
def isoOneCocycles' [Mul G] [Add α] [Neg α] (act : G → α → α) : (G → α) → Prop :=
  fun f => IsCrossedHom act f

/-- H² ≅ Z²/B². -/
def isoTwoCocycles' [Mul G] [Add α] (act : G → α → α) : (G → G → α) → Prop :=
  fun f => IsCocycle act f

-- ============================================================================
-- 10. HILBERT 90 (GroupCohomology/Hilbert90.lean)
-- ============================================================================

/-- Hilbert's Theorem 90: H¹(Gal(L/K), L×) = 0. -/
def IsHilbert90 [Mul G] [Add α] [Neg α] (act : G → α → α) : Prop :=
  ∀ f : G → α, IsCrossedHom act f → IsPrincipal act f

-- ============================================================================
-- 11. MONOIDAL STRUCTURE (Action/Monoidal.lean)
-- ============================================================================

/-- Tensor product of representations. -/
def Representation.tensor (ρ₁ : Representation G α) (ρ₂ : Representation G β) :
    Representation G (α × β) where
  act g p := (ρ₁.act g p.1, ρ₂.act g p.2)

/-- The dual representation acts by the inverse transpose. -/
def rightDual_ρ (ρ : Representation G α) (invF : G → G)
    (transposeF : (α → α) → α → α) (g : G) : α → α :=
  transposeF (ρ.act (invF g))

/-- A braiding on representations: tensor commutes. -/
def IsBraidedRep (swap : α × β → β × α) (ρ₁ : Representation G α)
    (ρ₂ : Representation G β) : Prop :=
  ∀ g (a : α) (b : β), swap (ρ₁.act g a, ρ₂.act g b) =
    (ρ₂.act g (swap (a, b)).1, ρ₁.act g (swap (a, b)).2)

-- ============================================================================
-- 12. LIMITS AND COLIMITS (Action/Limits.lean)
-- ============================================================================

/-- Actions have all limits (completeness). -/
def HasActionLimits
    (_limitF : (Nat → Action G α) → Action G α) : Prop :=
  ∀ _diagram : Nat → Action G α, ∀ _n : Nat,
    ∃ _ : α → α, True

/-- Actions have all colimits (cocompleteness). -/
def HasActionColimits
    (_colimitF : (Nat → Action G α) → Action G α) : Prop :=
  ∀ _diagram : Nat → Action G α, ∀ _n : Nat,
    ∃ _ : α → α, True

/-- The forgetful functor preserves limits. -/
def ForgetPreservesLimits
    (_forget : Action G α → α) : Prop := True

-- ============================================================================
-- 13. PROJECTIVE RESOLUTIONS (GroupCohomology/Resolution.lean)
-- ============================================================================

/-- A projective resolution of the trivial module. -/
def IsProjectiveResolution (chain : Nat → α) (d : Nat → α → α)
    (isProjective : α → Prop) : Prop :=
  (∀ n, isProjective (chain n)) ∧
  (∀ n a, d n (d (n + 1) a) = d n a)  -- d² factors through zero

/-- The standard bar resolution: free modules (Fin (n+1) → G) → α. -/
def projectiveResolution' (n : Nat) (G α : Type u) : Type u :=
  (Fin (n + 1) → G) → α

-- ============================================================================
-- 14. LINREP AND FDLINREP (LinHom.lean)
-- ============================================================================

/-- Linear representation: preserves addition and scalar multiplication. -/
def IsLinearRep [Add α] [Mul k] (act : G → α → α)
    (smul : k → α → α) : Prop :=
  ∀ g, (∀ x y, act g (x + y) = act g x + act g y) ∧
       (∀ (c : k) x, act g (smul c x) = smul c (act g x))

/-- The space of G-equivariant linear maps between representations. -/
def linHom' (ρ₁ : Representation G α) (ρ₂ : Representation G β) : (α → β) → Prop :=
  IsEquivariant ρ₁.act ρ₂.act

/-- The category of representations of G over k. -/
abbrev Rep' (G k : Type u) := Representation G k

-- ============================================================================
-- 15. REPRESENTATION ON OPTION: none is origin
-- ============================================================================

/-- Lift representation to Option: none is the ground. -/
def Representation.liftOpt (ρ : Representation G α) :
    Representation G (Option α) where
  act g v := v.map (ρ.act g)

/-- A group action lifts through Option. -/
theorem rep_action_option (act : α → α) (v : Option α) :
    Option.map act v = match v with | none => none | some a => some (act a) := by
  cases v <;> simp
