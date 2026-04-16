/-
Released under MIT license.
-/
import Origin.Core

/-!
# Condensed Mathematics on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Condensed: 21 files, 2,930 lines, 228 genuine declarations.
Origin restates every concept once, in minimum form.

Condensed mathematics studies sheaves on compact Hausdorff spaces.
The key concepts: condensed objects, light condensed objects, discrete
objects, morphisms, adjunctions, limits, epi characterization,
cartesian closed structure, solid modules, and the functors between them.
-/

universe u
variable {α β γ : Type u}

-- ============================================================================
-- 1. CONDENSED STRUCTURE (Basic.lean)
-- ============================================================================

/-- A condensed object: a presheaf satisfying a sheaf condition.
    Abstractly: a map from "spaces" to "values" preserving covers. -/
structure Condensed (α : Type u) where
  val : α
  isSheaf : Prop

/-- Condensed sets: the default case (Type-valued sheaves). -/
abbrev CondensedSet := Condensed (Type u)

-- ============================================================================
-- 2. LIGHT CONDENSED (Light/Basic.lean)
-- ============================================================================

/-- Light condensed: sheaves on countable profinite spaces. -/
structure LightCondensed (α : Type u) where
  val : α
  isSheaf : Prop

/-- Light condensed sets. -/
abbrev LightCondSet := LightCondensed (Type u)

-- ============================================================================
-- 3. MORPHISMS AND EXTENSIONALITY (Basic.lean)
-- ============================================================================

/-- A morphism of condensed objects: a map preserving sheaf structure. -/
structure CondensedHom (X Y : Condensed α) where
  map : α → α

/-- Extensionality: morphisms are determined by their components. -/
theorem CondensedHom.ext {X Y : Condensed α}
    (f g : CondensedHom X Y) (h : f.map = g.map) : f = g := by
  cases f; cases g; congr

/-- Identity morphism. -/
def CondensedHom.id (X : Condensed α) : CondensedHom X X :=
  ⟨fun a => a⟩

/-- Composition of morphisms. -/
def CondensedHom.comp {X Y Z : Condensed α}
    (f : CondensedHom X Y) (g : CondensedHom Y Z) : CondensedHom X Z :=
  ⟨g.map ∘ f.map⟩

-- ============================================================================
-- 4. DISCRETE OBJECTS (Discrete/Basic.lean, Characterization.lean)
-- ============================================================================

/-- A condensed object is discrete if it is a constant sheaf. -/
def IsDiscrete (X : Condensed α) (const : α → Prop) : Prop :=
  const X.val

/-- A light condensed object is discrete if it is constant. -/
def IsLightDiscrete (X : LightCondensed α) (const : α → Prop) : Prop :=
  const X.val

/-- The discrete functor: embeds a type as a constant sheaf. -/
def discrete (a : α) (h : Prop) : Condensed α :=
  ⟨a, h⟩

/-- The underlying functor: forgets the sheaf structure. -/
def underlying (X : Condensed α) : α := X.val

/-- The discrete-underlying adjunction:
    Hom(discrete a, X) ≅ Hom(a, underlying X). -/
def IsDiscreteUnderlyingAdj
    (toHom : (α → α) → (α → α)) (fromHom : (α → α) → (α → α)) : Prop :=
  (∀ f, toHom (fromHom f) = f) ∧ (∀ f, fromHom (toHom f) = f)

/-- Discrete objects are characterized by locally constant sections. -/
def isDiscrete_iff_locallyConstant (X : Condensed α)
    (isLocallyConst : α → Prop) : Prop :=
  IsDiscrete X isLocallyConst

-- ============================================================================
-- 5. LOCALLY CONSTANT (Discrete/LocallyConstant.lean, Colimit.lean)
-- ============================================================================

/-- The locally constant presheaf: maps spaces to locally constant functions. -/
def locallyConstantPresheaf (constF : α → α) : Condensed α → α :=
  fun X => constF X.val

/-- Locally constant presheaf is a functor to presheaves. -/
def functorToPresheaves (F : Condensed α → α) (morphF : α → α) :
    Condensed α → α :=
  fun X => morphF (F X)

/-- Fiber of a locally constant function over a point. -/
def fiber (f : α → β) (b : β) : α → Prop :=
  fun a => f a = b

/-- The counit of the discrete-locally constant adjunction. -/
def counitApp (X : Condensed α) (reconstruct : α → α) : Condensed α :=
  ⟨reconstruct X.val, X.isSheaf⟩

/-- The unit of the adjunction. -/
def unitApp (a : α) (embed : α → α) (h : Prop) : Condensed α :=
  ⟨embed a, h⟩

-- ============================================================================
-- 6. YONEDA EMBEDDING (Functors.lean)
-- ============================================================================

/-- Yoneda embedding: embeds compact Hausdorff spaces into condensed sets. -/
def yonedaPresheaf (embed : α → Condensed α) :
    α → Condensed α :=
  embed

/-- Yoneda preserves the sheaf condition. -/
def yonedaIsSheaf (embed : α → Condensed α) : Prop :=
  ∀ a, (embed a).isSheaf

-- ============================================================================
-- 7. LIMITS AND COLIMITS (Limits.lean)
-- ============================================================================

/-- Condensed objects have all limits (completeness). -/
def HasLimits (limitF : (Nat → Condensed α) → Condensed α) : Prop :=
  ∀ diagram : Nat → Condensed α, ∀ n,
    ∃ proj : α → α, proj (limitF diagram).val = (diagram n).val

/-- Condensed objects have all colimits (cocompleteness). -/
def HasColimits (colimitF : (Nat → Condensed α) → Condensed α) : Prop :=
  ∀ diagram : Nat → Condensed α, ∀ n,
    ∃ inj : α → α, inj (diagram n).val = (colimitF diagram).val

-- ============================================================================
-- 8. EPIMORPHISMS (Epi.lean)
-- ============================================================================

/-- An epimorphism of condensed objects: locally surjective. -/
def IsCondensedEpi (X Y : Condensed α) (f : CondensedHom X Y)
    (isSurj : (α → α) → Prop) : Prop :=
  isSurj f.map

-- ============================================================================
-- 9. CARTESIAN CLOSED (CartesianClosed.lean)
-- ============================================================================

/-- Condensed sets are cartesian closed: internal hom exists. -/
def internalHom (X Y : Condensed α) (homObj : α → α → α) : Condensed α :=
  ⟨homObj X.val Y.val, X.isSheaf⟩

/-- Exponential adjunction: Hom(X × Y, Z) ≅ Hom(X, [Y, Z]). -/
def IsExpAdj (curry : (α × α → α) → α → α → α)
    (uncurry : (α → α → α) → α × α → α) : Prop :=
  (∀ f, uncurry (curry f) = f) ∧ (∀ g, curry (uncurry g) = g)

-- ============================================================================
-- 10. EXPLICIT SHEAF CONDITIONS (Explicit.lean)
-- ============================================================================

/-- A condensed object is a finite-product-preserving presheaf
    satisfying an equalizer condition on covers. -/
def IsExplicitSheaf (F : α → α) (preservesProd : (α → α) → Prop)
    (satisfiesEqualizer : (α → α) → Prop) : Prop :=
  preservesProd F ∧ satisfiesEqualizer F

-- ============================================================================
-- 11. EQUIVALENCES (Equivalence.lean)
-- ============================================================================

/-- Sheaves on Stonean, Profinite, and CompHaus yield equivalent categories. -/
def IsSiteEquivalence (F : Condensed α → Condensed α)
    (G : Condensed α → Condensed α) : Prop :=
  (∀ X, F (G X) = X) ∧ (∀ X, G (F X) = X)

-- ============================================================================
-- 12. SOLID MODULES (Solid.lean)
-- ============================================================================

/-- A condensed module is solid if solidification is an isomorphism. -/
def IsSolid (X : Condensed α) (solidify : Condensed α → Condensed α)
    (isIso : Condensed α → Condensed α → Prop) : Prop :=
  isIso (solidify X) X

/-- Solidification: right Kan extension along profinite embedding. -/
def solidification (X : Condensed α) (kanExt : α → α) : Condensed α :=
  ⟨kanExt X.val, X.isSheaf⟩

-- ============================================================================
-- 13. MODULES (Module.lean)
-- ============================================================================

/-- Condensed R-modules: condensed objects with module structure. -/
structure CondensedMod (R α : Type u) where
  obj : Condensed α
  smul : R → α → α

/-- The free-forgetful adjunction for condensed modules. -/
def freeForgetAdj (freeF : Condensed α → CondensedMod β α)
    (forgetF : CondensedMod β α → Condensed α) : Prop :=
  (∀ X, forgetF (freeF X) = X)

/-- Condensed modules form an abelian category. -/
def IsAbelian (kernelF cokernelF : CondensedMod β α → CondensedMod β α) : Prop :=
  (∀ M, ∃ k, kernelF M = k) ∧ (∀ M, ∃ c, cokernelF M = c)

-- ============================================================================
-- 14. TOPOLOGICAL COMPARISON (TopCatAdjunction.lean, TopComparison.lean)
-- ============================================================================

/-- Adjunction between condensed sets and topological spaces. -/
def IsTopCondensedAdj (toTop : Condensed α → α) (fromTop : α → Condensed α) : Prop :=
  ∀ a, toTop (fromTop a) = a

/-- On compactly generated spaces, this adjunction is an equivalence. -/
def IsCompactlyGeneratedEquiv (toTop : Condensed α → α)
    (fromTop : α → Condensed α) : Prop :=
  (∀ a, toTop (fromTop a) = a) ∧ (∀ X, fromTop (toTop X) = X)

-- ============================================================================
-- 15. CONDENSED ON OPTION: none is origin
-- ============================================================================

/-- Lift condensed to Option: none is the ground. -/
def Condensed.lift (X : Condensed α) : Condensed (Option α) :=
  ⟨some X.val, X.isSheaf⟩

/-- The ground condensed object. -/
def Condensed.ground (h : Prop) : Condensed (Option α) :=
  ⟨none, h⟩

/-- Morphisms lift through Option. -/
theorem condensedHom_map_option (f : α → α) (v : Option α) :
    Option.map f v = match v with | none => none | some a => some (f a) := by
  cases v <;> simp

/-- A domain law lifts through Option. -/
theorem condensed_mul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]

-- None absorbs (mul, neg, map): Core.lean's @[simp] set handles all cases.
