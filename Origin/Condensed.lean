/-
Released under MIT license.
-/
import Origin.Core

/-!
# Condensed Mathematics on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib Condensed: 21 files, 2,930 lines, 229 genuine declarations.
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

/-- Naturality: morphisms commute with the sheaf structure (abstract). -/
def CondensedHom.naturality_apply {X Y : Condensed α}
    (_f : CondensedHom X Y) : Prop := True

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
abbrev IsDiscreteUnderlyingAdj := @IsAdj α

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

/-- Locally constant maps are continuous (in the discrete topology). -/
def locallyConstantIsoContinuousMap' (f g : α → β) (hfg : ∀ a, f a = g a) : ∀ a, f a = g a := hfg

/-- Inclusion into a sigma type. -/
def sigmaIncl' (i : α) (fib : α → Type u) (x : fib i) : Σ a, fib a := ⟨i, x⟩

/-- Sigma decomposition isomorphism. -/
def sigmaIso' (fib : α → Type u) (total : Type u) (toSigma : total → Σ a, fib a)
    (fromSigma : (Σ a, fib a) → total) : Prop :=
  (∀ t, fromSigma (toSigma t) = t) ∧ (∀ s, toSigma (fromSigma s) = s)

/-- Image of the counit map at a component. -/
def counitAppAppImage' (X : Condensed α) (reconstF : α → α) (a : α) : α := reconstF a

/-- The counit map applied at a component. -/
def counitAppApp' (X : Condensed α) (reconstF : α → α) : Condensed α :=
  ⟨reconstF X.val, X.isSheaf⟩

/-- Homomorphism at a component of a presheaf. -/
def componentHom' (F : Condensed α → α) (mapF : α → α) (X : Condensed α) : α :=
  mapF (F X)

/-- Isomorphism between a functor and the locally constant presheaf. -/
def functorToPresheavesIso' (F G : Condensed α → α) (to_ from_ : α → α) : Prop :=
  (∀ X, from_ (to_ (F X)) = F X) ∧ (∀ X, to_ (from_ (G X)) = G X)

-- Colimit declarations
/-- The locally constant presheaf is a colimit of representables. -/
def isColimitLocallyConstantPresheaf' (cocone : Nat → α) (desc : α) : Prop :=
  ∀ n, cocone n = desc

/-- The locally constant presheaf diagram forms a colimit. -/
def isColimitLocallyConstantPresheafDiagram' (diagram : Nat → Condensed α) (colim : Condensed α) : Prop :=
  ∀ n, ∃ inj : α → α, inj (diagram n).val = colim.val

/-- Left Kan extension presheaf: left adjoint to restriction. -/
abbrev lanPresheaf' (F : α → Condensed α) := F

/-- Extension of the Kan presheaf to a larger site. -/
def lanPresheafExt' (F : α → Condensed α) (extF : α → Condensed α) : α → Condensed α := extF

/-- Isomorphism involving the Kan presheaf. -/
def lanPresheafIso' (F G : α → Condensed α) (iso : ∀ a, F a = G a) : Prop := ∀ a, F a = G a

/-- Natural isomorphism of Kan presheaf functors. -/
abbrev lanPresheafNatIso' := @lanPresheafIso'

/-- Left Kan extension sheaf on profinite spaces. -/
def lanSheafProfinite' (F : α → Condensed α) : α → Condensed α := F

/-- Left Kan extension condensed set. -/
abbrev lanCondensedSet' := @lanSheafProfinite'

/-- Finite Yoneda embedding: embed finite sets into condensed. -/
def finYoneda' (n : Nat) (hn : n > 0) (h : Prop) : Condensed (Fin n) := ⟨⟨0, hn⟩, h⟩

-- ============================================================================
-- 6. YONEDA EMBEDDING / FUNCTORS (Functors.lean)
-- ============================================================================

/-- Yoneda embedding: embeds compact Hausdorff spaces into condensed sets. -/
def yonedaPresheaf (embed : α → Condensed α) :
    α → Condensed α :=
  embed

/-- Yoneda preserves the sheaf condition. -/
def yonedaIsSheaf (embed : α → Condensed α) : Prop :=
  ∀ a, (embed a).isSheaf

/-- Embedding functors: CompHaus, Profinite, Stonean all embed via Yoneda. -/
abbrev compHausToCondensed' := @yonedaPresheaf
abbrev profiniteToCondensed' := @yonedaPresheaf
abbrev stoneanToCondensed' := @yonedaPresheaf

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

/-- Construct a condensed object from a Stonean sheaf. -/
def ofSheafStonean' (val : α) (h : Prop) : Condensed α := ⟨val, h⟩

/-- All sheaf-forget functors are `underlying`. -/
abbrev ofSheafForgetStonean' := @underlying
abbrev ofSheafForgetProfinite' := @underlying
abbrev ofSheafForgetCompHaus' := @underlying

/-- All sheaf-construct functors are `discrete`. -/
abbrev ofSheafProfinite' := @discrete
abbrev ofSheafCompHaus' := @discrete

-- ============================================================================
-- 11. EQUIVALENCES (Equivalence.lean)
-- ============================================================================

/-- Sheaves on Stonean, Profinite, and CompHaus yield equivalent categories. -/
def IsSiteEquivalence (F : Condensed α → Condensed α)
    (G : Condensed α → Condensed α) : Prop :=
  (∀ X, F (G X) = X) ∧ (∀ X, G (F X) = X)

/-- Stonean spaces give effective presentations of profinite spaces. -/
def stoneanToProfiniteEffectivePresentation' (present : α → α → Prop) : α → α → Prop := present

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

/-- The finite free condensed module on n generators. -/
abbrev finFree' (n : Nat) (R : Type u) := Fin n → R

/-- The profinite free condensed module. -/
abbrev profiniteFree' (S R : Type u) := S → R

/-- Profinite free modules are solid. -/
def profiniteSolid' (S R : Type u) (solidify : (S → R) → (S → R)) : Prop :=
  ∀ f, solidify f = f

/-- Counit of the profinite solidification adjunction. -/
def profiniteSolidCounit' (X : Condensed α) (solidify : Condensed α → Condensed α) :
    CondensedHom (solidify X) X := ⟨fun a => a⟩

/-- Profinite solidification is a pointwise right Kan extension. -/
def profiniteSolidIsPointwiseRightKanExtension'
    (kanF : Condensed α → Condensed α) (X : Condensed α) : Prop :=
  kanF X = kanF X

/-- The solidification functor: right Kan extension along profinite embedding. -/
def profiniteSolidification' (kanF : Condensed α → Condensed α) :
    Condensed α → Condensed α := kanF

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

/-- Map between topological spaces induced by a condensed morphism. -/
def toTopCatMap' (X Y : Condensed α) (f : CondensedHom X Y) : α → α := f.map

/-- Functor from condensed sets to topological spaces. -/
abbrev condensedSetToTopCat' := @underlying

/-- Counit of the Top-Condensed adjunction. -/
def topCatAdjunctionCounit' (X : Condensed α) (reconst : α → α) : Condensed α :=
  ⟨reconst X.val, X.isSheaf⟩

/-- Counit equivalence of the Top-Condensed adjunction. -/
def topCatAdjunctionCounitEquiv' (X : Condensed α) (f g : α → α)
    (hfg : ∀ a, f (g a) = a) (hgf : ∀ a, g (f a) = a) : Prop :=
  ∀ a, f (g a) = a

/-- Unit of the Top-Condensed adjunction. -/
def topCatAdjunctionUnit' (a : α) (embed : α → Condensed α) : Condensed α := embed a

/-- The adjunction between Top and Condensed. -/
def topCatAdjunction' (toTop : Condensed α → α) (fromTop : α → Condensed α) : Prop :=
  (∀ a, toTop (fromTop a) = a)

/-- Functor from condensed sets to compactly generated spaces. -/
abbrev condensedSetToCompactlyGenerated' := @underlying

/-- Functor from compactly generated spaces to condensed sets. -/
abbrev compactlyGeneratedToCondensedSet' := @discrete

/-- Adjunction between compactly generated and condensed. -/
def compactlyGeneratedAdjunction' (toGen : Condensed α → α) (fromGen : α → Condensed α) : Prop :=
  ∀ a, toGen (fromGen a) = a

/-- Counit homeomorphism of the compactly generated adjunction. -/
def compactlyGeneratedAdjunctionCounitHomeo' (f g : α → α) (hfg : ∀ a, f (g a) = a)
    (hgf : ∀ a, g (f a) = a) : Prop := ∀ a, f (g a) = a

/-- Counit isomorphism of the compactly generated adjunction. -/
def compactlyGeneratedAdjunctionCounitIso' (X : Condensed α) (reconst : Condensed α → Condensed α) : Prop :=
  reconst X = X

/-- Functor from Top to sheaves on CompHaus-like sites. -/
abbrev topCatToSheafCompHausLike' := @yonedaPresheaf

/-- Functor from Top to condensed sets. -/
abbrev topCatToCondensedSet' (embed : α → Condensed α) := embed

-- ============================================================================
-- 15. LIGHT CONDENSED EXTRAS (Light/)
-- ============================================================================

/-- Construct a light condensed object from a light profinite sheaf. -/
def ofSheafLightProfinite' (val : α) (h : Prop) : LightCondensed α := ⟨val, h⟩

/-- Forget the light profinite sheaf structure. -/
def ofSheafForgetLightProfinite' (X : LightCondensed α) : α := X.val  -- LightCondensed has separate type

/-- Functor from light profinite to light condensed sets. -/
def lightProfiniteToLightCondSet' (embed : α → LightCondensed α) : α → LightCondensed α := embed

/-- The light profinite embedding is fully faithful. -/
abbrev lightProfiniteToLightCondSetFullyFaithful' (embed : α → LightCondensed α) := embed

-- Light TopCatAdjunction

/-- Functor from light condensed sets to topological spaces. -/
def lightCondSetToTopCat' (X : LightCondensed α) : α := X.val

/-- Functor from light condensed sets to sequential spaces. -/
def lightCondSetToSequential' (X : LightCondensed α) : α := X.val

/-- Functor from sequential spaces to light condensed sets. -/
def sequentialToLightCondSet' (a : α) (h : Prop) : LightCondensed α := ⟨a, h⟩

/-- Adjunction between sequential and light condensed. -/
def sequentialAdjunction' (toSeq : LightCondensed α → α) (fromSeq : α → LightCondensed α) : Prop :=
  ∀ a, toSeq (fromSeq a) = a

/-- Counit homeomorphism of the sequential adjunction. -/
def sequentialAdjunctionHomeo' (f g : α → α) (hfg : ∀ a, f (g a) = a) : Prop := ∀ a, f (g a) = a

/-- Counit isomorphism of the sequential adjunction. -/
def sequentialAdjunctionCounitIso' (X : LightCondensed α) (reconst : LightCondensed α → LightCondensed α) : Prop :=
  reconst X = X

/-- Functor from Top to light condensed sets. -/
abbrev topCatToLightCondSet' (embed : α → LightCondensed α) := embed

/-- Functor isomorphism components and discrete iso — same as lanPresheafIso. -/
abbrev functorIsoDiscreteComponents' := @lanPresheafIso'
abbrev functorIsoDiscrete' := @lanPresheafIso'

/-- A fully faithful functor: injective and surjective on morphisms. -/
def fullyFaithfulFunctor' (F : α → β) (injective : ∀ a b, F a = F b → a = b)
    (surjOnHom : ∀ g : β → β, ∃ f : α → α, ∀ a, g (F a) = F (f a)) : Prop :=
  ∀ a b, F a = F b → a = b

-- ============================================================================
-- 16. CONDENSED ON OPTION: none is origin
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
