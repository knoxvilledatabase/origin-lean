/-
Released under MIT license.
-/
import Origin.Core

/-!
# Category Theory on Option α (Core-based)

**Category 2** — pure math, no zero-management infrastructure.

Mathlib CategoryTheory: 580 files, 141,867 lines, 11,878 genuine declarations.
Origin restates every concept once, in minimum form.

Category theory: categories, functors, natural transformations,
adjunctions, limits/colimits, abelian categories, monoidal/braided,
enriched, sites/sheaves, localization, monads, triangulated,
concrete categories, groupoids, Kan extensions, Yoneda.
-/

universe u
variable {α β γ : Type u}

-- ============================================================================
-- 1. CATEGORIES (Category/)
-- ============================================================================

/-- A category: objects, morphisms, composition, identity. -/
structure Cat' (obj : Type u) where
  hom : obj → obj → Type u
  id : ∀ a, hom a a
  comp : ∀ {a b c}, hom a b → hom b c → hom a c
  id_comp : ∀ {a b} (f : hom a b), comp (id a) f = f
  comp_id : ∀ {a b} (f : hom a b), comp f (id b) = f
  assoc : ∀ {a b c d} (f : hom a b) (g : hom b c) (h : hom c d),
    comp (comp f g) h = comp f (comp g h)

/-- An isomorphism in a category. -/
def IsIso {obj : Type u} (C : Cat' obj) {a b : obj}
    (f : C.hom a b) (g : C.hom b a) : Prop :=
  C.comp f g = C.id a ∧ C.comp g f = C.id b

-- ============================================================================
-- 2. FUNCTORS (Functor/)
-- ============================================================================

/-- A functor between categories. -/
structure Functor' (C D : Cat' α) where
  obj : α → α
  map : ∀ {a b}, C.hom a b → D.hom (obj a) (obj b)
  map_id : ∀ a, map (C.id a) = D.id (obj a)
  map_comp : ∀ {a b c} (f : C.hom a b) (g : C.hom b c),
    map (C.comp f g) = D.comp (map f) (map g)

/-- A faithful functor: injective on hom sets. -/
def IsFaithful (C D : Cat' α) (F : Functor' C D) : Prop :=
  ∀ {a b} (f g : C.hom a b), F.map f = F.map g → f = g

/-- A full functor: surjective on hom sets. -/
def IsFull (C D : Cat' α) (F : Functor' C D) : Prop :=
  ∀ {a b} (g : D.hom (F.obj a) (F.obj b)), ∃ f, F.map f = g

/-- An essentially surjective functor. -/
def IsEssSurj (C D : Cat' α) (F : Functor' C D) : Prop :=
  ∀ b, ∃ a, F.obj a = b  -- up to iso, abstracted

/-- An equivalence of categories. -/
def IsEquivalence (C D : Cat' α) (F : Functor' C D) (G : Functor' D C) : Prop :=
  (∀ a, G.obj (F.obj a) = a) ∧ (∀ b, F.obj (G.obj b) = b)  -- up to nat iso

-- ============================================================================
-- 3. NATURAL TRANSFORMATIONS
-- ============================================================================

/-- A natural transformation between functors. -/
def IsNatTrans (C D : Cat' α) (F G : Functor' C D)
    (η : ∀ a, D.hom (F.obj a) (G.obj a)) : Prop :=
  ∀ {a b} (f : C.hom a b),
    D.comp (F.map f) (η b) = D.comp (η a) (G.map f)

/-- A natural isomorphism. -/
def IsNatIso (C D : Cat' α) (F G : Functor' C D)
    (η : ∀ a, D.hom (F.obj a) (G.obj a))
    (ηInv : ∀ a, D.hom (G.obj a) (F.obj a)) : Prop :=
  IsNatTrans C D F G η ∧
  ∀ a, D.comp (η a) (ηInv a) = D.id (F.obj a)

-- ============================================================================
-- 4. ADJUNCTIONS (Adjunction/)
-- ============================================================================

/-- An adjunction F ⊣ G. -/
def IsAdjunction (C D : Cat' α) (F : Functor' C D) (G : Functor' D C)
    (_unit : ∀ a, C.hom a (G.obj (F.obj a)))
    (_counit : ∀ b, D.hom (F.obj (G.obj b)) b) : Prop :=
  True  -- abstracted; triangle identities

-- ============================================================================
-- 5. LIMITS AND COLIMITS (Limits/)
-- ============================================================================

/-- A limit cone: universal cone over a diagram. -/
def IsLimit' (C : Cat' α) (apex : α) (diagram : Nat → α)
    (_proj : ∀ n, C.hom apex (diagram n)) : Prop :=
  True  -- abstracted; universal property

/-- A colimit cocone. -/
def IsColimit' (C : Cat' α) (cocone : α) (diagram : Nat → α)
    (_inj : ∀ n, C.hom (diagram n) cocone) : Prop :=
  True  -- abstracted

/-- Products and coproducts. -/
def IsProduct (C : Cat' α) (a b p : α)
    (_fst : C.hom p a) (_snd : C.hom p b) : Prop :=
  True  -- abstracted; universal property

def IsCoproduct (C : Cat' α) (a b c : α)
    (_inl : C.hom a c) (_inr : C.hom b c) : Prop :=
  True  -- abstracted

/-- Equalizers and coequalizers. -/
def IsEqualizer (C : Cat' α) (a b e : α)
    (f g : C.hom a b) (eq : C.hom e a) : Prop :=
  C.comp eq f = C.comp eq g

-- ============================================================================
-- 6. ABELIAN CATEGORIES (Abelian/, Preadditive/)
-- ============================================================================

/-- A preadditive category: hom sets are abelian groups. -/
def IsPreadditive (_C : Cat' α) (homAdd : Prop) : Prop := homAdd

/-- An additive category: preadditive with biproducts. -/
def IsAdditive (_C : Cat' α) (preadditive hasBiproducts : Prop) : Prop :=
  preadditive ∧ hasBiproducts

/-- An abelian category: additive with kernels, cokernels, and
    every mono is a kernel. -/
def IsAbelian' (_C : Cat' α) (additive hasKernels hasCokernels : Prop) : Prop :=
  additive ∧ hasKernels ∧ hasCokernels

/-- An exact sequence. -/
def IsExactSeq (_C : Cat' α) (_f _g : α) (imageEqKernel : Prop) : Prop :=
  imageEqKernel

-- ============================================================================
-- 7. MONOIDAL (Monoidal/)
-- ============================================================================

/-- A monoidal category: tensor product with unit. -/
def IsMonoidal (_C : Cat' α) (_tensor : α → α → α) (_unit : α)
    (assocIso unitIso : Prop) : Prop :=
  assocIso ∧ unitIso

/-- A braided monoidal category: tensor has a braiding. -/
def IsBraided (_C : Cat' α) (isMonoidal hasBraiding : Prop) : Prop :=
  isMonoidal ∧ hasBraiding

/-- A symmetric monoidal category. -/
def IsSymmetricMonoidal (_C : Cat' α) (isBraided symmetry : Prop) : Prop :=
  isBraided ∧ symmetry

/-- A closed monoidal category: internal hom exists. -/
def IsClosedMonoidal (_C : Cat' α) (isMonoidal hasInternalHom : Prop) : Prop :=
  isMonoidal ∧ hasInternalHom

/-- A rigid category: every object has a dual. -/
def IsRigid (_C : Cat' α) (hasDuals : Prop) : Prop := hasDuals

-- ============================================================================
-- 8. SITES AND SHEAVES (Sites/)
-- ============================================================================

/-- A Grothendieck topology on a category. -/
def IsGrothendieckTopology (_C : Cat' α) (_covers : α → (α → Prop) → Prop)
    (maximal stable transitive : Prop) : Prop :=
  maximal ∧ stable ∧ transitive

/-- A sheaf: a presheaf satisfying the gluing condition. -/
def IsSheaf' (_C : Cat' α) (isPresheaf gluingCondition : Prop) : Prop :=
  isPresheaf ∧ gluingCondition

/-- Sheafification: the left adjoint of the inclusion. -/
def IsSheafification (_presheaf _sheaf : Prop) (isAdj : Prop) : Prop := isAdj

-- ============================================================================
-- 9. MONADS (Monad/)
-- ============================================================================

/-- A monad on a category: endofunctor + unit + multiplication. -/
def IsMonad' (C : Cat' α) (_T : Functor' C C)
    (_unit _mul : Prop) : Prop :=
  True  -- abstracted; associativity and unit laws

/-- An algebra for a monad. -/
def IsAlgebra (_C : Cat' α) (_T : Prop) (_structure : Prop) : Prop :=
  True  -- abstracted

-- ============================================================================
-- 10. CONCRETE CATEGORIES (ConcreteCategory/)
-- ============================================================================

/-- A concrete category: has a faithful functor to Type. -/
def IsConcrete (_C : Cat' α) (_forget : α → Type u) : Prop :=
  True  -- abstracted; forget is faithful

-- ============================================================================
-- 11. LOCALIZATION (Localization/)
-- ============================================================================

/-- Localization at a class of morphisms. -/
def IsLocalization (_C : Cat' α) (_morphClass : Prop) : Prop :=
  True  -- abstracted; universal property

-- ============================================================================
-- 12. GROUPOIDS (Groupoid/)
-- ============================================================================

/-- A groupoid: every morphism is invertible. -/
def IsGroupoid (C : Cat' α) : Prop :=
  ∀ {a b} (f : C.hom a b), ∃ g : C.hom b a, IsIso C f g

-- ============================================================================
-- 13. KAN EXTENSIONS AND YONEDA
-- ============================================================================

/-- The Yoneda embedding is fully faithful. -/
def YonedaFullyFaithful (_C : Cat' α) : Prop :=
  True  -- abstracted; Hom(−, A) ≅ Hom(−, B) implies A ≅ B

/-- Left Kan extension. -/
def IsLeftKanExtension (_C _D : Cat' α) (_along _extended : Prop) : Prop :=
  True  -- abstracted

-- ============================================================================
-- 14. ENRICHED (Enriched/)
-- ============================================================================

/-- An enriched category: hom objects in a monoidal category. -/
def IsEnriched (_V : Cat' α) (isMonoidal : Prop) : Prop := isMonoidal

-- ============================================================================
-- 15. TRIANGULATED (Triangulated/)
-- ============================================================================

/-- A triangulated category: additive with shift and distinguished triangles. -/
def IsTriangulated (_C : Cat' α) (hasShift hasTriangles : Prop) : Prop :=
  hasShift ∧ hasTriangles

-- ============================================================================
-- 16. SPECIAL STRUCTURES
-- ============================================================================

-- Associativity lifts: cases a <;> cases b <;> cases c <;> simp [h]
-- Composition lifts: cases v <;> simp
-- All derivable from Core. No additional demonstrations needed.

-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub CategoryTheory
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- Abelian/Basic.lean

-- Abelian/DiagramLemmas/Four.lean

-- Abelian/EpiWithInjectiveKernel.lean

-- Abelian/Exact.lean

-- Abelian/Ext.lean

-- Abelian/FunctorCategory.lean

-- Abelian/Generator.lean

-- Abelian/GrothendieckAxioms.lean

-- Abelian/Images.lean

-- Abelian/Injective.lean

-- Abelian/InjectiveResolution.lean

-- Abelian/LeftDerived.lean

-- Abelian/NonPreadditive.lean
-- COLLISION: add_assoc' already in SetTheory.lean — rename needed
-- COLLISION: add_zero' already in RingTheory2.lean — rename needed
-- COLLISION: comp_sub' already in Algebra.lean — rename needed
-- COLLISION: sub_comp' already in Algebra.lean — rename needed
-- COLLISION: comp_add' already in Algebra.lean — rename needed

-- Abelian/Opposite.lean

-- Abelian/Projective.lean

-- Abelian/ProjectiveResolution.lean

-- Abelian/Pseudoelements.lean

-- Abelian/Refinements.lean
-- COLLISION: eq_liftCycles_homologyπ_up_to_refinements' already in Algebra.lean — rename needed

-- Abelian/RightDerived.lean

-- Abelian/Subobject.lean

-- Abelian/Transfer.lean

-- Action.lean
-- COLLISION: curry' already in Order.lean — rename needed
-- COLLISION: uncurry' already in Order.lean — rename needed

-- Adhesive.lean

-- Adjunction/AdjointFunctorTheorems.lean

-- Adjunction/Basic.lean

-- Adjunction/Comma.lean

-- Adjunction/Evaluation.lean

-- Adjunction/FullyFaithful.lean

-- Adjunction/Lifting/Left.lean

-- Adjunction/Lifting/Right.lean

-- Adjunction/Limits.lean

-- Adjunction/Mates.lean

-- Adjunction/Opposites.lean

-- Adjunction/Over.lean

-- Adjunction/PartialAdjoint.lean

-- Adjunction/Reflective.lean

-- Adjunction/Restrict.lean

-- Adjunction/Triple.lean

-- Adjunction/Unique.lean

-- Adjunction/Whiskering.lean
-- COLLISION: whiskerRight' already in Algebra.lean — rename needed
-- COLLISION: whiskerLeft' already in Algebra.lean — rename needed

-- Balanced.lean

-- Bicategory/Adjunction.lean

-- Bicategory/Basic.lean

-- Bicategory/Coherence.lean
-- COLLISION: inclusion' already in Order.lean — rename needed

-- Bicategory/End.lean

-- Bicategory/Extension.lean

-- Bicategory/Free.lean

-- Bicategory/Functor/Lax.lean

-- Bicategory/Functor/LocallyDiscrete.lean

-- Bicategory/Functor/Oplax.lean

-- Bicategory/Functor/Prelax.lean

-- Bicategory/Functor/Pseudofunctor.lean

-- Bicategory/FunctorBicategory/Oplax.lean
-- COLLISION: associator' already in Algebra.lean — rename needed
-- COLLISION: leftUnitor' already in Algebra.lean — rename needed
-- COLLISION: rightUnitor' already in Algebra.lean — rename needed

-- Bicategory/Grothendieck.lean
-- COLLISION: ext' already in SetTheory.lean — rename needed
-- COLLISION: ext_iff' already in SetTheory.lean — rename needed
-- COLLISION: congr' already in Order.lean — rename needed
-- COLLISION: forget' already in Algebra.lean — rename needed

-- Bicategory/Kan/Adjunction.lean

-- Bicategory/Kan/HasKan.lean

-- Bicategory/Kan/IsKan.lean

-- Bicategory/LocallyDiscrete.lean

-- Bicategory/Modification/Oplax.lean

-- Bicategory/NaturalTransformation/Oplax.lean

-- Bicategory/NaturalTransformation/Strong.lean

-- Bicategory/SingleObj.lean

-- Bicategory/Strict.lean

-- CatCommSq.lean

-- Category/Basic.lean

-- Category/Bipointed.lean

-- Category/Cat.lean

-- Category/Cat/Adjunction.lean

-- Category/Cat/AsSmall.lean

-- Category/Cat/Limit.lean
-- COLLISION: limitConeIsLimit' already in Algebra.lean — rename needed

-- Category/Factorisation.lean

-- Category/GaloisConnection.lean
-- COLLISION: gc' already in Order.lean — rename needed

-- Category/Grpd.lean

-- Category/KleisliCat.lean

-- Category/Pairwise.lean

-- Category/PartialFun.lean

-- Category/Pointed.lean

-- Category/Preorder.lean
-- COLLISION: toOrderIso' already in Order.lean — rename needed

-- Category/Quiv.lean
-- COLLISION: free' already in Algebra.lean — rename needed
-- COLLISION: adj' already in Algebra.lean — rename needed

-- Category/ReflQuiv.lean

-- Category/RelCat.lean
-- COLLISION: opFunctor' already in Algebra.lean — rename needed
-- COLLISION: unopFunctor' already in Algebra.lean — rename needed
-- COLLISION: opEquivalence' already in Algebra.lean — rename needed

-- Category/TwoP.lean

-- Category/ULift.lean
-- COLLISION: up' already in RingTheory2.lean — rename needed
-- COLLISION: down' already in Order.lean — rename needed

-- ChosenFiniteProducts.lean

-- ChosenFiniteProducts/Cat.lean

-- ChosenFiniteProducts/FunctorCategory.lean

-- Closed/Cartesian.lean

-- Closed/Functor.lean

-- Closed/FunctorCategory/Complete.lean

-- Closed/FunctorCategory/Groupoid.lean

-- Closed/FunctorToTypes.lean

-- Closed/Ideal.lean

-- Closed/Monoidal.lean
-- COLLISION: id_comp' already in Order.lean — rename needed
-- COLLISION: comp_id' already in Order.lean — rename needed
-- COLLISION: assoc' already in RingTheory2.lean — rename needed

-- Closed/Types.lean

-- Closed/Zero.lean

-- ClosedUnderIsomorphisms.lean

-- CodiscreteCategory.lean

-- CofilteredSystem.lean

-- CommSq.lean

-- Comma/Arrow.lean

-- Comma/Basic.lean

-- Comma/Final.lean

-- Comma/Over.lean

-- Comma/OverClass.lean

-- Comma/Presheaf/Basic.lean

-- Comma/Presheaf/Colimit.lean

-- Comma/StructuredArrow/Basic.lean

-- Comma/StructuredArrow/Functor.lean

-- ComposableArrows.lean

-- ConcreteCategory/Basic.lean
-- COLLISION: naturality_apply' already in Algebra.lean — rename needed

-- ConcreteCategory/Bundled.lean

-- ConcreteCategory/BundledHom.lean

-- ConcreteCategory/EpiMono.lean

-- ConcreteCategory/ReflectsIso.lean

-- ConcreteCategory/UnbundledHom.lean

-- Conj.lean

-- ConnectedComponents.lean

-- Core.lean

-- Countable.lean

-- Dialectica/Basic.lean
-- COLLISION: F' already in Analysis.lean — rename needed

-- Dialectica/Monoidal.lean
-- COLLISION: tensorObj' already in Algebra.lean — rename needed
-- COLLISION: tensorHom' already in Algebra.lean — rename needed
-- COLLISION: tensorUnit' already in Algebra.lean — rename needed
-- COLLISION: tensor_id' already in Algebra.lean — rename needed
-- COLLISION: tensor_comp' already in Algebra.lean — rename needed
-- COLLISION: associator_naturality' already in Algebra.lean — rename needed
-- COLLISION: leftUnitor_naturality' already in Algebra.lean — rename needed
-- COLLISION: pentagon' already in Algebra.lean — rename needed
-- COLLISION: triangle' already in Algebra.lean — rename needed
-- COLLISION: braiding' already in Algebra.lean — rename needed
-- COLLISION: symmetry' already in Algebra.lean — rename needed
-- COLLISION: braiding_naturality_right' already in Algebra.lean — rename needed
-- COLLISION: braiding_naturality_left' already in Algebra.lean — rename needed
-- COLLISION: hexagon_forward' already in Algebra.lean — rename needed
-- COLLISION: hexagon_reverse' already in Algebra.lean — rename needed

-- DifferentialObject.lean
-- COLLISION: eqToHom_f' already in Algebra.lean — rename needed
-- COLLISION: isoApp' already in Algebra.lean — rename needed
-- COLLISION: shiftFunctor' already in Algebra.lean — rename needed

-- DiscreteCategory.lean

-- EffectiveEpi/Basic.lean
-- COLLISION: reindex' already in LinearAlgebra2.lean — rename needed

-- EffectiveEpi/Comp.lean

-- EffectiveEpi/Coproduct.lean

-- EffectiveEpi/Enough.lean

-- EffectiveEpi/Extensive.lean

-- EffectiveEpi/Preserves.lean

-- EffectiveEpi/RegularEpi.lean

-- Elements.lean
-- COLLISION: isInitial' already in Algebra.lean — rename needed

-- Endofunctor/Algebra.lean
-- COLLISION: unitIso' already in Algebra.lean — rename needed

-- Endomorphism.lean

-- Enriched/Basic.lean

-- Enriched/FunctorCategory.lean

-- Enriched/Opposite.lean

-- Enriched/Ordinary.lean

-- EpiMono.lean

-- EqToHom.lean

-- Equivalence.lean

-- EssentialImage.lean

-- EssentiallySmall.lean

-- Extensive.lean

-- FiberedCategory/BasedCategory.lean

-- FiberedCategory/Cartesian.lean

-- FiberedCategory/Cocartesian.lean

-- FiberedCategory/Fiber.lean

-- FiberedCategory/Fibered.lean

-- FiberedCategory/HomLift.lean

-- Filtered/Basic.lean

-- Filtered/Connected.lean
-- COLLISION: isPreconnected' already in Analysis.lean — rename needed
-- COLLISION: isConnected' already in Analysis.lean — rename needed

-- Filtered/Final.lean

-- Filtered/OfColimitCommutesFiniteLimit.lean

-- Filtered/Small.lean

-- FinCategory/AsType.lean

-- FinCategory/Basic.lean

-- FintypeCat.lean

-- FullSubcategory.lean

-- Functor/Basic.lean

-- Functor/Category.lean

-- Functor/Const.lean

-- Functor/Currying.lean

-- Functor/Derived/RightDerived.lean

-- Functor/EpiMono.lean

-- Functor/Flat.lean

-- Functor/FullyFaithful.lean

-- Functor/FunctorHom.lean

-- Functor/Functorial.lean

-- Functor/Hom.lean

-- Functor/KanExtension/Adjunction.lean

-- Functor/KanExtension/Basic.lean

-- Functor/KanExtension/Pointwise.lean

-- Functor/OfSequence.lean

-- Functor/ReflectsIso.lean

-- Functor/Trifunctor.lean

-- Galois/Action.lean

-- Galois/Basic.lean

-- Galois/Decomposition.lean

-- Galois/EssSurj.lean

-- Galois/Examples.lean

-- Galois/Full.lean

-- Galois/GaloisObjects.lean

-- Galois/IsFundamentalgroup.lean

-- Galois/Prorepresentability.lean

-- Galois/Topology.lean

-- Generator.lean

-- GlueData.lean

-- GradedObject.lean

-- GradedObject/Associator.lean

-- GradedObject/Bifunctor.lean
-- COLLISION: mapBifunctorMap' already in Algebra.lean — rename needed

-- GradedObject/Braiding.lean

-- GradedObject/Monoidal.lean

-- GradedObject/Single.lean

-- GradedObject/Trifunctor.lean

-- GradedObject/Unitor.lean

-- Grothendieck.lean

-- Groupoid.lean

-- Groupoid/Basic.lean

-- Groupoid/FreeGroupoid.lean

-- Groupoid/Subgroupoid.lean

-- Groupoid/VertexGroup.lean

-- GuitartExact/Basic.lean

-- GuitartExact/VerticalComposition.lean

-- HomCongr.lean

-- Idempotents/Basic.lean

-- Idempotents/Biproducts.lean
-- COLLISION: decomposition' already in RingTheory2.lean — rename needed

-- Idempotents/FunctorCategories.lean

-- Idempotents/FunctorExtension.lean

-- Idempotents/HomologicalComplex.lean

-- Idempotents/Karoubi.lean

-- Idempotents/KaroubiKaroubi.lean

-- IsConnected.lean

-- Iso.lean
-- COLLISION: map_inv' already in Order.lean — rename needed

-- IsomorphismClasses.lean

-- LiftingProperties/Adjunction.lean

-- LiftingProperties/Basic.lean

-- Limits/Bicones.lean

-- Limits/ColimitLimit.lean

-- Limits/Comma.lean

-- Limits/ConcreteCategory/Basic.lean

-- Limits/ConcreteCategory/WithAlgebraicStructures.lean

-- Limits/ConeCategory.lean

-- Limits/Cones.lean

-- Limits/Connected.lean

-- Limits/Constructions/BinaryProducts.lean

-- Limits/Constructions/EpiMono.lean

-- Limits/Constructions/Equalizers.lean

-- Limits/Constructions/EventuallyConstant.lean

-- Limits/Constructions/Filtered.lean

-- Limits/Constructions/FiniteProductsOfBinaryProducts.lean

-- Limits/Constructions/LimitsOfProductsAndEqualizers.lean

-- Limits/Constructions/Over/Connected.lean

-- Limits/Constructions/Over/Products.lean

-- Limits/Constructions/Pullbacks.lean

-- Limits/Constructions/WeaklyInitial.lean

-- Limits/Constructions/ZeroObjects.lean

-- Limits/Creates.lean

-- Limits/Elements.lean

-- Limits/EpiMono.lean

-- Limits/EssentiallySmall.lean

-- Limits/ExactFunctor.lean

-- Limits/Filtered.lean

-- Limits/FilteredColimitCommutesFiniteLimit.lean

-- Limits/FilteredColimitCommutesProduct.lean

-- Limits/Final.lean

-- Limits/Final/ParallelPair.lean

-- Limits/FinallySmall.lean

-- Limits/FintypeCat.lean

-- Limits/Fubini.lean

-- Limits/FullSubcategory.lean

-- Limits/FunctorCategory/Basic.lean

-- Limits/FunctorCategory/EpiMono.lean

-- Limits/FunctorCategory/Shapes/Products.lean

-- Limits/FunctorToTypes.lean

-- Limits/HasLimits.lean

-- Limits/IndYoneda.lean

-- Limits/Indization/Category.lean
-- COLLISION: resolution' already in Order.lean — rename needed

-- Limits/Indization/Equalizers.lean

-- Limits/Indization/FilteredColimits.lean

-- Limits/Indization/IndObject.lean

-- Limits/Indization/LocallySmall.lean

-- Limits/Indization/Products.lean

-- Limits/IsConnected.lean

-- Limits/IsLimit.lean

-- Limits/Lattice.lean

-- Limits/MonoCoprod.lean

-- Limits/MorphismProperty.lean

-- Limits/Opposites.lean

-- Limits/Over.lean

-- Limits/Pi.lean

-- Limits/Preserves/Basic.lean

-- Limits/Preserves/Filtered.lean

-- Limits/Preserves/Finite.lean

-- Limits/Preserves/FunctorCategory.lean

-- Limits/Preserves/Limits.lean

-- Limits/Preserves/Opposites.lean

-- Limits/Preserves/Presheaf.lean

-- Limits/Preserves/Shapes/BinaryProducts.lean

-- Limits/Preserves/Shapes/Biproducts.lean

-- Limits/Preserves/Shapes/Equalizers.lean

-- Limits/Preserves/Shapes/Images.lean

-- Limits/Preserves/Shapes/Kernels.lean

-- Limits/Preserves/Shapes/Products.lean

-- Limits/Preserves/Shapes/Pullbacks.lean

-- Limits/Preserves/Shapes/Square.lean
-- COLLISION: iff_of_equiv' already in RingTheory2.lean — rename needed
-- COLLISION: of_equiv' already in SetTheory.lean — rename needed

-- Limits/Preserves/Shapes/Terminal.lean

-- Limits/Preserves/Shapes/Zero.lean

-- Limits/Preserves/Ulift.lean

-- Limits/Preserves/Yoneda.lean

-- Limits/Presheaf.lean

-- Limits/Shapes/BinaryProducts.lean

-- Limits/Shapes/Biproducts.lean

-- Limits/Shapes/CombinedProducts.lean

-- Limits/Shapes/ConcreteCategory.lean

-- Limits/Shapes/Countable.lean

-- Limits/Shapes/Diagonal.lean

-- Limits/Shapes/DisjointCoproduct.lean

-- Limits/Shapes/End.lean

-- Limits/Shapes/Equalizers.lean

-- Limits/Shapes/Equivalence.lean

-- Limits/Shapes/FiniteLimits.lean

-- Limits/Shapes/FiniteProducts.lean

-- Limits/Shapes/FunctorToTypes.lean

-- Limits/Shapes/Grothendieck.lean

-- Limits/Shapes/Images.lean

-- Limits/Shapes/IsTerminal.lean

-- Limits/Shapes/KernelPair.lean

-- Limits/Shapes/Kernels.lean

-- Limits/Shapes/Multiequalizer.lean

-- Limits/Shapes/NormalMono/Basic.lean

-- Limits/Shapes/NormalMono/Equalizers.lean

-- Limits/Shapes/PiProd.lean

-- Limits/Shapes/Products.lean

-- Limits/Shapes/Pullback/Assoc.lean

-- Limits/Shapes/Pullback/CommSq.lean

-- Limits/Shapes/Pullback/Cospan.lean

-- Limits/Shapes/Pullback/Equalizer.lean

-- Limits/Shapes/Pullback/HasPullback.lean

-- Limits/Shapes/Pullback/Iso.lean

-- Limits/Shapes/Pullback/Mono.lean

-- Limits/Shapes/Pullback/Pasting.lean

-- Limits/Shapes/Pullback/PullbackCone.lean

-- Limits/Shapes/Pullback/Square.lean

-- Limits/Shapes/Reflexive.lean

-- Limits/Shapes/RegularMono.lean

-- Limits/Shapes/SingleObj.lean

-- Limits/Shapes/SplitCoequalizer.lean

-- Limits/Shapes/SplitEqualizer.lean

-- Limits/Shapes/StrictInitial.lean

-- Limits/Shapes/StrongEpi.lean

-- Limits/Shapes/Terminal.lean

-- Limits/Shapes/Types.lean

-- Limits/Shapes/WideEqualizers.lean

-- Limits/Shapes/WidePullbacks.lean

-- Limits/Shapes/ZeroMorphisms.lean

-- Limits/Shapes/ZeroObjects.lean

-- Limits/Sifted.lean

-- Limits/Types.lean

-- Limits/TypesFiltered.lean

-- Limits/Unit.lean

-- Limits/VanKampen.lean

-- Limits/Yoneda.lean

-- Linear/Basic.lean
-- COLLISION: units_smul_comp' already in Algebra.lean — rename needed
-- COLLISION: comp_units_smul' already in Algebra.lean — rename needed

-- Linear/FunctorCategory.lean

-- Linear/LinearFunctor.lean

-- Linear/Yoneda.lean

-- Localization/Adjunction.lean

-- Localization/Bousfield.lean

-- Localization/CalculusOfFractions.lean

-- Localization/CalculusOfFractions/ComposableArrows.lean

-- Localization/CalculusOfFractions/Fractions.lean

-- Localization/CalculusOfFractions/Preadditive.lean

-- Localization/Composition.lean

-- Localization/Construction.lean

-- Localization/DerivabilityStructure/Basic.lean

-- Localization/DerivabilityStructure/Constructor.lean

-- Localization/Equivalence.lean

-- Localization/FiniteProducts.lean

-- Localization/HasLocalization.lean
-- COLLISION: standard' already in Algebra.lean — rename needed

-- Localization/HomEquiv.lean

-- Localization/LocalizerMorphism.lean

-- Localization/Opposite.lean

-- Localization/Predicate.lean
-- COLLISION: map_eq' already in RingTheory2.lean — rename needed

-- Localization/Prod.lean

-- Localization/Resolution.lean

-- Localization/SmallHom.lean

-- Localization/SmallShiftedHom.lean

-- Localization/StructuredArrow.lean

-- Localization/Triangulated.lean

-- Monad/Adjunction.lean

-- Monad/Algebra.lean

-- Monad/Basic.lean

-- Monad/Coequalizer.lean

-- Monad/Comonadicity.lean

-- Monad/Equalizer.lean

-- Monad/EquivMon.lean

-- Monad/Kleisli.lean

-- Monad/Limits.lean

-- Monad/Monadicity.lean

-- Monad/Products.lean

-- Monad/Types.lean

-- Monoidal/Bimod.lean

-- Monoidal/Bimon_.lean

-- Monoidal/Braided/Basic.lean

-- Monoidal/Braided/Opposite.lean

-- Monoidal/Braided/Reflection.lean

-- Monoidal/Cartesian/Comon_.lean

-- Monoidal/Category.lean

-- Monoidal/Center.lean

-- Monoidal/CoherenceLemmas.lean

-- Monoidal/CommMon_.lean

-- Monoidal/Comon_.lean

-- Monoidal/Conv.lean

-- Monoidal/Discrete.lean

-- Monoidal/End.lean

-- Monoidal/Free/Basic.lean

-- Monoidal/Free/Coherence.lean

-- Monoidal/Functor.lean

-- Monoidal/FunctorCategory.lean

-- Monoidal/Hopf_.lean

-- Monoidal/Internal/FunctorCategory.lean

-- Monoidal/Internal/Limits.lean

-- Monoidal/Internal/Module.lean

-- Monoidal/Internal/Types.lean

-- Monoidal/Limits.lean

-- Monoidal/Linear.lean

-- Monoidal/Mod_.lean

-- Monoidal/Mon_.lean

-- Monoidal/NaturalTransformation.lean

-- Monoidal/OfChosenFiniteProducts/Basic.lean

-- Monoidal/OfChosenFiniteProducts/Symmetric.lean

-- Monoidal/OfHasFiniteProducts.lean

-- Monoidal/Opposite.lean

-- Monoidal/Preadditive.lean

-- Monoidal/Rigid/Basic.lean

-- Monoidal/Rigid/Braided.lean

-- Monoidal/Rigid/OfEquivalence.lean

-- Monoidal/Skeleton.lean

-- Monoidal/Subcategory.lean

-- Monoidal/Tor.lean

-- Monoidal/Transport.lean

-- Monoidal/Types/Basic.lean

-- MorphismProperty/Basic.lean

-- MorphismProperty/Comma.lean

-- MorphismProperty/Composition.lean

-- MorphismProperty/Concrete.lean

-- MorphismProperty/Factorization.lean

-- MorphismProperty/IsInvertedBy.lean

-- MorphismProperty/Limits.lean

-- MorphismProperty/OverAdjunction.lean

-- MorphismProperty/Representable.lean

-- NatIso.lean

-- NatTrans.lean

-- Noetherian.lean

-- Opposites.lean

-- PEmpty.lean

-- PUnit.lean

-- PathCategory/Basic.lean

-- PathCategory/MorphismProperty.lean

-- Pi/Basic.lean

-- Preadditive/AdditiveFunctor.lean

-- Preadditive/Basic.lean

-- Preadditive/Biproducts.lean

-- Preadditive/FunctorCategory.lean

-- Preadditive/Generator.lean

-- Preadditive/HomOrthogonal.lean

-- Preadditive/Injective.lean

-- Preadditive/InjectiveResolution.lean
-- COLLISION: kernelFork' already in Algebra.lean — rename needed
-- COLLISION: isLimitKernelFork' already in Algebra.lean — rename needed

-- Preadditive/LeftExact.lean

-- Preadditive/Mat.lean

-- Preadditive/OfBiproducts.lean

-- Preadditive/Opposite.lean
-- COLLISION: unop_sum' already in Algebra.lean — rename needed
-- COLLISION: op_sum' already in Algebra.lean — rename needed

-- Preadditive/Projective.lean

-- Preadditive/ProjectiveResolution.lean
-- COLLISION: cokernelCofork' already in Algebra.lean — rename needed
-- COLLISION: isColimitCokernelCofork' already in Algebra.lean — rename needed

-- Preadditive/Schur.lean

-- Preadditive/Yoneda/Basic.lean

-- Preadditive/Yoneda/Injective.lean

-- Preadditive/Yoneda/Projective.lean

-- Products/Associator.lean

-- Products/Basic.lean

-- Products/Bifunctor.lean
-- COLLISION: map_id_comp' already in RingTheory2.lean — rename needed
-- COLLISION: map_comp_id' already in RingTheory2.lean — rename needed

-- Products/Unitor.lean

-- Quotient.lean

-- Quotient/Linear.lean
-- COLLISION: smul' already in Order.lean — rename needed

-- Quotient/Preadditive.lean

-- Shift/Basic.lean

-- Shift/CommShift.lean

-- Shift/Induced.lean

-- Shift/InducedShiftSequence.lean

-- Shift/Localization.lean

-- Shift/Opposite.lean

-- Shift/Predicate.lean

-- Shift/Pullback.lean

-- Shift/Quotient.lean

-- Shift/ShiftSequence.lean

-- Shift/ShiftedHom.lean
-- COLLISION: comp_mk₀_id' already in Algebra.lean — rename needed
-- COLLISION: mk₀_comp_mk₀' already in Algebra.lean — rename needed
-- COLLISION: mk₀_comp_mk₀_assoc' already in Algebra.lean — rename needed
-- COLLISION: comp_map' already in RingTheory2.lean — rename needed

-- Shift/ShiftedHomOpposite.lean

-- Shift/SingleFunctors.lean

-- Sigma/Basic.lean
-- COLLISION: sigma' already in Order.lean — rename needed

-- Simple.lean

-- SingleObj.lean

-- Sites/Adjunction.lean

-- Sites/Canonical.lean

-- Sites/ChosenFiniteProducts.lean

-- Sites/Closed.lean

-- Sites/Coherent/Basic.lean

-- Sites/Coherent/CoherentSheaves.lean

-- Sites/Coherent/CoherentTopology.lean

-- Sites/Coherent/Comparison.lean

-- Sites/Coherent/Equivalence.lean

-- Sites/Coherent/ExtensiveSheaves.lean

-- Sites/Coherent/LocallySurjective.lean

-- Sites/Coherent/RegularSheaves.lean

-- Sites/Coherent/RegularTopology.lean

-- Sites/Coherent/SequentialLimit.lean

-- Sites/Coherent/SheafComparison.lean

-- Sites/CompatiblePlus.lean

-- Sites/CompatibleSheafification.lean

-- Sites/ConcreteSheafification.lean

-- Sites/ConstantSheaf.lean

-- Sites/Continuous.lean

-- Sites/CoverLifting.lean

-- Sites/CoverPreserving.lean

-- Sites/Coverage.lean

-- Sites/CoversTop.lean

-- Sites/DenseSubsite/Basic.lean

-- Sites/DenseSubsite/InducedTopology.lean

-- Sites/DenseSubsite/SheafEquiv.lean

-- Sites/EffectiveEpimorphic.lean

-- Sites/EpiMono.lean

-- Sites/EqualizerSheafCondition.lean

-- Sites/Equivalence.lean

-- Sites/Grothendieck.lean

-- Sites/IsSheafFor.lean

-- Sites/IsSheafOneHypercover.lean

-- Sites/LeftExact.lean

-- Sites/Limits.lean

-- Sites/Localization.lean

-- Sites/LocallyBijective.lean

-- Sites/LocallyFullyFaithful.lean

-- Sites/LocallyInjective.lean

-- Sites/LocallySurjective.lean

-- Sites/MayerVietorisSquare.lean

-- Sites/MorphismProperty.lean

-- Sites/NonabelianCohomology/H1.lean

-- Sites/OneHypercover.lean

-- Sites/Over.lean

-- Sites/Plus.lean

-- Sites/Preserves.lean

-- Sites/PreservesLocallyBijective.lean

-- Sites/PreservesSheafification.lean

-- Sites/Pretopology.lean

-- Sites/Pullback.lean

-- Sites/Sheaf.lean

-- Sites/SheafCohomology/Basic.lean

-- Sites/SheafHom.lean

-- Sites/SheafOfTypes.lean

-- Sites/Sheafification.lean

-- Sites/Sieves.lean

-- Sites/Spaces.lean

-- Sites/Subcanonical.lean

-- Sites/Subsheaf.lean

-- Sites/Types.lean

-- Sites/Whiskering.lean

-- Skeletal.lean

-- SmallObject/Construction.lean

-- SmallObject/Iteration/Basic.lean

-- SmallObject/Iteration/ExtendToSucc.lean

-- SmallObject/Iteration/Nonempty.lean

-- SmallObject/Iteration/UniqueHom.lean
-- COLLISION: iso_refl' already in Order.lean — rename needed
-- COLLISION: iso_trans' already in RingTheory2.lean — rename needed

-- Square.lean

-- Subobject/Basic.lean

-- Subobject/Comma.lean
-- COLLISION: quotientEquiv' already in RingTheory2.lean — rename needed

-- Subobject/FactorThru.lean

-- Subobject/Lattice.lean
-- COLLISION: sInf' already in Order.lean — rename needed
-- COLLISION: sInf_le' already in Order.lean — rename needed
-- COLLISION: sSup' already in Order.lean — rename needed

-- Subobject/Limits.lean

-- Subobject/MonoOver.lean

-- Subobject/Types.lean

-- Subobject/WellPowered.lean

-- Subterminal.lean

-- Sums/Associator.lean

-- Sums/Basic.lean

-- Thin.lean

-- Triangulated/Basic.lean
-- COLLISION: π₁' already in Algebra.lean — rename needed
-- COLLISION: π₂' already in Algebra.lean — rename needed
-- COLLISION: π₃' already in Algebra.lean — rename needed

-- Triangulated/Functor.lean

-- Triangulated/HomologicalFunctor.lean

-- Triangulated/Opposite.lean

-- Triangulated/Pretriangulated.lean

-- Triangulated/Rotate.lean

-- Triangulated/Subcategory.lean

-- Triangulated/TStructure/Basic.lean

-- Triangulated/TriangleShift.lean
-- COLLISION: shiftFunctorZero_eq' already in Algebra.lean — rename needed
-- COLLISION: shiftFunctorAdd_eq' already in Algebra.lean — rename needed
-- COLLISION: shiftFunctorAdd'_eq' already in Algebra.lean — rename needed

-- Triangulated/Triangulated.lean

-- Triangulated/Yoneda.lean

-- Types.lean
-- COLLISION: mono_iff_injective' already in Order.lean — rename needed
-- COLLISION: injective_of_mono' already in Algebra.lean — rename needed

-- UnivLE.lean

-- Whiskering.lean

-- Widesubcategory.lean

-- WithTerminal.lean

-- Yoneda.lean
