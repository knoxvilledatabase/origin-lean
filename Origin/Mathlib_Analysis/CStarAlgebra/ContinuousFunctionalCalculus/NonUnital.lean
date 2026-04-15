/-
Extracted from Analysis/CStarAlgebra/ContinuousFunctionalCalculus/NonUnital.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The continuous functional calculus for non-unital algebras

This file defines a generic API for the *continuous functional calculus* in *non-unital* algebras
which is suitable in a wide range of settings. The design is intended to match as closely as
possible that for unital algebras in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean`.  Changes to either file
should be mirrored in its counterpart whenever possible. The underlying reasons for the design
decisions in the unital case apply equally in the non-unital case. See the module documentation in
that file for more information.

A continuous functional calculus for an element `a : A` in a non-unital topological `R`-algebra is
a continuous extension of the polynomial functional calculus (i.e., `Polynomial.aeval`) for
polynomials with no constant term to continuous `R`-valued functions on `quasispectrum R a` which
vanish at zero. More precisely, it is a continuous star algebra homomorphism
`C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A` that sends `(ContinuousMap.id R).restrict (quasispectrum R a)`
to `a`. In all cases of interest (e.g., when `quasispectrum R a` is compact and `R` is `ℝ≥0`, `ℝ`,
or `ℂ`), this is sufficient to uniquely determine the continuous functional calculus which is
encoded in the `ContinuousMapZero.UniqueHom` class.

## Main declarations

+ `NonUnitalContinuousFunctionalCalculus R A (p : A → Prop)`: a class stating that every `a : A`
  satisfying `p a` has a non-unital star algebra homomorphism from the continuous `R`-valued
  functions on the `R`-quasispectrum of `a` vanishing at zero into the algebra `A`. This map is a
  closed embedding, and satisfies the **spectral mapping theorem**.
+ `cfcₙHom : p a → C(quasispectrum R a, R)₀ →⋆ₐ[R] A`: the underlying non-unital star algebra
  homomorphism for an element satisfying property `p`.
+ `cfcₙ : (R → R) → A → A`: an unbundled version of `cfcₙHom` which takes the junk value `0` when
  `cfcₙHom` is not defined.

## Main theorems

+ `cfcₙ_comp : cfcₙ (x ↦ g (f x)) a = cfcₙ g (cfcₙ f a)`

-/

local notation "σₙ" => quasispectrum

open Topology ContinuousMapZero

class NonUnitalContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  predicate_zero : p 0
  [compactSpace_quasispectrum : ∀ a : A, CompactSpace (σₙ R a)]
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A,
    Continuous φ ∧ Function.Injective φ ∧ φ ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a ∧
      (∀ f, σₙ R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

scoped[NonUnitalContinuousFunctionalCalculus]

attribute [instance] NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum

class ContinuousMapZero.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s] [Fact (0 ∈ s)]
    (φ ψ : C(s, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.id s) = ψ (.id s)) :
    φ = ψ

-- INSTANCE (free from Core): {R

section Main

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]

variable [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]

variable [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

variable [instCFCₙ : NonUnitalContinuousFunctionalCalculus R A p]

include instCFCₙ in

lemma NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (a : A) :
    IsCompact (σₙ R a) :=
  isCompact_iff_compactSpace.mpr inferInstance

lemma NonUnitalStarAlgHom.ext_continuousMap [UniqueHom R A]
    (a : A) [CompactSpace (σₙ R a)] (φ ψ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : φ (.id (σₙ R a)) = ψ (.id (σₙ R a))) :
    φ = ψ :=
  UniqueHom.eq_of_continuous_of_map_id _ φ ψ hφ hψ h

section cfcₙHom

variable {a : A} (ha : p a)

noncomputable def cfcₙHom : C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose
