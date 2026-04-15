/-
Extracted from Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The continuous functional calculus

This file defines a generic API for the *continuous functional calculus* which is suitable in a wide
range of settings.

A continuous functional calculus for an element `a : A` in a topological `R`-algebra is a continuous
extension of the polynomial functional calculus (i.e., `Polynomial.aeval`) to continuous `R`-valued
functions on `spectrum R a`. More precisely, it is a continuous star algebra homomorphism
`C(spectrum R a, R) →⋆ₐ[R] A` that sends `(ContinuousMap.id R).restrict (spectrum R a)` to
`a`. In all cases of interest (e.g., when `spectrum R a` is compact and `R` is `ℝ≥0`, `ℝ`, or `ℂ`),
this is sufficient to uniquely determine the continuous functional calculus which is encoded in the
`ContinuousMap.UniqueHom` class.

Although these properties suffice to uniquely determine the continuous functional calculus, we
choose to bundle more information into the class itself. Namely, we include that the star algebra
homomorphism is a closed embedding, and also that the spectrum of the image of
`f : C(spectrum R a, R)` under this morphism is the range of `f`. In addition, the class specifies
a collection of continuous functional calculi for elements satisfying a given predicate
`p : A → Prop`, and we require that this predicate is preserved by the functional calculus.

Although `cfcHom : p a → C(spectrum R a, R) →*ₐ[R] A` is a necessity for getting the full power
out of the continuous functional calculus, this declaration will generally not be accessed directly
by the user. One reason for this is that `cfcHom` requires a proof of `p a` (indeed, if the
spectrum is empty, there cannot exist a star algebra homomorphism like this). Instead, we provide
the completely unbundled `cfc : (R → R) → A → A` which operates on bare functions and provides junk
values when either `a` does not satisfy the property `p`, or else when the function which is the
argument to `cfc` is not continuous on the spectrum of `a`.

This completely unbundled approach may give up some conveniences, but it allows for tremendous
freedom. In particular, `cfc f a` makes sense for *any* `a : A` and `f : R → R`. This is quite
useful in a variety of settings, but perhaps the most important is the following.
Besides being a star algebra homomorphism sending the identity to `a`, the key property enjoyed
by the continuous functional calculus is the *composition property*, which guarantees that
`cfc (g ∘ f) a = cfc g (cfc f a)` under suitable hypotheses on `a`, `f` and `g`. Note that this
theorem is nearly impossible to state nicely in terms of `cfcHom` (see `cfcHom_comp`). An
additional advantage of the unbundled approach is that expressions like `fun x : R ↦ x⁻¹` are valid
arguments to `cfc`, and a bundled continuous counterpart can only make sense when the spectrum of
`a` does not contain zero and when we have an `⁻¹` operation on the domain.

A reader familiar with C⋆-algebra theory may be somewhat surprised at the level of abstraction here.
For instance, why not require `A` to be an actual C⋆-algebra? Why define separate continuous
functional calculi for `R := ℂ`, `ℝ` or `ℝ≥0` instead of simply using the continuous functional
calculus for normal elements? The reason for both can be explained with a simple example,
`A := Matrix n n ℝ`. In Mathlib, matrices are not equipped with a norm (nor even a metric), and so
requiring `A` to be a C⋆-algebra is far too stringent. Likewise, `A` is not a `ℂ`-algebra, and so
it is impossible to consider the `ℂ`-spectrum of `a : Matrix n n ℝ`.

There is another, more practical reason to define separate continuous functional calculi for
different scalar rings. It gives us the ability to use functions defined on these types, and the
algebra of functions on them. For example, for `R := ℝ` it is quite natural to consider the
functions `(·⁺ : ℝ → ℝ)` and `(·⁻ : ℝ → ℝ)` because the functions `ℝ → ℝ` form a lattice ordered
group. If `a : A` is selfadjoint, and we define `a⁺ := cfc (·⁺ : ℝ → ℝ) a`, and likewise for `a⁻`,
then the properties `a⁺ * a⁻ = 0 = a⁻ * a⁺` and `a = a⁺ - a⁻` are trivial consequences of the
corresponding facts for functions. In contrast, if we had to do this using functions on `ℂ`, the
proofs of these facts would be much more cumbersome.

## Example

The canonical example of the continuous functional calculus is when `A := Matrix n n ℂ`, `R := ℂ`
and `p := IsStarNormal`. In this case, `spectrum ℂ a` consists of the eigenvalues of the normal
matrix `a : Matrix n n ℂ`, and, because this set is discrete, any function is continuous on the
spectrum. The continuous functional calculus allows us to make sense of expressions like `log a`
(`:= cfc log a`), and when `0 ∉ spectrum ℂ a`, we get the nice property `exp (log a) = a`, which
arises from the composition property `cfc exp (cfc log a) = cfc (exp ∘ log) a = cfc id a = a`, since
`exp ∘ log = id` *on the spectrum of `a`*. Of course, there are other ways to make sense of `exp`
and `log` for matrices (power series), and these agree with the continuous functional calculus.
In fact, given `f : C(spectrum ℂ a, ℂ)`, `cfc f a` amounts to diagonalizing `a` (possible since `a`
is normal), and applying `f` to the resulting diagonal entries. That is, if `a = u * d * star u`
with `u` a unitary matrix and `d` diagonal, then `cfc f a = u * d.map f * star u`.

In addition, if `a : Matrix n n ℂ` is positive semidefinite, then the `ℂ`-spectrum of `a` is
contained in (the range of the coercion of) `ℝ≥0`. In this case, we get a continuous functional
calculus with `R := ℝ≥0`. From this we can define `√a := cfc a NNReal.sqrt`, which is also
positive semidefinite (because `cfc` preserves the predicate), and this is truly a square root since
```
√a * √a = cfc NNReal.sqrt a * cfc NNReal.sqrt a =
  cfc (NNReal.sqrt ^ 2) a = cfc id a = a
```
The composition property allows us to show that, in fact, this is the *unique* positive semidefinite
square root of `a` because, if `b` is any positive semidefinite square root, then
```
b = cfc id b = cfc (NNReal.sqrt ∘ (· ^ 2)) b =
  cfc NNReal.sqrt (cfc b (· ^ 2)) = cfc NNReal.sqrt a = √a
```

## Main declarations

+ `ContinuousFunctionalCalculus R A (p : A → Prop)`: a class stating that every `a : A` satisfying
  `p a` has a star algebra homomorphism from the continuous `R`-valued functions on the
  `R`-spectrum of `a` into the algebra `A`. This map is a closed embedding, and satisfies the
  **spectral mapping theorem**.
+ `cfcHom : p a → C(spectrum R a, R) →⋆ₐ[R] A`: the underlying star algebra homomorphism for an
  element satisfying property `p`.
+ `cfc : (R → R) → A → A`: an unbundled version of `cfcHom` which takes the junk value `0` when
  `cfcHom` is not defined.
+ `cfcUnits`: builds a unit from `cfc f a` when `f` is nonzero and continuous on the
  spectrum of `a`.

## Main theorems

+ `cfc_comp : cfc (x ↦ g (f x)) a = cfc g (cfc f a)`
+ `cfc_polynomial`: the continuous functional calculus extends the polynomial functional calculus.

## Implementation details

Instead of defining a class depending on a term `a : A`, we register it for an `outParam` predicate
`p : A → Prop`, and then any element of `A` satisfying this predicate has the associated star
algebra homomorphism with the specified properties. In so doing we avoid a common pitfall:
dependence of the class on a term. This avoids annoying situations where `a b : A` are
propositionally equal, but not definitionally so, and hence Lean would not be able to automatically
identify the continuous functional calculi associated to these elements. In order to guarantee
the necessary properties, we require that the continuous functional calculus preserves this
predicate. That is, `p a → p (cfc f a)` for any function `f` continuous on the spectrum of `a`.

As stated above, the unbundled approach to `cfc` has its advantages. For instance, given an
expression `cfc f a`, the user is free to rewrite either `a` or `f` as desired with no possibility
of the expression ceasing to be defined. However, this unbundling also has some potential downsides.
In particular, by unbundling, proof requirements are deferred until the user calls the lemmas, most
of which have hypotheses both of `p a` and of `ContinuousOn f (spectrum R a)`.

In order to minimize burden to the user, we provide `autoParams` in terms of two tactics. Goals
related to continuity are dispatched by (a small wrapper around) `fun_prop`. As for goals involving
the predicate `p`, it should be noted that these will only ever be of the form `IsStarNormal a`,
`IsSelfAdjoint a` or `0 ≤ a`. For the moment we provide a rudimentary tactic to deal with these
goals, but it can be modified to become more sophisticated as the need arises.
-/

open scoped Ring

open Topology ContinuousMap

section Basic

class ContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [TopologicalSpace A] [Algebra R A] : Prop where
  predicate_zero : p 0
  [compactSpace_spectrum (a : A) : CompactSpace (spectrum R a)]
  spectrum_nonempty [Nontrivial A] (a : A) (ha : p a) : (spectrum R a).Nonempty
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(spectrum R a, R) →⋆ₐ[R] A,
    Continuous φ ∧ Function.Injective φ ∧ φ ((ContinuousMap.id R).restrict <| spectrum R a) = a ∧
      (∀ f, spectrum R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

scoped[ContinuousFunctionalCalculus]

attribute [instance] ContinuousFunctionalCalculus.compactSpace_spectrum

class ContinuousMap.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s]
    (φ ψ : C(s, R) →⋆ₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict s <| .id R) = ψ (.restrict s <| .id R)) :
    φ = ψ

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]

variable [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]

variable [Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p]

include instCFC in

lemma ContinuousFunctionalCalculus.isCompact_spectrum (a : A) :
    IsCompact (spectrum R a) :=
  isCompact_iff_compactSpace.mpr inferInstance

lemma StarAlgHom.ext_continuousMap [UniqueHom R A]
    (a : A) [CompactSpace (spectrum R a)] (φ ψ : C(spectrum R a, R) →⋆ₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.restrict (spectrum R a) <| .id R) = ψ (.restrict (spectrum R a) <| .id R)) :
    φ = ψ :=
  UniqueHom.eq_of_continuous_of_map_id (spectrum R a) φ ψ hφ hψ h

section cfcHom

variable {a : A} (ha : p a)

noncomputable def cfcHom : C(spectrum R a, R) →⋆ₐ[R] A :=
  (ContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose
