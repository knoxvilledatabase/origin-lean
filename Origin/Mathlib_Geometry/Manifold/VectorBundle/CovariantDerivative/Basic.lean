/-
Extracted from Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covariant derivatives

This file defines covariant derivatives (aka Koszul connections) on vector bundles over manifolds.

There are versions of the story: a local unbundled one and a global bundled one.
The local version is used by the global version but also (in other files) when
seeing a global object in a local trivialization.

In the whole file `M` is a manifold over any nontrivially normed field `𝕜` and `V` is
a vector bundle over `M` with model fiber `F`.

## Main definitions and constructions

* `IsCovariantDerivativeOn`: A function from sections of a vector bundle `V` over a manifold `M` to
  sections of $Hom(TM, V)$ is a *covariant derivative* on a set `s` in `M` if it is additive and
  satisfies the Leibniz rule when applied to sections that are differentiable at a point of `s`.
* `ContMDiffCovariantDerivativeOn`: A covariant derivative ∇ on some set is called *of class* `C^k`
  iff, whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇_X σ` is a `C^k`
  section. This is a class so typeclass inference can deduce this automatically.
* `IsCovariantDerivativeOn.add_one_form`: Adding a one-form taking values in the endomorphisms of
  the vector bundle to a covariant derivative on a set gives a covariant derivative on that set.
* `IsCovariantDerivativeOn.difference`: The difference of two covariant derivatives on a set,
  as a one-form taking values in the endomorphism bundle.
* `CovariantDerivative`: a globally defined covariant derivative on a vector bundle, as a bundled
  object.
* `ContMDiffCovariantDerivative`: A covariant derivative ∇ is called *of class* `C^k`
  iff, whenever `X` is a `C^k` section and `σ` a `C^{k+1}` section, the result `∇_X σ` is a `C^k`
  section. This is a class so typeclass inference can deduce this automatically.
* `CovariantDerivative.addOneForm`: Adding a one-form taking values in the endomorphisms of the
  vector bundle to a covariant derivative gives a covariant derivative.
* `CovariantDerivative.difference`: The difference of two covariant derivatives, as a one-form
  taking values in the endomorphism bundle.

## Implementation notes

On paper there are several equivalent ways to define covariant derivatives on a vector bundle
`V → M`. The most common one starts with a function `∇` taking as input a global smooth vector field
`X` and a global smooth section `σ` and giving as output a global smooth section `∇_X σ`, before
proving the result that `(∇_X σ) x` at a point `x` only depends on the value of the vector field at
that point and the 1-jet of the section at that point.

Here we ask for a map sending a global section `σ` of `V` to a global section `∇ σ` of `Hom(TM, V)`.
So the fact that `(∇_X σ) x` depends only on `X x` is baked into the definition.
Note also that we don’t put any differentiability restriction on `σ` and `X`, the type of
the covariant derivative map is simply `(Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))`.
But the conditions on this map involve differentiability, see the definition of
`IsCovariantDerivativeOn`.

This file proves that `(∇_X σ) x` depends only on the germ of `σ` at `x`, but not the stronger
statement that it depends only the 1-jet of `σ` at `x`. This will be proved in a later file.
-/

open Bundle NormedSpace

open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ## Local unbundled theory -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

structure IsCovariantDerivativeOn
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (s : Set M := Set.univ) : Prop where
  add {σ σ' : Π x : M, V x} {x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hx : x ∈ s := by trivial) :
    cov (σ + σ') x = cov σ x + cov σ' x
  leibniz {σ : Π x : M, V x} {g : M → 𝕜} {x}
    (hσ : MDiffAt (T% σ) x) (hg : MDiffAt g x) (hx : x ∈ s := by trivial) :
    cov (g • σ) x = g x • cov σ x + (extDerivFun g x).smulRight (σ x)

class ContMDiffCovariantDerivativeOn [IsManifold I 1 M] [VectorBundle 𝕜 F V] (k : WithTop ℕ∞)
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (u : Set M) where
  contMDiff : ∀ {σ : Π x : M, V x}, CMDiff[u] (k + 1) (T% σ) →
    letI cov (x : M) : TotalSpace (E →L[𝕜] F) fun x ↦ TangentSpace I x →L[𝕜] V x := ⟨x, cov σ x⟩
    ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] F)) k cov u
    -- TODO elaborators are not working here. We want to use `T% (cov σ)` and CMDiff[u] k f

variable {F}

namespace IsCovariantDerivativeOn

/-! ### Changing set

In this section, we change `s` in `IsCovariantDerivativeOn F cov s`, proving the condition is
monotone and local.
-/

section changing_set

lemma mono
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s t : Set M}
    (hcov : IsCovariantDerivativeOn F cov t) (hst : s ⊆ t) : IsCovariantDerivativeOn F cov s where
  add hσ hσ' hx := hcov.add hσ hσ' (hst hx)
  leibniz hσ hcov' hx := hcov.leibniz hσ hcov' (hst hx)

lemma iUnion {ι : Type*} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : ι → Set M} (hcov : ∀ i, IsCovariantDerivativeOn F cov (s i)) :
    IsCovariantDerivativeOn F cov (⋃ i, s i) where
  add hσ hσ' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).add hσ hσ'
  leibniz hσ hf' hx := by
    obtain ⟨si, ⟨i, rfl⟩, hxsi⟩ := hx
    exact (hcov i).leibniz hσ hf'

end changing_set

lemma congr_of_eqOn
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hxs : s ∈ 𝓝 x) (hσσ' : ∀ x ∈ s, σ x = σ' x) :
    cov σ x = cov σ' x := by
  classical
  have hxs' : x ∈ s := mem_of_mem_nhds hxs
  let ψ (x' : M) : 𝕜 := if x' ∈ s then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hxs']
  -- Observe that `ψ • σ = ψ • σ'` as dependent functions.
  have H (x' : M) : ((ψ : M → 𝕜) • σ) x' = ((ψ : M → 𝕜) • σ') x' := by
    dsimp [ψ]
    split_ifs with hx's
    · simpa using hσσ' _ hx's
    · simp
  have hψ' : HasMFDerivAt I 𝓘(𝕜) ψ x 0 := by
    have : HasMFDerivAt I 𝓘(𝕜, 𝕜) (fun (_x : M) ↦ (1 : 𝕜)) x 0 := hasMFDerivAt_const ..
    refine this.congr_of_eventuallyEq ?_
    apply Filter.eventuallyEq_of_mem hxs
    intro t ht
    simp [ψ, ht]
  have := hcov.leibniz hσ hψ'.mdifferentiableAt
  -- Then, it's a chain of (dependent) equalities.
  calc cov σ x
    _ = cov ((ψ : M → 𝕜) • σ) x := by
      simp [hcov.leibniz hσ hψ'.mdifferentiableAt, hψx, extDerivFun, hψ'.mfderiv]
    _ = cov ((ψ : M → 𝕜) • σ') x := by rw [funext H]
    _ = cov σ' x := by
      simp [hcov.leibniz hσ' hψ'.mdifferentiableAt, hψx, extDerivFun, hψ'.mfderiv]

open Filter Set in

lemma congr_of_eventuallyEq
    {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ σ' : Π x : M, V x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hxs : s ∈ 𝓝 x) (hσσ' : ∀ᶠ x in 𝓝 x, σ x = σ' x) :
    cov σ x = cov σ' x := by
  rw [eventually_iff_exists_mem] at hσσ'
  choose s' hs' b using hσσ'
  exact (hcov.mono inter_subset_left).congr_of_eqOn hσ hσ' (inter_mem hxs hs') fun x hx ↦ b x hx.2

/-! ### Computational properties -/

section computational_properties

variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {s : Set M}

lemma zero [VectorBundle 𝕜 F V] (hcov : IsCovariantDerivativeOn F cov s)
    {x} (hx : x ∈ s := by trivial) :
    cov 0 x = 0 := by
  simpa using (hcov.add (mdifferentiableAt_zeroSection ..)
    (mdifferentiableAt_zeroSection ..) : cov (0 + 0) x = _)

theorem smul_const (hcov : IsCovariantDerivativeOn F cov s)
    {σ : Π x : M, V x} {x} (a : 𝕜)
    (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov (a • σ) x = a • cov σ x := by
  simpa [extDerivFun] using hcov.leibniz (g := fun _ ↦ a) hσ mdifferentiableAt_const

end computational_properties

/-! ### Operations

In this section we prove that:

* affine combinations of covariant derivatives are covariant derivatives
* adding a one-form taking values in the endomorphisms of the vector bundle to a covariant
  derivative gives a covariant derivative. See `IsCovariantDerivativeOn.add_one_form`.
* subtracting two covariant derivatives on some set gives a one-form taking values in
  the endomorphisms of the vector bundle. See `IsCovariantDerivativeOn.difference`.

Note: morally this means covariant derivatives form an affine space over the vector space of
one-forms taking values in the endomorphisms of the bundle, but we don’t package it that way yet.
-/

section operations

variable {s : Set M} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
