/-
Extracted from Geometry/Manifold/VectorBundle/LocalFrame.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Local frames in a vector bundle

Let `V → M` be a finite rank smooth vector bundle with standard fiber `F`.
A family of sections `s i` of `V → M` is called a **C^k local frame** on a set `U ⊆ M` iff each
section `s i` is `C^k` on `U`, and the section values `s i x` form a basis for each `x ∈ U`.
We define a predicate `IsLocalFrame` for a collection of sections to be a local frame on a set,
and define basic notions (such as the coefficients of a section w.r.t. a local frame, and
checking the smoothness of `t` via its coefficients in a local frame).

Given a basis `b` for `F` and a local trivialisation `e` for `V`, we construct a
**smooth local frame** on `V` w.r.t. `e` and `b`, i.e. a collection of sections `sᵢ` of `V`
which is smooth on `e.baseSet` such that `{sᵢ x}` is a basis of `V x` for each `x ∈ e.baseSet`.
Any section `s` of `e` can be uniquely written as `s = ∑ i, f^i sᵢ` near `x`,
and `s` is smooth at `x` iff the functions `f^i` are.

In this file, we prove the latter statement for finite-rank bundles (with coefficients in a
complete field). In the planned file `Mathlib/Geometry/Manifold/VectorBundle/OrthonormalFrame.lean`
(#26221), we will prove the same for real vector bundles of any rank which admit a `C^n` bundle
metric. This includes bundles of finite rank, modelled on a Hilbert space or on a Banach space which
has smooth partitions of unity.

We will use this to construct local extensions of a vector to a section which is smooth on the
trivialisation domain.

## Main definitions and results

* `IsLocalFrameOn`: a family of sections `s i` of `V → M` is called a **C^k local frame** on a set
  `U ⊆ M` iff each section `s i` is `C^k` on `U`, and the section values `s i x` form a basis for
  each `x ∈ U`

Suppose `{sᵢ}` is a local frame on `U`, and `hs : IsLocalFrameOn s U`.
* `IsLocalFrameOn.toBasisAt hs`: for each `x ∈ U`, the vectors `sᵢ x` form a basis of `F`
* `IsLocalFrameOn.coeff hs` describes the coefficient of sections of `V` w.r.t. `{sᵢ}`.
  `hs.coeff i` is a family of fiberwise linear maps `Π x, V x →ₗ[𝕜] 𝕜`.
  The coefficient function of a section `t` is `(LinearMap.piApply (hs.coeff i)) t`.
* `IsLocalFrameOn.eventually_eq_sum_coeff_smul hs`: for a local frame `{sᵢ}` near `x`,
  for each section `t` we have `t = ∑ i, (LinearMap.piApply (hs.coeff i) t) • sᵢ` near `x`.
* `IsLocalFrameOn.coeff_sum_eq hs t hx` proves that
  `t x = ∑ i, hs.coeff i x (t x) • sᵢ x`, provided that `hx : x ∈ U`.
* `IsLocalFrameOn.coeff_congr hs`: the coefficient `hs.coeff i` of `t` in the local frame `{sᵢ}`
  only depends on `t` at `x`.
* `IsLocalFrameOn.eq_iff_coeff hs`: two sections `t` and `t'` are equal at `x` if and only if their
  coefficients at `x` w.r.t. `{sᵢ}` agree.
* `IsLocalFrameOn.contMDiffOn_of_coeff hs`: a section `t` is `C^k` on `U` if each coefficient
  `(LinearMap.piApply (hs.coeff i) t)` is `C^k` on `U`
* `IsLocalFrameOn.contMDiffAt_of_coeff hs`: a section `t` is `C^k` at `x ∈ U`
  if all of its frame coefficients are
* `IsLocalFrameOn.contMDiffOn_off_coeff hs`: a section `t` is `C^k` on an open set `t ⊆ U`
  ff all of its frame coefficients are
* `MDifferentiable` versions of the previous three statements

In the following lemmas, let `e` be a compatible local trivialisation of `V`, and `b` a basis of
the model fiber `F`.
* `Bundle.Trivialization.basisAt e b`: for each `x ∈ e.baseSet`,
  return the basis of `V x` induced by `e` and `b`
* `e.localFrame b`: the local frame on `V` induced by `e` and `b`.
  Use `e.localFrame b i` to access the i-th section in that frame.
* `e.contMDiffOn_localFrame_baseSet`: each section `e.localFrame b i` is smooth on `e.baseSet`
* `e.localFrame_coeff b i` describes the `i`-th coefficient of sections of `V` w.r.t.
  `e.localFrame b`: it is a family of fiberwise linear maps `Π x, V x →ₗ[𝕜] 𝕜`, and the coefficient
  function of a section `s` is `(LinearMap.piApply (e.localFrame_coeff b i)) s`.
* `e.eventually_eq_localFrame_sum_coeff_smul b`: near `x`, we have
  `s = ∑ i, (LinearMap.piApply (e.localFrame_coeff b i) s) • e.localFrame b i`
* `e.localFrame_coeff_congr b`: the coefficient `e.localFrame_coeff b i` of `s` in the local frame
  induced by `e` and `b` at `x` only depends on `s` at `x`.
* `e.contMDiffOn_localFrame_coeff`: if `s` is a `C^k` section, each coefficient
  `(LinearMap.piApply (e.localFrame_coeff b i) s)` is `C^k` on `e.baseSet`
* `e.contMDiffAt_iff_localFrame_coeff b`: a section `s` is `C^k` at `x ∈ e.baseSet`
  iff all of its frame coefficients are
* `e.contMDiffOn_iff_localFrame_coeff b`: a section `s` is `C^k` on an open set `t ⊆ e.baseSet`
  iff all of its frame coefficients are

## Note

This file proves smoothness criteria in terms of coefficients for local frames induced by a
trivialization. A fully frame-intrinsic converse for `IsLocalFrameOn` will be added later.

## Implementation notes

Local frames use the junk value pattern: they are defined on all of `M`, but their value is
only meaningful on the set on which they are a local frame.

## Tags
vector bundle, local frame, smoothness

-/

open Bundle Filter Function Topology Module

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

noncomputable section

section IsLocalFrame

variable {ι : Type*} {s s' : ι → (x : M) → V x} {u u' : Set M} {x : M} {n : WithTop ℕ∞}

variable (I F n) in

structure IsLocalFrameOn (s : ι → (x : M) → V x) (u : Set M) where
  linearIndependent {x : M} (hx : x ∈ u) : LinearIndependent 𝕜 (s · x)
  generating {x : M} (hx : x ∈ u) : ⊤ ≤ Submodule.span 𝕜 (Set.range (s · x))
  contMDiffOn (i : ι) : CMDiff[u] n (T% (s i))

namespace IsLocalFrameOn

lemma congr (hs : IsLocalFrameOn I F n s u) (hs' : ∀ i, ∀ x, x ∈ u → s i x = s' i x) :
    IsLocalFrameOn I F n s' u where
  linearIndependent := by
    intro x hx
    have := hs.linearIndependent hx
    simp_all
  generating := by
    intro x hx
    have := hs.generating hx
    simp_all
  contMDiffOn i := (hs.contMDiffOn i).congr (by simp +contextual [hs'])

lemma mono (hs : IsLocalFrameOn I F n s u) (hu'u : u' ⊆ u) : IsLocalFrameOn I F n s u' where
  linearIndependent := by
    intro x hx
    exact hs.linearIndependent (hu'u hx)
  generating := by
    intro x hx
    exact hs.generating (hu'u hx)
  contMDiffOn i := (hs.contMDiffOn i).mono hu'u

lemma contMDiffAt (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x ∈ u) (i : ι) :
    CMDiffAt n (T% (s i)) x :=
  (hs.contMDiffOn i).contMDiffAt <| hu.mem_nhds hx

def toBasisAt (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) : Basis ι 𝕜 (V x) :=
  Basis.mk (hs.linearIndependent hx) (hs.generating hx)
